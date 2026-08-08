// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! TIER 5 — symbolic verification over *unbounded* integer domains, in pure Rust.
//!
//! Tier 4 ([`crate::for_all`]) enumerates: it proves a property by checking every value, so it can only
//! cover finite/bounded domains. Tier 5 proves properties over the **entire** domain — including all
//! 2^64 values of `u64`, over any number of variables — **without enumerating it**, by *interval
//! abstract interpretation*: it computes, for each sub-expression, an interval guaranteed to contain
//! every value that expression can take, then decides the property over those intervals.
//!
//! Because tier 5 must *reason about* an expression rather than merely call it, its predicates are a
//! small first-party [`Expr`]/[`Prop`] DSL (an opaque `Fn` can't be analysed — only executed). Variables
//! are addressed by index ([`Expr::var_at`]); [`Expr::var`] is variable 0.
//!
//! **Function contracts** — the workhorse of component/kernel verification — are [`prove_contract`]:
//! prove that a postcondition holds whenever a precondition does, over the variables' domains.
//!
//! **Soundness is the whole point** — the interval transfer functions always *over-approximate* (the
//! true set of values is a subset of the computed interval), and every uncertain case degrades to
//! [`SymVerdict::Unknown`] rather than guessing:
//!  - [`SymVerdict::Proven`] — the property holds for **every** assignment in the domain (a real proof).
//!  - [`SymVerdict::Refuted`] — carries a **concrete** assignment that falsifies it (confirmed).
//!  - [`SymVerdict::Unknown`] — the interval abstraction wasn't precise enough to decide (e.g. a
//!    relational/correlated property). Never a false Proven or Refuted.
//!
//! This is the role Kani/CBMC plays, done entirely first-party: no C, no external solver, no WSL —
//! `no_std`, only `alloc` for the expression tree and witnesses.

// The DSL's builder methods (add/sub/mul/shl/shr/rem/not) intentionally mirror operator names.
#![allow(clippy::should_implement_trait)]

use alloc::boxed::Box;
use alloc::vec::Vec;

/// An inclusive interval `[lo, hi]` over `u64`. Every operation **over-approximates**: the set of real
/// results is always a subset of the returned interval — which is exactly what makes a proof over the
/// interval sound. When an operation could wrap/overflow into an un-representable set, it widens to
/// [`Iv::full`] (always sound, just less precise).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Iv {
    pub lo: u64,
    pub hi: u64,
}

impl Iv {
    /// The interval containing exactly one value.
    pub const fn point(v: u64) -> Iv {
        Iv { lo: v, hi: v }
    }
    /// The interval `[lo, hi]` (swapped if given out of order).
    pub const fn new(lo: u64, hi: u64) -> Iv {
        if lo <= hi {
            Iv { lo, hi }
        } else {
            Iv { lo: hi, hi: lo }
        }
    }
    /// The whole `u64` domain, `[0, u64::MAX]`.
    pub const fn full() -> Iv {
        Iv {
            lo: 0,
            hi: u64::MAX,
        }
    }
    /// Whether `v` is inside the interval.
    pub const fn contains(&self, v: u64) -> bool {
        self.lo <= v && v <= self.hi
    }

    /// Whether this interval denotes the **empty set** — `lo > hi`, so no value is inside it.
    ///
    /// # Why an interval can be empty at all, when `new` swaps
    ///
    /// [`new`](Iv::new) normalises, but `lo` and `hi` are **public fields**, so `Iv { lo: 5, hi: 3 }`
    /// is ordinary Rust that any caller can write — most often by transposing the two arguments of a
    /// bound they computed. Nothing rejected it, and the arithmetic below assumed `lo <= hi`
    /// throughout:
    ///
    /// * [`refine`] computed the split width as `d.hi - d.lo`, which **underflow-panics under
    ///   `debug-assertions` and wraps to a near-`u64::MAX` width in a release build** — after which
    ///   `d.lo + (d.hi - d.lo) / 2` overflows in turn;
    /// * `Iv::shl` guards on `self.hi` and then shifts `self.lo`, so an inverted interval passes the
    ///   guard on the small end and **overflow-panics on the large one**;
    /// * `prove_forall_n` reported `Refuted { witness: [d.lo] }` for a domain containing no
    ///   assignments at all — a witness the caller's domain excludes.
    ///
    /// That is the same shape as the `Affine` overflow this crate already carries a note about: a
    /// proof engine whose answer depends on the optimisation level, on an input a caller is entitled
    /// to construct. The public entry points now refuse an empty box rather than reason over it —
    /// see [`prove_forall_n`].
    pub const fn is_empty(&self) -> bool {
        self.lo > self.hi
    }

    /// The canonical empty interval.
    pub const fn empty() -> Iv {
        Iv { lo: 1, hi: 0 }
    }

    fn add(self, o: Iv) -> Iv {
        match (self.lo.checked_add(o.lo), self.hi.checked_add(o.hi)) {
            (Some(lo), Some(hi)) => Iv { lo, hi },
            _ => Iv::full(), // a wrap makes the result set non-contiguous -> widen (sound)
        }
    }
    fn sub(self, o: Iv) -> Iv {
        match (self.lo.checked_sub(o.hi), self.hi.checked_sub(o.lo)) {
            (Some(lo), Some(hi)) => Iv { lo, hi },
            _ => Iv::full(),
        }
    }
    fn mul(self, o: Iv) -> Iv {
        match (self.lo.checked_mul(o.lo), self.hi.checked_mul(o.hi)) {
            (Some(lo), Some(hi)) => Iv { lo, hi },
            _ => Iv::full(),
        }
    }
    fn shl(self, k: u32) -> Iv {
        if k >= 64 {
            return if self.lo == 0 && self.hi == 0 {
                Iv::point(0)
            } else {
                Iv::full()
            };
        }
        if self.hi <= (u64::MAX >> k) {
            Iv {
                lo: self.lo << k,
                hi: self.hi << k,
            }
        } else {
            Iv::full()
        }
    }
    fn shr(self, k: u32) -> Iv {
        // The shift amount is MASKED, not saturated. [`Expr::eval_at`] evaluates `Shr` with
        // `u64::wrapping_shr`, which discards the high bits of `k` and shifts by `k % 64` — so
        // `x >> 64` is `x`, not zero.
        //
        // This line previously returned `Iv::point(0)` for `k >= 64`, which is an
        // UNDER-approximation: the interval [0, 0] does not contain the value the expression
        // actually takes. That is the one direction the abstraction may never go, and it made
        // `prove_forall_n(&[Iv::point(5)], &Prop::Eq(Expr::var().shr(64), Expr::c(0)))` return
        // `Proven` for a property that is false at the only point of its domain.
        let k = k % 64;
        Iv {
            lo: self.lo >> k,
            hi: self.hi >> k,
        } // monotone, never overflows
    }
    fn bitand(self, mask: u64) -> Iv {
        let hi = if mask < self.hi { mask } else { self.hi };
        Iv { lo: 0, hi }
    }
    /// Bitwise OR with a CONSTANT mask.
    ///
    /// # Why this delegates rather than keeping its own bound
    ///
    /// This used to return `Iv { lo: max(mask, self.lo), hi: u64::MAX }` — sound, but it discarded
    /// the upper bound entirely, even when the operand was tightly bounded. The two-variable
    /// [`Iv::bitor_iv`] already computed the correct bit-saturation bound, so the CONSTANT case —
    /// the more informative one, since one side is known exactly — was strictly LESS precise than
    /// the variable case on identical input:
    ///
    /// ```text
    ///   x in [0,1], x | 1  via bitor      -> [1, u64::MAX]     (no upper bound at all)
    ///   x in [0,1], x | 1  via bitor_iv   -> [1, 1]            (exact)
    /// ```
    ///
    /// The cost was real and measured, not hypothetical. `rustc` lowers `x | 1` to a constant-mask
    /// `Or`, so every lifted function containing an OR-with-literal hit the weak path: the contract
    /// `x <= 1 -> (x | 1) <= 1` came back `Unknown` from the lifted MIR while the identical goal
    /// written by hand with `OrE` came back `Proven`. A property that is provable when typed by a
    /// human and unprovable when read from the compiler is precisely the asymmetry the lifter exists
    /// to remove.
    ///
    /// # Soundness
    ///
    /// Unchanged in direction — this only ever NARROWS the returned interval, and it narrows to a
    /// bound already proven sound for the two-interval case. A constant `mask` is the point interval
    /// `[mask, mask]`, so delegating is exact, not an approximation of an approximation.
    fn bitor(self, mask: u64) -> Iv {
        self.bitor_iv(Iv::point(mask))
    }
    fn rem(self, m: u64) -> Iv {
        if m == 0 {
            return Iv::full();
        }
        if self.hi < m {
            self
        } else {
            Iv { lo: 0, hi: m - 1 }
        }
    }

    /// Bitwise AND of two intervals — the variable-by-variable case.
    ///
    /// # Why this is not `bitand`'s job
    ///
    /// [`Iv::bitand`] masks by a CONSTANT and is the only bitwise form the engine had, because
    /// [`Expr::And`] carries a `u64` rather than a second `Expr`. That was a real expressiveness
    /// wall, and it had a measured cost: `Cap::attenuate` computes `rights & keep` over two
    /// *variables*, so the one function whose defect this crate most wanted to catch could not be
    /// written down.
    ///
    /// # Soundness
    ///
    /// For unsigned values, `a & b <= a` and `a & b <= b` — clearing bits can only decrease the
    /// value. So `hi = min(a.hi, b.hi)` is a sound upper bound. The lower bound is `0`: whenever the
    /// two operands have no bits in common the result is `0`, and interval endpoints alone cannot
    /// rule that out. Widening downward is always legal; narrowing is what would be unsound.
    fn bitand_iv(self, o: Iv) -> Iv {
        Iv {
            lo: 0,
            hi: if self.hi < o.hi { self.hi } else { o.hi },
        }
    }

    /// Bitwise OR of two intervals — the variable-by-variable case.
    ///
    /// # Soundness
    ///
    /// `a | b >= a` and `a | b >= b` (setting bits can only increase the value), so
    /// `lo = max(a.lo, b.lo)` is sound. For the upper bound, `a | b <= a + b` would overflow, so this
    /// uses the standard bit-saturation bound: take `max(a.hi, b.hi)` and set every bit below its
    /// highest set bit. That value is `>= a | b` for any `a <= a.hi`, `b <= b.hi`, because `a | b`
    /// cannot have a set bit above the highest set bit of either operand's maximum, and every bit at
    /// or below that position is already set in the bound.
    fn bitor_iv(self, o: Iv) -> Iv {
        let lo = if self.lo > o.lo { self.lo } else { o.lo };
        let m = if self.hi > o.hi { self.hi } else { o.hi };
        // Saturate every bit below m's highest set bit. `m == 0` means both maxima are 0, and the
        // only possible result is 0.
        let hi = if m == 0 {
            0
        } else {
            // Smear the highest set bit downward: 0b0100.. -> 0b0111..
            let mut s = m;
            s |= s >> 1;
            s |= s >> 2;
            s |= s >> 4;
            s |= s >> 8;
            s |= s >> 16;
            s |= s >> 32;
            s
        };
        // The smeared bound is >= lo by construction (hi >= m >= max(a.hi,b.hi) >= max(a.lo,b.lo)),
        // but an inverted input interval could break that, so normalise rather than emit an empty
        // interval that would read as "no values".
        if lo > hi {
            Iv::full()
        } else {
            Iv { lo, hi }
        }
    }

    /// Bitwise XOR of two intervals.
    ///
    /// # Soundness
    ///
    /// XOR is neither monotone up nor down: `a ^ b` can be `0` (when `a == b`) and can be as large as
    /// the OR bound. So the lower bound is `0` and the upper bound is the same bit-saturation bound
    /// [`bitor_iv`](Iv::bitor_iv) uses — `a ^ b <= a | b` for all `a, b`, so the OR bound covers XOR.
    fn bitxor_iv(self, o: Iv) -> Iv {
        Iv {
            lo: 0,
            hi: self.bitor_iv(o).hi,
        }
    }

    /// Left shift by a variable amount.
    ///
    /// The shift amount is masked to `k % 64`, matching [`Expr::eval_at`]'s `wrapping_shl`. Any
    /// non-zero shift can lose bits off the top, so unless the shift amount is provably `0` this
    /// widens to the full domain — sound, and honest about how little an interval knows here.
    fn shl_iv(self, k: Iv) -> Iv {
        if k.lo == 0 && k.hi == 0 {
            return self;
        }
        Iv::full()
    }

    /// Right shift by a variable amount.
    ///
    /// Shifting right is monotone in the value and anti-monotone in the amount, and the amount is
    /// masked to `[0, 63]`. So the smallest result is `lo >> 63` (largest legal shift of the smallest
    /// value) and the largest is `hi >> (smallest possible shift)`.
    fn shr_iv(self, k: Iv) -> Iv {
        // When the amount's interval spans 64 or more values every masked amount 0..=63 is possible,
        // so the smallest shift that can occur is 0.
        let (kmin, kmax) = if k.hi.wrapping_sub(k.lo) >= 63 || k.hi >= 64 {
            (0u32, 63u32)
        } else {
            ((k.lo % 64) as u32, (k.hi % 64) as u32)
        };
        // Guard the ordering: if masking inverted the pair, fall back to the widest legal range.
        let (kmin, kmax) = if kmin <= kmax { (kmin, kmax) } else { (0, 63) };
        Iv {
            lo: self.lo >> kmax,
            hi: self.hi >> kmin,
        }
    }
}

/// An integer expression over one or more symbolic variables (addressed by index), evaluated in the
/// `u64` bitvector domain (wrapping arithmetic, like real Rust `u64`).
#[derive(Clone, Debug)]
pub enum Expr {
    /// A symbolic input variable, by index (0, 1, ...).
    Var(u32),
    /// A constant.
    Const(u64),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    /// Left shift by a constant.
    Shl(Box<Expr>, u32),
    /// Right shift by a constant.
    Shr(Box<Expr>, u32),
    /// Bitwise AND with a constant mask.
    And(Box<Expr>, u64),
    /// Bitwise OR with a constant mask.
    Or(Box<Expr>, u64),
    /// Remainder by a constant modulus.
    Rem(Box<Expr>, u64),

    // ── variable-by-variable bitwise and shift ────────────────────────────────────────────────────
    //
    // ADDED, NOT REPLACING: `And`/`Or`/`Shl`/`Shr` above carry a CONSTANT and every existing caller
    // and proof keeps working unchanged. These are the forms real code produces that the constant
    // versions could not express — `rights & keep` in `Cap::attenuate` being the motivating case,
    // where BOTH sides are function parameters. Without them the one function the tier-5 exercise
    // most wanted to check could not be written down at all, which is why `aion_caps`'
    // `tier5_symbolic_proofs.rs` records "THERE IS NO VARIABLE-BY-VARIABLE `AND`" as a stated
    // limitation rather than a property.
    /// Bitwise AND of two expressions.
    AndE(Box<Expr>, Box<Expr>),
    /// Bitwise OR of two expressions.
    OrE(Box<Expr>, Box<Expr>),
    /// Bitwise XOR of two expressions.
    XorE(Box<Expr>, Box<Expr>),
    /// Left shift by a variable amount (masked to `k % 64`, matching `wrapping_shl`).
    ShlE(Box<Expr>, Box<Expr>),
    /// Right shift by a variable amount (masked to `k % 64`, matching `wrapping_shr`).
    ShrE(Box<Expr>, Box<Expr>),
}

impl Expr {
    /// Variable 0 (the common single-variable case).
    pub fn var() -> Expr {
        Expr::Var(0)
    }
    /// Variable `i`.
    pub fn var_at(i: u32) -> Expr {
        Expr::Var(i)
    }
    pub fn c(v: u64) -> Expr {
        Expr::Const(v)
    }
    pub fn add(self, o: Expr) -> Expr {
        Expr::Add(Box::new(self), Box::new(o))
    }
    pub fn sub(self, o: Expr) -> Expr {
        Expr::Sub(Box::new(self), Box::new(o))
    }
    pub fn mul(self, o: Expr) -> Expr {
        Expr::Mul(Box::new(self), Box::new(o))
    }
    pub fn shl(self, k: u32) -> Expr {
        Expr::Shl(Box::new(self), k)
    }
    pub fn shr(self, k: u32) -> Expr {
        Expr::Shr(Box::new(self), k)
    }
    pub fn and(self, m: u64) -> Expr {
        Expr::And(Box::new(self), m)
    }
    pub fn or(self, m: u64) -> Expr {
        Expr::Or(Box::new(self), m)
    }
    pub fn rem(self, m: u64) -> Expr {
        Expr::Rem(Box::new(self), m)
    }
    /// Bitwise AND with another **expression** (as opposed to [`Expr::and`]'s constant mask).
    pub fn and_e(self, o: Expr) -> Expr {
        Expr::AndE(Box::new(self), Box::new(o))
    }
    /// Bitwise OR with another expression.
    pub fn or_e(self, o: Expr) -> Expr {
        Expr::OrE(Box::new(self), Box::new(o))
    }
    /// Bitwise XOR with another expression.
    pub fn xor_e(self, o: Expr) -> Expr {
        Expr::XorE(Box::new(self), Box::new(o))
    }
    /// Left shift by a variable amount.
    pub fn shl_e(self, o: Expr) -> Expr {
        Expr::ShlE(Box::new(self), Box::new(o))
    }
    /// Right shift by a variable amount.
    pub fn shr_e(self, o: Expr) -> Expr {
        Expr::ShrE(Box::new(self), Box::new(o))
    }

    /// Substitute every variable by its next-state expression: `Var(i)` becomes `next[i]`. This is how a
    /// transition system's step is applied to an invariant (turn `inv(state)` into `inv(next_state)`).
    pub fn subst(&self, next: &[Expr]) -> Expr {
        match self {
            Expr::Var(i) => next.get(*i as usize).cloned().unwrap_or(Expr::Var(*i)),
            Expr::Const(v) => Expr::Const(*v),
            Expr::Add(a, b) => Expr::Add(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::Sub(a, b) => Expr::Sub(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::Mul(a, b) => Expr::Mul(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::Shl(a, k) => Expr::Shl(Box::new(a.subst(next)), *k),
            Expr::Shr(a, k) => Expr::Shr(Box::new(a.subst(next)), *k),
            Expr::And(a, m) => Expr::And(Box::new(a.subst(next)), *m),
            Expr::Or(a, m) => Expr::Or(Box::new(a.subst(next)), *m),
            Expr::Rem(a, m) => Expr::Rem(Box::new(a.subst(next)), *m),
            Expr::AndE(a, b) => Expr::AndE(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::OrE(a, b) => Expr::OrE(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::XorE(a, b) => Expr::XorE(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::ShlE(a, b) => Expr::ShlE(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::ShrE(a, b) => Expr::ShrE(Box::new(a.subst(next)), Box::new(b.subst(next))),
        }
    }

    /// Abstract evaluation: the interval of every value this expression can take when each variable `i`
    /// ranges over `doms[i]`. Guaranteed to be a superset of the true value set (soundness). An
    /// out-of-range variable index defaults to the full domain (still sound).
    fn eval_iv(&self, doms: &[Iv]) -> Iv {
        match self {
            Expr::Var(i) => doms.get(*i as usize).copied().unwrap_or_else(Iv::full),
            Expr::Const(v) => Iv::point(*v),
            Expr::Add(a, b) => a.eval_iv(doms).add(b.eval_iv(doms)),
            Expr::Sub(a, b) => a.eval_iv(doms).sub(b.eval_iv(doms)),
            Expr::Mul(a, b) => a.eval_iv(doms).mul(b.eval_iv(doms)),
            Expr::Shl(a, k) => a.eval_iv(doms).shl(*k),
            Expr::Shr(a, k) => a.eval_iv(doms).shr(*k),
            Expr::And(a, m) => a.eval_iv(doms).bitand(*m),
            Expr::Or(a, m) => a.eval_iv(doms).bitor(*m),
            Expr::Rem(a, m) => a.eval_iv(doms).rem(*m),
            Expr::AndE(a, b) => a.eval_iv(doms).bitand_iv(b.eval_iv(doms)),
            Expr::OrE(a, b) => a.eval_iv(doms).bitor_iv(b.eval_iv(doms)),
            Expr::XorE(a, b) => a.eval_iv(doms).bitxor_iv(b.eval_iv(doms)),
            Expr::ShlE(a, b) => a.eval_iv(doms).shl_iv(b.eval_iv(doms)),
            Expr::ShrE(a, b) => a.eval_iv(doms).shr_iv(b.eval_iv(doms)),
        }
    }

    /// Concrete evaluation at an assignment `xs` (wrapping `u64` arithmetic) — used to confirm witnesses.
    fn eval_at(&self, xs: &[u64]) -> u64 {
        match self {
            Expr::Var(i) => xs.get(*i as usize).copied().unwrap_or(0),
            Expr::Const(v) => *v,
            Expr::Add(a, b) => a.eval_at(xs).wrapping_add(b.eval_at(xs)),
            Expr::Sub(a, b) => a.eval_at(xs).wrapping_sub(b.eval_at(xs)),
            Expr::Mul(a, b) => a.eval_at(xs).wrapping_mul(b.eval_at(xs)),
            Expr::Shl(a, k) => a.eval_at(xs).wrapping_shl(*k),
            Expr::Shr(a, k) => a.eval_at(xs).wrapping_shr(*k),
            Expr::And(a, m) => a.eval_at(xs) & *m,
            Expr::Or(a, m) => a.eval_at(xs) | *m,
            Expr::Rem(a, m) => {
                if *m == 0 {
                    0
                } else {
                    a.eval_at(xs) % *m
                }
            }
            Expr::AndE(a, b) => a.eval_at(xs) & b.eval_at(xs),
            Expr::OrE(a, b) => a.eval_at(xs) | b.eval_at(xs),
            Expr::XorE(a, b) => a.eval_at(xs) ^ b.eval_at(xs),
            // Wrapping, to match the constant-shift arms above and `Iv::shl_iv`/`Iv::shr_iv`.
            Expr::ShlE(a, b) => a.eval_at(xs).wrapping_shl(b.eval_at(xs) as u32),
            Expr::ShrE(a, b) => a.eval_at(xs).wrapping_shr(b.eval_at(xs) as u32),
        }
    }
}

/// Three-valued logic: the outcome of deciding a proposition over an *interval* abstraction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tri {
    True,
    False,
    Unknown,
}

impl Tri {
    fn negate(self) -> Tri {
        match self {
            Tri::True => Tri::False,
            Tri::False => Tri::True,
            Tri::Unknown => Tri::Unknown,
        }
    }
    fn and(self, o: Tri) -> Tri {
        match (self, o) {
            (Tri::False, _) | (_, Tri::False) => Tri::False,
            (Tri::True, Tri::True) => Tri::True,
            _ => Tri::Unknown,
        }
    }
    fn or(self, o: Tri) -> Tri {
        match (self, o) {
            (Tri::True, _) | (_, Tri::True) => Tri::True,
            (Tri::False, Tri::False) => Tri::False,
            _ => Tri::Unknown,
        }
    }
}

/// A boolean property of the symbolic variables, built from comparisons of [`Expr`]s and connectives.
#[derive(Clone, Debug)]
pub enum Prop {
    Le(Expr, Expr),
    Lt(Expr, Expr),
    Ge(Expr, Expr),
    Gt(Expr, Expr),
    Eq(Expr, Expr),
    Ne(Expr, Expr),
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
    Not(Box<Prop>),
    /// `a -> b`, i.e. `!a || b`.
    Implies(Box<Prop>, Box<Prop>),
}

impl Prop {
    pub fn and(self, o: Prop) -> Prop {
        Prop::And(Box::new(self), Box::new(o))
    }
    pub fn or(self, o: Prop) -> Prop {
        Prop::Or(Box::new(self), Box::new(o))
    }
    pub fn not(self) -> Prop {
        Prop::Not(Box::new(self))
    }
    pub fn implies(self, o: Prop) -> Prop {
        Prop::Implies(Box::new(self), Box::new(o))
    }

    /// Substitute every variable in this proposition by its next-state expression (`Var(i)` -> `next[i]`).
    /// Turns `inv(state)` into `inv(next_state)` — the heart of an inductive consecution check.
    pub fn subst(&self, next: &[Expr]) -> Prop {
        match self {
            Prop::Le(a, b) => Prop::Le(a.subst(next), b.subst(next)),
            Prop::Lt(a, b) => Prop::Lt(a.subst(next), b.subst(next)),
            Prop::Ge(a, b) => Prop::Ge(a.subst(next), b.subst(next)),
            Prop::Gt(a, b) => Prop::Gt(a.subst(next), b.subst(next)),
            Prop::Eq(a, b) => Prop::Eq(a.subst(next), b.subst(next)),
            Prop::Ne(a, b) => Prop::Ne(a.subst(next), b.subst(next)),
            Prop::And(p, q) => Prop::And(Box::new(p.subst(next)), Box::new(q.subst(next))),
            Prop::Or(p, q) => Prop::Or(Box::new(p.subst(next)), Box::new(q.subst(next))),
            Prop::Not(p) => Prop::Not(Box::new(p.subst(next))),
            Prop::Implies(p, q) => Prop::Implies(Box::new(p.subst(next)), Box::new(q.subst(next))),
        }
    }

    fn eval_iv(&self, doms: &[Iv]) -> Tri {
        match self {
            Prop::Le(a, b) => cmp_le_full(a, b, doms),
            Prop::Lt(a, b) => cmp_lt_full(a, b, doms),
            Prop::Ge(a, b) => cmp_le_full(b, a, doms),
            Prop::Gt(a, b) => cmp_lt_full(b, a, doms),
            Prop::Eq(a, b) => cmp_eq_full(a, b, doms),
            Prop::Ne(a, b) => cmp_eq_full(a, b, doms).negate(),
            Prop::And(p, q) => p.eval_iv(doms).and(q.eval_iv(doms)),
            Prop::Or(p, q) => p.eval_iv(doms).or(q.eval_iv(doms)),
            Prop::Not(p) => p.eval_iv(doms).negate(),
            // `P -> Q` is `!P || Q`. Evaluating both sides over intervals treats the two
            // occurrences of a SHARED sub-proposition as independent, so the tautology `P -> P`
            // comes back `Unknown`: `Unknown.negate().or(Unknown)` is `Unknown`.
            //
            // That is not a corner case, it is the ordinary shape of a lifted verification goal. A
            // function lifted from MIR produces one guarded case per path, and
            // `LiftedFn::postcondition` builds `guard -> claim`; whenever the property being checked
            // is the branch condition the compiler itself tested — which is exactly what
            // `if held & req == req` does — the goal IS `P -> P`. Before this rule the engine
            // returned `Unknown` for the CORRECT function, and a verdict that is `Unknown` for both
            // the correct and the corrupted version distinguishes nothing at all.
            //
            // Sound because it is a propositional tautology, decided structurally and never against
            // the abstraction: `entails(p, q)` answers `true` only when `q` is syntactically `p` or a
            // conjunct of it, in which case `p -> q` holds in every model.
            Prop::Implies(p, q) => {
                if entails(p, q) {
                    Tri::True
                } else {
                    p.eval_iv(doms).negate().or(q.eval_iv(doms))
                }
            }
        }
    }

    fn eval_at(&self, xs: &[u64]) -> bool {
        match self {
            Prop::Le(a, b) => a.eval_at(xs) <= b.eval_at(xs),
            Prop::Lt(a, b) => a.eval_at(xs) < b.eval_at(xs),
            Prop::Ge(a, b) => a.eval_at(xs) >= b.eval_at(xs),
            Prop::Gt(a, b) => a.eval_at(xs) > b.eval_at(xs),
            Prop::Eq(a, b) => a.eval_at(xs) == b.eval_at(xs),
            Prop::Ne(a, b) => a.eval_at(xs) != b.eval_at(xs),
            Prop::And(p, q) => p.eval_at(xs) && q.eval_at(xs),
            Prop::Or(p, q) => p.eval_at(xs) || q.eval_at(xs),
            Prop::Not(p) => !p.eval_at(xs),
            Prop::Implies(p, q) => !p.eval_at(xs) || q.eval_at(xs),
        }
    }
}

// ── Phase D: affine (linear) relational reasoning ─────────────────────────────────────────────────
//
// A plain interval domain evaluates each occurrence of a variable independently, so it can't see that
// the two `x`s in `x <= x + y` are the *same* value. Representing the LINEAR fragment as an affine form
// `c + Σ cᵢ·vᵢ` lets a comparison `a ≤ b` be decided from the bounds of `a − b`, where shared terms
// cancel (`x − (x + y) = −y`) — proving relational facts with no splitting.
//
// SOUNDNESS vs u64 wrapping: the affine form is exact integer math, but the engine's semantics are
// *wrapping* u64. We only use affine reasoning when it provably matches: the fragment is built solely
// from non-negative, non-decreasing ops (Var / Const / Add / Mul-by-const / Shl), so every value is
// ≥ 0, and we require each operand's maximum over the domain to be ≤ u64::MAX (no overflow). Under
// those two conditions the u64 value equals the integer value, so the u64 comparison equals the
// integer one. Anything else (Sub, Shr, And, Or, Rem, var·var) is not affine here and falls back to
// the interval comparison — never an unsound shortcut.

/// A linear form `c + Σ coeffs[(var, coeff)]` over `i128`.
///
/// # `i128` is wide enough for one u64 magnitude, not for a product of them
///
/// Sums and differences of u64-sized quantities fit here with room to spare. **Products of
/// coefficients do not.** `to_affine` multiplies a coefficient by a constant on every `Mul`-by-const
/// and by `1 << k` on every `Shl`, so a nested expression like `(x * u64::MAX) * u64::MAX` asks for a
/// coefficient of `(2^64 - 1)^2 ≈ 3.4e38`, and `i128::MAX ≈ 1.7e38`.
///
/// That is not a precision question, it is a soundness one, and it went both ways at once:
///
/// * under `debug-assertions` the multiplication **panicked** — the proof engine crashing on an
///   ordinary expression a caller is entitled to hand it;
/// * in a release build it **wrapped**, and a wrapped coefficient is negative, so `bounds` reported a
///   maximum of `0` for a form whose true values are positive. `cmp_le_full` read `a - b <= 0`
///   everywhere and `prove_forall_n` returned **`Proven` for a property that is false at x = 1**.
///
/// So every operation below is checked and returns `None` on overflow. `to_affine` already returns
/// `Option`, and its `None` means "not in the linear fragment — fall back to the interval domain",
/// which is always sound. An affine form that cannot be represented is exactly that case.
struct Affine {
    c: i128,
    coeffs: Vec<(u32, i128)>,
}

impl Affine {
    fn add(mut self, o: Affine) -> Option<Affine> {
        self.c = self.c.checked_add(o.c)?;
        for (v, k) in o.coeffs {
            match self.coeffs.iter_mut().find(|(vv, _)| *vv == v) {
                Some(e) => e.1 = e.1.checked_add(k)?,
                None => self.coeffs.push((v, k)),
            }
        }
        Some(self)
    }
    fn scale(mut self, s: i128) -> Option<Affine> {
        self.c = self.c.checked_mul(s)?;
        for e in self.coeffs.iter_mut() {
            e.1 = e.1.checked_mul(s)?;
        }
        Some(self)
    }
    fn neg(self) -> Option<Affine> {
        self.scale(-1)
    }
    /// The (min, max) of this form over the variable domains, exact in `i128`.
    ///
    /// `None` when the exact value does not fit — the caller must then decline affine reasoning
    /// rather than proceed on a wrapped figure.
    fn bounds(&self, doms: &[Iv]) -> Option<(i128, i128)> {
        let mut lo = self.c;
        let mut hi = self.c;
        for &(v, k) in &self.coeffs {
            let d = doms.get(v as usize).copied().unwrap_or_else(Iv::full);
            let (dl, dh) = (d.lo as i128, d.hi as i128);
            let (klo, khi) = if k >= 0 { (dl, dh) } else { (dh, dl) };
            lo = lo.checked_add(k.checked_mul(klo)?)?;
            hi = hi.checked_add(k.checked_mul(khi)?)?;
        }
        Some((lo, hi))
    }
}

/// The affine form of the linear fragment (`None` for anything non-linear or possibly-negative).
fn to_affine(e: &Expr) -> Option<Affine> {
    match e {
        Expr::Var(i) => Some(Affine {
            c: 0,
            coeffs: alloc::vec![(*i, 1)],
        }),
        Expr::Const(v) => Some(Affine {
            c: *v as i128,
            coeffs: Vec::new(),
        }),
        Expr::Add(a, b) => to_affine(a)?.add(to_affine(b)?),
        Expr::Mul(a, b) => {
            let (af, bf) = (to_affine(a)?, to_affine(b)?);
            if af.coeffs.is_empty() {
                bf.scale(af.c)
            } else if bf.coeffs.is_empty() {
                af.scale(bf.c)
            } else {
                None // var·var is non-linear
            }
        }
        Expr::Shl(a, k) if *k < 63 => to_affine(a)?.scale(1i128 << k),
        // Sub can go negative (u64 wrap); Shr/And/Or/Rem are non-linear — fall back to intervals.
        _ => None,
    }
}

/// If both sides are affine and provably non-wrapping over the domain, decide `a - b` vs 0 relationally.
/// Returns `None` when affine reasoning doesn't apply (caller falls back to the interval comparison).
fn affine_diff(a: &Expr, b: &Expr, doms: &[Iv]) -> Option<(i128, i128)> {
    let (af, bf) = (to_affine(a)?, to_affine(b)?);
    const MAX: i128 = u64::MAX as i128;
    // No overflow in computing either operand (both are ≥ 0 by construction of the fragment).
    // A `None` from `bounds` is an unrepresentable form, and declines affine reasoning for the same
    // reason an over-MAX bound does: the u64 value would not equal the integer value.
    if af.bounds(doms)?.1 > MAX || bf.bounds(doms)?.1 > MAX {
        return None;
    }
    af.add(bf.neg()?)?.bounds(doms) // bounds of (a - b)
}

/// Structural equality of two expressions — "these are syntactically the same term".
///
/// Used only to recognise the shared operand in a bitwise dominance law (`x & y <= x`). It is
/// deliberately conservative: two expressions that are equal in value but written differently
/// (`x + 0` vs `x`) answer `false`, which costs precision and never soundness.
fn same_expr(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Var(i), Expr::Var(j)) => i == j,
        (Expr::Const(x), Expr::Const(y)) => x == y,
        (Expr::Add(a1, a2), Expr::Add(b1, b2))
        | (Expr::Sub(a1, a2), Expr::Sub(b1, b2))
        | (Expr::Mul(a1, a2), Expr::Mul(b1, b2))
        | (Expr::AndE(a1, a2), Expr::AndE(b1, b2))
        | (Expr::OrE(a1, a2), Expr::OrE(b1, b2))
        | (Expr::XorE(a1, a2), Expr::XorE(b1, b2))
        | (Expr::ShlE(a1, a2), Expr::ShlE(b1, b2))
        | (Expr::ShrE(a1, a2), Expr::ShrE(b1, b2)) => same_expr(a1, b1) && same_expr(a2, b2),
        (Expr::Shl(a1, k1), Expr::Shl(b1, k2)) | (Expr::Shr(a1, k1), Expr::Shr(b1, k2)) => {
            k1 == k2 && same_expr(a1, b1)
        }
        (Expr::And(a1, m1), Expr::And(b1, m2))
        | (Expr::Or(a1, m1), Expr::Or(b1, m2))
        | (Expr::Rem(a1, m1), Expr::Rem(b1, m2)) => m1 == m2 && same_expr(a1, b1),
        _ => false,
    }
}

/// Bitwise dominance: whether `a <= b` follows from the SHAPE of the two terms alone.
///
/// # Why this exists, and why it is not an interval fact
///
/// `x & y <= x` is a theorem of unsigned bitwise arithmetic for every `x` and `y` — clearing bits
/// cannot increase a value. The interval domain cannot see it: over the full `u64` box both sides
/// evaluate to `[0, u64::MAX]`, so [`cmp_le`] answers `Unknown`, exactly as it does for two
/// unrelated variables. That is a *relational* fact about a shared operand, which is the same class
/// of fact the affine fragment above recovers for `+`/`-` — and this is its bitwise counterpart.
///
/// The cost of not having it was concrete and was measured, not guessed: `Cap::attenuate` computes
/// `rights & keep`, and the delegation argument "a child never holds a right the parent lacked" is
/// exactly `(rights & keep) <= rights`. Lifted straight from the compiler's MIR, that property came
/// back `Unknown` — so the induced-defect experiment could not even establish its own control, and a
/// verdict that is `Unknown` for both the correct and the corrupted function distinguishes nothing.
///
/// # Soundness
///
/// Each rule is a theorem over all `u64` values, independent of any domain:
///  * `x & y <= x` and `x & y <= y` — AND only clears bits.
///  * `x <= x | y` and `y <= x | y` — OR only sets bits.
///  * `x & m <= x` (constant mask) and `x <= x | m`.
///  * `x >> k <= x` — a right shift never increases an unsigned value.
///  * `x % m <= x` for `m != 0` — a remainder never exceeds its dividend.
///  * `x <= x` — reflexivity.
///
/// Returning `false` is always safe: the caller falls back to the interval comparison.
fn bitwise_dominates(small: &Expr, big: &Expr) -> bool {
    if same_expr(small, big) {
        return true; // x <= x
    }
    // Rules where the SMALLER side is the compound term.
    match small {
        // (x & y) <= x, and (x & y) <= y
        Expr::AndE(x, y) => {
            if bitwise_dominates(x, big) || bitwise_dominates(y, big) {
                return true;
            }
        }
        // (x & m) <= x
        Expr::And(x, _) => {
            if bitwise_dominates(x, big) {
                return true;
            }
        }
        // (x >> k) <= x
        Expr::Shr(x, _) => {
            if bitwise_dominates(x, big) {
                return true;
            }
        }
        // (x % m) <= x, for a non-zero modulus. `m == 0` is `Fault::DivByZero` territory and
        // `eval_at` yields 0 there, so the rule would still hold — but it is excluded rather than
        // relied upon, because the engine's two evaluators treat `% 0` differently and a law that
        // depends on which one ran is not a law.
        Expr::Rem(x, m) if *m != 0 && bitwise_dominates(x, big) => return true,
        _ => {}
    }
    // Rules where the LARGER side is the compound term.
    match big {
        // x <= (x | y), and y <= (x | y)
        Expr::OrE(x, y) => bitwise_dominates(small, x) || bitwise_dominates(small, y),
        // x <= (x | m)
        Expr::Or(x, _) => bitwise_dominates(small, x),
        _ => false,
    }
}

/// Structural equality of two propositions.
///
/// Conservative in the same way [`same_expr`] is: two propositions that are logically equivalent but
/// written differently answer `false`. That costs precision (an honest `Unknown`) and never
/// soundness.
fn same_prop(a: &Prop, b: &Prop) -> bool {
    match (a, b) {
        (Prop::Le(a1, a2), Prop::Le(b1, b2))
        | (Prop::Lt(a1, a2), Prop::Lt(b1, b2))
        | (Prop::Ge(a1, a2), Prop::Ge(b1, b2))
        | (Prop::Gt(a1, a2), Prop::Gt(b1, b2))
        | (Prop::Eq(a1, a2), Prop::Eq(b1, b2))
        | (Prop::Ne(a1, a2), Prop::Ne(b1, b2)) => same_expr(a1, b1) && same_expr(a2, b2),
        (Prop::And(a1, a2), Prop::And(b1, b2))
        | (Prop::Or(a1, a2), Prop::Or(b1, b2))
        | (Prop::Implies(a1, a2), Prop::Implies(b1, b2)) => same_prop(a1, b1) && same_prop(a2, b2),
        (Prop::Not(a1), Prop::Not(b1)) => same_prop(a1, b1),
        _ => false,
    }
}

/// Whether `p` syntactically entails `q` — i.e. `p -> q` holds in every model, decided from shape
/// alone.
///
/// Two rules, both propositional tautologies:
///  * `p -> p` (reflexivity).
///  * `(a ∧ b) -> q` whenever `a` entails `q` or `b` entails `q` (conjunction elimination).
///
/// A `false` answer means "not decided here", and the caller falls back to the interval evaluation.
fn entails(p: &Prop, q: &Prop) -> bool {
    if same_prop(p, q) {
        return true;
    }
    // Assuming a conjunction lets either conjunct discharge the goal — this is what makes a lifted
    // goal decidable when the path guard is `a ∧ b` and the claim is one of them, which is the shape
    // `LiftedFn::postcondition` produces for a nested branch.
    if let Prop::And(a, b) = p {
        if entails(a, q) || entails(b, q) {
            return true;
        }
    }
    // A conjunctive GOAL is discharged when every conjunct is.
    if let Prop::And(a, b) = q {
        return entails(p, a) && entails(p, b);
    }
    // WEAKENING: if `p` entails `q`, then `p` entails `a -> q` for ANY `a`, because a true
    // consequent makes the implication true regardless of its antecedent.
    //
    // This is the rule the lifted goals actually need. `LiftedFn::postcondition` emits
    // `guard -> claim(value)`, and a claim written as an implication (`result == 1 -> ...`, the
    // natural way to state "whatever this function admits, the following holds") makes the goal
    // `guard -> (antecedent -> guard)`. Without weakening the engine evaluates the inner `guard`
    // against intervals independently of the outer one and answers `Unknown` — for the CORRECT
    // function.
    if let Prop::Implies(_, inner_q) = q {
        if entails(p, inner_q) {
            return true;
        }
    }
    // And the dual on the left: `(a -> b)` entails `q` when `b` does AND `a` is discharged by `p`.
    // Not attempted — it needs `p |= a`, which reintroduces the same undecidability this function
    // exists to sidestep. Left as an honest gap rather than an unsound shortcut.
    false
}

fn cmp_le_full(a: &Expr, b: &Expr, doms: &[Iv]) -> Tri {
    if let Some((dlo, dhi)) = affine_diff(a, b, doms) {
        if dhi <= 0 {
            return Tri::True; // a - b <= 0 everywhere
        }
        if dlo > 0 {
            return Tri::False;
        }
    }
    // The bitwise counterpart of the affine rule above: a relational fact the interval domain loses.
    // Checked AFTER affine (which can also return False) and BEFORE the interval fallback, and only
    // ever able to turn an `Unknown` into a `True` — it never contradicts a decided answer.
    if bitwise_dominates(a, b) {
        return Tri::True;
    }
    cmp_le(a.eval_iv(doms), b.eval_iv(doms))
}

fn cmp_lt_full(a: &Expr, b: &Expr, doms: &[Iv]) -> Tri {
    if let Some((dlo, dhi)) = affine_diff(a, b, doms) {
        if dhi < 0 {
            return Tri::True;
        }
        if dlo >= 0 {
            return Tri::False;
        }
    }
    cmp_lt(a.eval_iv(doms), b.eval_iv(doms))
}

fn cmp_eq_full(a: &Expr, b: &Expr, doms: &[Iv]) -> Tri {
    if let Some((dlo, dhi)) = affine_diff(a, b, doms) {
        if dlo == 0 && dhi == 0 {
            return Tri::True; // a - b is identically 0
        }
        if dlo > 0 || dhi < 0 {
            return Tri::False; // 0 not attainable
        }
    }
    cmp_eq(a.eval_iv(doms), b.eval_iv(doms))
}

fn cmp_le(a: Iv, b: Iv) -> Tri {
    if a.hi <= b.lo {
        Tri::True
    } else if a.lo > b.hi {
        Tri::False
    } else {
        Tri::Unknown
    }
}
fn cmp_lt(a: Iv, b: Iv) -> Tri {
    if a.hi < b.lo {
        Tri::True
    } else if a.lo >= b.hi {
        Tri::False
    } else {
        Tri::Unknown
    }
}
fn cmp_eq(a: Iv, b: Iv) -> Tri {
    if a.lo == a.hi && b.lo == b.hi && a.lo == b.lo {
        Tri::True
    } else if a.hi < b.lo || b.hi < a.lo {
        Tri::False
    } else {
        Tri::Unknown
    }
}

/// The interval every value of `e` is guaranteed to fall inside, when variable `i` ranges over
/// `doms[i]` — the abstraction that every tier-5 verdict in this workspace is ultimately computed from.
///
/// # The contract, which is this crate's central claim
///
/// For **every** assignment `xs` with `doms[i].contains(xs[i])`, the concrete value of `e` at `xs`
/// — ordinary wrapping `u64` arithmetic, as [`Expr`] documents — lies inside the returned interval.
///
/// The interval may be **wider** than the true value set. That costs precision and surfaces as
/// [`SymVerdict::Unknown`], which is an honest answer. It must never be **narrower**: a missing value
/// lets the three-valued comparison read `True` where the truth is mixed, and [`prove_forall_n`]
/// returns `Proven` for a property that is false. Nothing downstream re-derives that verdict, so
/// nothing downstream could catch it.
///
/// # Why this is public
///
/// Because until it was, the claim above could not be checked from outside the engine at all. The only
/// way an under-approximation could be noticed was when it happened to *flip a comparison*, which
/// requires the sample to contain both the faulty shape and an operand positioned to expose it — a
/// detour that a plausible-looking sample misses silently. Exposing the interval turns the soundness
/// lemma into something a proof can assert directly, at the point where it is actually violated.
///
/// ```
/// use aion_verify::symbolic::{interval_of, Expr, Iv};
///
/// // x + 1 over x in [0, 10] can only be [1, 11].
/// let iv = interval_of(&[Iv::new(0, 10)], &Expr::var().add(Expr::c(1)));
/// assert_eq!((iv.lo, iv.hi), (1, 11));
///
/// // Widening is legal; narrowing is not. x - 1 over x in [0, 10] can wrap, so the abstraction
/// // gives up the whole domain rather than reporting an interval that excludes u64::MAX.
/// assert_eq!(interval_of(&[Iv::new(0, 10)], &Expr::var().sub(Expr::c(1))), Iv::full());
/// ```
/// True when any variable's domain is the empty set — see [`Iv::is_empty`] for what that costs.
///
/// The one place the answer is decided, so `interval_of` and the five `prove_*` entry points cannot
/// drift apart on it.
fn any_empty(doms: &[Iv]) -> bool {
    doms.iter().any(Iv::is_empty)
}

pub fn interval_of(doms: &[Iv], e: &Expr) -> Iv {
    // An empty box admits no assignment, so the containment lemma above is vacuously true of ANY
    // returned interval — and the empty one is the only answer that is also true of the value SET.
    // Returning it here rather than evaluating is not cosmetic: `Iv::shl` guards on `hi` and shifts
    // `lo`, so evaluating over an inverted interval overflow-panics under `debug-assertions`.
    if any_empty(doms) {
        return Iv::empty();
    }
    e.eval_iv(doms)
}

/// The outcome of a tier-5 symbolic proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymVerdict {
    /// The property holds for every assignment in the domain — a proof, no enumeration.
    Proven,
    /// The property fails; `witness[i]` is a concrete value for variable `i` that falsifies it
    /// (confirmed by concrete evaluation).
    Refuted { witness: Vec<u64> },
    /// The interval abstraction was too imprecise to decide. Never a false Proven/Refuted.
    Unknown,
}

/// Prove `prop` holds for every value of a **single** variable `x` in `domain` (convenience for the
/// common one-variable case). See [`prove_forall_n`] for multiple variables.
pub fn prove_forall(domain: Iv, prop: &Prop) -> SymVerdict {
    prove_forall_n(&[domain], prop)
}

/// Prove `prop` holds for **every** assignment where variable `i` ranges over `doms[i]` — symbolically,
/// without enumerating the domain.
///
/// Sound: a `Proven` result means the interval analysis established the property over a *superset* of
/// the domain, so it holds for the domain itself. A `Refuted` result is always backed by a concrete
/// assignment confirmed with wrapping arithmetic. Otherwise `Unknown`.
/// # An empty domain is refused, not reasoned over
///
/// If any `doms[i]` [is empty](Iv::is_empty) the answer is [`SymVerdict::Unknown`]. Two other answers
/// were available and both are worse. `Proven` is *technically* right — every property holds over a
/// domain with no assignments in it — and is the single most dangerous verdict this engine can emit:
/// a silent vacuous proof, with no `cases` figure to expose it the way [`crate::Verdict::is_vacuous`]
/// exposes the tier-4 equivalent. `Refuted` is what the code did before, reporting `witness: [d.lo]`
/// for a `d.lo` the domain excludes — a counterexample outside the domain it claims to be a
/// counterexample in.
///
/// Normalising (swapping `lo` and `hi`, as [`Iv::new`] does) was rejected as well: `Iv::new` swaps
/// because the caller stated an intent and got the order wrong, while a struct literal that reaches
/// here has already escaped that check, and silently deciding which of the two bounds the caller
/// meant is a guess the engine would then report as a proof.
pub fn prove_forall_n(doms: &[Iv], prop: &Prop) -> SymVerdict {
    if any_empty(doms) {
        return SymVerdict::Unknown;
    }
    match prop.eval_iv(doms) {
        Tri::True => SymVerdict::Proven,
        Tri::False => {
            // False across the whole (over-approximated) domain; the all-low corner is a real assignment
            // — confirm it concretely so the witness is never spurious.
            let xs: Vec<u64> = doms.iter().map(|d| d.lo).collect();
            if !prop.eval_at(&xs) {
                SymVerdict::Refuted { witness: xs }
            } else {
                probe(doms, prop)
            }
        }
        Tri::Unknown => probe(doms, prop),
    }
}

/// Prove a **function contract**: that `postcond` holds for every assignment in `doms` for which
/// `precond` holds. This is `forall x. precond(x) -> postcond(x)` — the core of verifying a function or
/// component's behaviour (validate inputs in the precondition, guarantee the postcondition).
pub fn prove_contract(doms: &[Iv], precond: &Prop, postcond: &Prop) -> SymVerdict {
    let implication = precond.clone().implies(postcond.clone());
    prove_forall_n(doms, &implication)
}

/// Prove an **inductive invariant** of a transition system — the first-party way to reason about a
/// *loop or state machine* without unrolling it. Given:
///  - `init_doms`: the set of initial states,
///  - `guard`: the condition under which a step is taken (the loop condition),
///  - `transition[i]`: the next value of variable `i` after one step,
///  - `invariant`: the property to establish for **every reachable state**,
///  - `state_doms`: a domain covering the reachable states (over which preservation is checked),
///
/// it checks the two classic conditions and, if both hold, the invariant holds for *all* iterations:
///  1. **Initiation** — the invariant holds in every initial state.
///  2. **Consecution** — if the invariant and the guard hold, they still hold after one step
///     (`(invariant ∧ guard) → invariant[next]`).
///
/// Returns [`SymVerdict::Proven`] only when both hold; otherwise the failing check's verdict (a
/// `Refuted` names a concrete state that breaks it). `max_splits` bounds the refinement used on each
/// verification condition. This handles **state**, which the value-only tiers do not.
const fn as_var(e: &Expr) -> Option<u32> {
    if let Expr::Var(i) = e {
        Some(*i)
    } else {
        None
    }
}
const fn as_const(e: &Expr) -> Option<u64> {
    if let Expr::Const(v) = e {
        Some(*v)
    } else {
        None
    }
}

/// Narrow a domain box by the box-expressible constraints in `p` (conjunctions of `variable vs constant`
/// comparisons) — "assume `p` holds". Returns `None` if the constraints make the box empty (so `p` is
/// unsatisfiable on it). Relational/disjunctive parts are ignored (a sound over-approximation: we assume
/// *less*, so a proof over the wider box still holds). This is Phase G's key move: assume the invariant
/// and guard, then prove preservation on the *narrowed* region — which works over UNBOUNDED state.
fn assume_narrow(p: &Prop, doms: &[Iv]) -> Option<Vec<Iv>> {
    let mut d = doms.to_vec();
    fn le(a: &Expr, b: &Expr, d: &mut [Iv]) -> Option<()> {
        if let (Some(vi), Some(c)) = (as_var(a), as_const(b)) {
            let iv = d.get_mut(vi as usize)?;
            iv.hi = iv.hi.min(c);
            if iv.lo > iv.hi {
                return None;
            }
        } else if let (Some(c), Some(vi)) = (as_const(a), as_var(b)) {
            let iv = d.get_mut(vi as usize)?;
            iv.lo = iv.lo.max(c);
            if iv.lo > iv.hi {
                return None;
            }
        }
        Some(())
    }
    fn lt(a: &Expr, b: &Expr, d: &mut [Iv]) -> Option<()> {
        if let (Some(vi), Some(c)) = (as_var(a), as_const(b)) {
            if c == 0 {
                return None; // var < 0 is impossible for unsigned
            }
            let iv = d.get_mut(vi as usize)?;
            iv.hi = iv.hi.min(c - 1);
            if iv.lo > iv.hi {
                return None;
            }
        } else if let (Some(c), Some(vi)) = (as_const(a), as_var(b)) {
            let iv = d.get_mut(vi as usize)?;
            iv.lo = iv.lo.max(c.saturating_add(1));
            if iv.lo > iv.hi {
                return None;
            }
        }
        Some(())
    }
    fn go(p: &Prop, d: &mut [Iv]) -> Option<()> {
        match p {
            Prop::And(a, b) => {
                go(a, d)?;
                go(b, d)
            }
            Prop::Le(a, b) => le(a, b, d),
            Prop::Lt(a, b) => lt(a, b, d),
            Prop::Ge(a, b) => le(b, a, d),
            Prop::Gt(a, b) => lt(b, a, d),
            Prop::Eq(a, b) => {
                le(a, b, d)?;
                le(b, a, d)
            }
            _ => Some(()), // Or / Not / Ne / relational: no box narrowing (assume less — sound)
        }
    }
    go(p, &mut d)?;
    Some(d)
}

pub fn prove_inductive(
    init_doms: &[Iv],
    guard: &Prop,
    transition: &[Expr],
    invariant: &Prop,
    state_doms: &[Iv],
    max_splits: u32,
) -> SymVerdict {
    // Both boxes are checked HERE rather than left to the calls below. `prove_forall_refine` would
    // catch an empty `init_doms`, but an empty `state_doms` reaches `assume_narrow` first, which
    // returns `None` for an unsatisfiable narrowing and which this function maps to `Proven` —
    // "no state satisfies (invariant ∧ guard)". That mapping is right for a narrowing that emptied a
    // real box and wrong for a box the caller handed over already empty, and the two are
    // indistinguishable by the time `assume_narrow` answers.
    if any_empty(init_doms) || any_empty(state_doms) {
        return SymVerdict::Unknown;
    }
    // 1. Initiation: the invariant holds in every initial state.
    let initiation = prove_forall_refine(init_doms, invariant, max_splits);
    if initiation != SymVerdict::Proven {
        return initiation;
    }
    // 2. Consecution: (invariant ∧ guard) ⇒ invariant after one step.
    let inv_next = invariant.subst(transition);
    let assumption = invariant.clone().and(guard.clone());
    // Phase G: assume the invariant+guard by narrowing the state box, then prove preservation there.
    // This discharges the common (box-expressible) case over UNBOUNDED state with no refinement.
    match assume_narrow(&assumption, state_doms) {
        None => SymVerdict::Proven, // no state satisfies (invariant ∧ guard) here — vacuously preserved
        Some(narrowed) => {
            if prove_forall_refine(&narrowed, &inv_next, max_splits) == SymVerdict::Proven {
                return SymVerdict::Proven;
            }
            // Narrowing dropped a relational part (or it genuinely fails) — fall back to the full,
            // always-sound verification condition over the whole state domain.
            let vc = assumption.implies(inv_next);
            prove_forall_refine(state_doms, &vc, max_splits)
        }
    }
}

/// When the abstraction can't decide, try the assignments most likely to break a property — the corners
/// of the domain box and per-variable special values — concretely. A hit is a genuine counterexample.
fn probe(doms: &[Iv], prop: &Prop) -> SymVerdict {
    let n = doms.len();
    // Corners of the domain box: each variable at its lo or hi. Bounded to 2^12 to stay fast.
    if n <= 12 {
        for mask in 0u32..(1u32 << n) {
            let xs: Vec<u64> = (0..n)
                .map(|i| {
                    if mask & (1 << i) != 0 {
                        doms[i].hi
                    } else {
                        doms[i].lo
                    }
                })
                .collect();
            if !prop.eval_at(&xs) {
                return SymVerdict::Refuted { witness: xs };
            }
        }
    }
    // Per-variable special values (the rest held at their low bound) — catches interior breakers.
    for i in 0..n {
        let d = doms[i];
        let mid = d.lo.wrapping_add(d.hi.wrapping_sub(d.lo) / 2);
        for &sv in &[d.lo, d.hi, mid, 0, u64::MAX, 1u64 << 63, 1] {
            if !d.contains(sv) {
                continue;
            }
            let mut xs: Vec<u64> = doms.iter().map(|dd| dd.lo).collect();
            xs[i] = sv;
            if !prop.eval_at(&xs) {
                return SymVerdict::Refuted { witness: xs };
            }
        }
    }
    SymVerdict::Unknown
}

/// Prove `prop` over `doms` with **interval refinement** (branch-and-bound). When the plain interval
/// analysis can't decide a domain, this bisects the widest variable and proves each half — the property
/// holds on the whole box iff it holds on both halves, so splitting is sound and recovers the
/// correlation a non-relational interval domain loses. This proves many properties [`prove_forall_n`]
/// returns `Unknown` for (e.g. `(x >> 1) <= x`).
///
/// `max_splits` bounds the total number of bisections (protecting against blow-up); on exhaustion the
/// undecided part is reported honestly as `Unknown`. A `Refuted` anywhere is a real counterexample for
/// the whole domain; `Proven` requires every sub-box to be proven.
/// An empty domain is refused here for the same reason as in [`prove_forall_n`], and with one extra:
/// `refine` picks its split variable by the width `d.hi - d.lo`, which on an inverted interval
/// underflow-**panics** under `debug-assertions` and wraps to a near-`u64::MAX` width in a release
/// build. The engine did not merely answer wrongly on this input, it answered differently by profile.
pub fn prove_forall_refine(doms: &[Iv], prop: &Prop, max_splits: u32) -> SymVerdict {
    if any_empty(doms) {
        return SymVerdict::Unknown;
    }
    let mut budget = max_splits;
    refine(doms, prop, &mut budget)
}

fn refine(doms: &[Iv], prop: &Prop, budget: &mut u32) -> SymVerdict {
    match prop.eval_iv(doms) {
        Tri::True => SymVerdict::Proven,
        Tri::False => {
            let xs: Vec<u64> = doms.iter().map(|d| d.lo).collect();
            if !prop.eval_at(&xs) {
                SymVerdict::Refuted { witness: xs }
            } else {
                probe(doms, prop)
            }
        }
        Tri::Unknown => {
            // Pick the widest splittable variable; if none (all points) the intervals are exact and
            // eval_iv would not have returned Unknown, so fall back to a probe.
            let mut wi: Option<usize> = None;
            let mut wwidth = 0u64;
            for (i, d) in doms.iter().enumerate() {
                let w = d.hi - d.lo;
                if w > 0 && w >= wwidth {
                    wwidth = w;
                    wi = Some(i);
                }
            }
            let i = match wi {
                Some(i) => i,
                None => return probe(doms, prop),
            };
            if *budget == 0 {
                return probe(doms, prop); // out of budget: try to refute, else honest Unknown
            }
            *budget -= 1;
            let d = doms[i];
            let mid = d.lo + (d.hi - d.lo) / 2;
            let mut left = doms.to_vec();
            left[i] = Iv::new(d.lo, mid);
            let mut right = doms.to_vec();
            right[i] = Iv::new(mid + 1, d.hi);
            match refine(&left, prop, budget) {
                SymVerdict::Refuted { witness } => SymVerdict::Refuted { witness },
                SymVerdict::Unknown => match refine(&right, prop, budget) {
                    // left undecided: a refutation on the right is still real; otherwise Unknown.
                    SymVerdict::Refuted { witness } => SymVerdict::Refuted { witness },
                    _ => SymVerdict::Unknown,
                },
                SymVerdict::Proven => refine(&right, prop, budget), // whole = left ∧ right
            }
        }
    }
}

// ── Automatic arithmetic-safety properties ────────────────────────────────────────────────────────
// Kani checks overflow, underflow, and division by zero without being asked, because they follow from
// the language semantics rather than from a property the author stated. `safety::verify_no_panic`
// reaches the same result by execution, but only over a bounded domain and only when the build profile
// has `debug-assertions` on (release builds wrap silently). The functions below answer the same
// question symbolically: over UNBOUNDED domains, and independent of the build profile.

/// An arithmetic fault an expression can exhibit at run time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    /// `a + b` exceeded `u64::MAX`.
    AddOverflow,
    /// `a - b` went below zero.
    SubUnderflow,
    /// `a * b` exceeded `u64::MAX`.
    MulOverflow,
    /// `a << k` shifted bits out, or `k >= 64`.
    ShlOverflow,
    /// `a % 0`.
    DivByZero,
}

impl Expr {
    /// Concrete evaluation with **checked** arithmetic: returns the first fault instead of wrapping.
    ///
    /// [`Expr::eval_at`] deliberately wraps, modelling release-mode Rust. This is its counterpart,
    /// modelling debug-mode Rust, and is what confirms a witness is genuine rather than an artefact of
    /// interval imprecision.
    fn eval_checked(&self, xs: &[u64]) -> Result<u64, Fault> {
        match self {
            Expr::Var(i) => Ok(xs.get(*i as usize).copied().unwrap_or(0)),
            Expr::Const(v) => Ok(*v),
            Expr::Add(a, b) => a
                .eval_checked(xs)?
                .checked_add(b.eval_checked(xs)?)
                .ok_or(Fault::AddOverflow),
            Expr::Sub(a, b) => a
                .eval_checked(xs)?
                .checked_sub(b.eval_checked(xs)?)
                .ok_or(Fault::SubUnderflow),
            Expr::Mul(a, b) => a
                .eval_checked(xs)?
                .checked_mul(b.eval_checked(xs)?)
                .ok_or(Fault::MulOverflow),
            Expr::Shl(a, k) => {
                let v = a.eval_checked(xs)?;
                if *k >= 64 || v > (u64::MAX >> *k) {
                    Err(Fault::ShlOverflow)
                } else {
                    Ok(v << *k)
                }
            }
            // Masked, matching [`Expr::eval_at`] and [`Iv::shr`]. There is no `Fault::ShrOverflow`:
            // this crate models an over-wide RIGHT shift as the wrapping shift its concrete evaluator
            // performs, not as a fault. (`Shl` is deliberately the other way — `Fault::ShlOverflow`
            // documents `k >= 64` as a fault — because losing bits off the top destroys information
            // and is worth reporting, while `x >> 64` under `wrapping_shr` is simply `x`.)
            // Returning 0 here disagreed with `eval_at`, so a witness confirmed through this path
            // was being confirmed against different semantics from the ones the engine reasons in.
            Expr::Shr(a, k) => Ok(a.eval_checked(xs)? >> (*k % 64)),
            Expr::And(a, m) => Ok(a.eval_checked(xs)? & *m),
            Expr::Or(a, m) => Ok(a.eval_checked(xs)? | *m),
            Expr::Rem(a, m) => {
                let v = a.eval_checked(xs)?;
                if *m == 0 {
                    Err(Fault::DivByZero)
                } else {
                    Ok(v % *m)
                }
            }
            // Bitwise ops cannot fault: no operand value overflows, underflows, or divides.
            Expr::AndE(a, b) => Ok(a.eval_checked(xs)? & b.eval_checked(xs)?),
            Expr::OrE(a, b) => Ok(a.eval_checked(xs)? | b.eval_checked(xs)?),
            Expr::XorE(a, b) => Ok(a.eval_checked(xs)? ^ b.eval_checked(xs)?),
            // A variable LEFT shift can lose bits off the top, exactly as `Expr::Shl` can, and is
            // reported as the same fault. Deliberately NOT silently wrapping here: `eval_checked`
            // models debug-mode Rust, where `<<` by >= 64 panics, and a shift that discards
            // information is worth reporting.
            Expr::ShlE(a, b) => {
                let v = a.eval_checked(xs)?;
                let k = b.eval_checked(xs)?;
                if k >= 64 || (k > 0 && v > (u64::MAX >> k)) {
                    Err(Fault::ShlOverflow)
                } else {
                    Ok(v << k)
                }
            }
            // A variable RIGHT shift is masked, matching `Expr::Shr` and `eval_at`. No fault.
            Expr::ShrE(a, b) => {
                let v = a.eval_checked(xs)?;
                let k = b.eval_checked(xs)?;
                Ok(v >> (k % 64))
            }
        }
    }

    /// True when interval reasoning establishes that NO node in this expression can fault over `doms`.
    ///
    /// Sound in the direction that matters: `true` means fault-free for certain (every reachable value
    /// lies within the interval, and the interval endpoints are safe). `false` means "cannot rule it
    /// out", not "faults" — interval analysis loses correlation between variables, so `x - x` is
    /// reported as possibly-underflowing even though it never is.
    fn cannot_fault(&self, doms: &[Iv]) -> bool {
        match self {
            Expr::Var(_) | Expr::Const(_) => true,
            Expr::Add(a, b) => {
                a.cannot_fault(doms)
                    && b.cannot_fault(doms)
                    && a.eval_iv(doms).hi.checked_add(b.eval_iv(doms).hi).is_some()
            }
            Expr::Sub(a, b) => {
                a.cannot_fault(doms)
                    && b.cannot_fault(doms)
                    && a.eval_iv(doms).lo >= b.eval_iv(doms).hi
            }
            Expr::Mul(a, b) => {
                a.cannot_fault(doms)
                    && b.cannot_fault(doms)
                    && a.eval_iv(doms).hi.checked_mul(b.eval_iv(doms).hi).is_some()
            }
            Expr::Shl(a, k) => {
                a.cannot_fault(doms) && *k < 64 && a.eval_iv(doms).hi <= (u64::MAX >> *k)
            }
            Expr::Shr(a, _) | Expr::And(a, _) | Expr::Or(a, _) => a.cannot_fault(doms),
            Expr::Rem(a, m) => a.cannot_fault(doms) && *m != 0,
            // Bitwise ops and the masked right shift never fault themselves, so the answer is
            // entirely about their operands.
            Expr::AndE(a, b) | Expr::OrE(a, b) | Expr::XorE(a, b) | Expr::ShrE(a, b) => {
                a.cannot_fault(doms) && b.cannot_fault(doms)
            }
            // A variable left shift is fault-free only when the shift amount is provably small
            // enough that the value's maximum still fits. `hi >= 64` cannot be ruled out, so any
            // domain reaching 64 answers `false` ("cannot rule it out"), never `true`.
            Expr::ShlE(a, b) => {
                let k = b.eval_iv(doms);
                a.cannot_fault(doms)
                    && b.cannot_fault(doms)
                    && k.hi < 64
                    && a.eval_iv(doms).hi <= (u64::MAX >> k.hi)
            }
        }
    }
}

/// Corner assignments of `doms`: each variable at its low or high endpoint.
///
/// Extremes are where arithmetic faults live, so corners are where a witness is most likely to be
/// found. Capped at `MAX_CORNER_VARS` variables to keep this from becoming exponential; beyond that
/// only the all-low and all-high corners are tried, which can turn a `Refuted` into an honest
/// `Unknown` but never produces a wrong answer.
fn corner_assignments(doms: &[Iv]) -> Vec<Vec<u64>> {
    const MAX_CORNER_VARS: usize = 10;
    let n = doms.len();
    if n == 0 {
        return alloc::vec![Vec::new()];
    }
    if n > MAX_CORNER_VARS {
        return alloc::vec![
            doms.iter().map(|d| d.lo).collect(),
            doms.iter().map(|d| d.hi).collect(),
        ];
    }
    let mut out = Vec::with_capacity(1usize << n);
    for mask in 0u32..(1u32 << n) {
        out.push(
            doms.iter()
                .enumerate()
                .map(|(i, d)| if mask >> i & 1 == 1 { d.hi } else { d.lo })
                .collect(),
        );
    }
    out
}

/// Prove that evaluating `e` **cannot overflow, underflow, or divide by zero** for any assignment in
/// `doms` — symbolically, over unbounded domains, without enumeration.
///
/// This is an automatic property in the model-checking sense: you state no invariant, and the faults
/// come from the arithmetic itself. It is the profile-independent counterpart to
/// [`safety::verify_no_panic`](crate::safety::verify_no_panic), which finds the same faults by
/// execution but only over a bounded domain and only under `debug-assertions`.
///
/// - `Proven` — no assignment in the domain can fault. Sound: established over a superset of the domain.
/// - `Refuted { witness }` — a concrete assignment that genuinely faults, confirmed with checked
///   arithmetic. Never spurious.
/// - `Unknown` — interval reasoning could not rule a fault out and no corner assignment exhibited one.
///   Interval analysis discards correlation between variables, so `x - x` lands here.
///
/// ```
/// use aion_verify::symbolic::{prove_no_overflow, Expr, Iv, SymVerdict};
///
/// // x + 1 over the full u64 domain overflows at x = u64::MAX.
/// let e = Expr::var().add(Expr::c(1));
/// assert!(matches!(prove_no_overflow(&[Iv::full()], &e), SymVerdict::Refuted { .. }));
///
/// // Constrain the domain and the same expression is provably safe.
/// assert_eq!(prove_no_overflow(&[Iv::new(0, 1000)], &e), SymVerdict::Proven);
/// ```
pub fn prove_no_overflow(doms: &[Iv], e: &Expr) -> SymVerdict {
    // Refused rather than answered, as in `prove_forall_n`. `cannot_fault` evaluates intervals, and
    // `Iv::shl` overflow-panics on an inverted one; `corner_assignments` would then offer `d.lo` and
    // `d.hi` as witnesses, neither of which the domain contains.
    if any_empty(doms) {
        return SymVerdict::Unknown;
    }
    if e.cannot_fault(doms) {
        return SymVerdict::Proven;
    }
    // A fault could not be ruled out. Look for a genuine witness at the domain corners before
    // reporting anything -- an unconfirmed "may fault" must never be presented as a refutation.
    for xs in corner_assignments(doms) {
        if e.eval_checked(&xs).is_err() {
            return SymVerdict::Refuted { witness: xs };
        }
    }
    SymVerdict::Unknown
}

/// The specific [`Fault`] an assignment triggers, or `None` if it evaluates cleanly.
///
/// Useful for reporting *why* a [`prove_no_overflow`] witness fails.
pub fn fault_at(e: &Expr, xs: &[u64]) -> Option<Fault> {
    e.eval_checked(xs).err()
}

#[cfg(test)]
mod overflow_tests {
    use super::*;

    #[test]
    fn unbounded_increment_is_refuted_with_a_real_witness() {
        let e = Expr::var().add(Expr::c(1));
        match prove_no_overflow(&[Iv::full()], &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(witness, alloc::vec![u64::MAX]);
                assert_eq!(fault_at(&e, &witness), Some(Fault::AddOverflow));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    #[test]
    fn a_constrained_domain_makes_the_same_expression_provably_safe() {
        let e = Expr::var().add(Expr::c(1));
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, 1000)], &e),
            SymVerdict::Proven
        );
        // Right at the boundary it is still safe: u64::MAX - 1 plus 1 fits exactly.
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, u64::MAX - 1)], &e),
            SymVerdict::Proven
        );
    }

    #[test]
    fn subtraction_underflow_is_found() {
        // x - 5 underflows whenever x < 5.
        let e = Expr::var().sub(Expr::c(5));
        match prove_no_overflow(&[Iv::new(0, 100)], &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(fault_at(&e, &witness), Some(Fault::SubUnderflow));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
        // Constrain x >= 5 and it is safe.
        assert_eq!(
            prove_no_overflow(&[Iv::new(5, 100)], &e),
            SymVerdict::Proven
        );
    }

    #[test]
    fn multiplication_overflow_is_found() {
        let e = Expr::var().mul(Expr::var_at(1));
        let doms = [Iv::new(0, u64::MAX), Iv::new(0, u64::MAX)];
        match prove_no_overflow(&doms, &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(fault_at(&e, &witness), Some(Fault::MulOverflow));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
        // Bounded factors whose product fits are proven safe.
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, 1_000_000), Iv::new(0, 1_000_000)], &e),
            SymVerdict::Proven
        );
    }

    #[test]
    fn division_by_zero_is_found_without_being_asked() {
        let e = Expr::var().rem(0);
        match prove_no_overflow(&[Iv::new(0, 10)], &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(fault_at(&e, &witness), Some(Fault::DivByZero));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, 10)], &Expr::var().rem(7)),
            SymVerdict::Proven
        );
    }

    #[test]
    fn shift_overflow_is_found() {
        let e = Expr::var().shl(60);
        match prove_no_overflow(&[Iv::full()], &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(fault_at(&e, &witness), Some(Fault::ShlOverflow));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
        // Values small enough that 60 bits of headroom remain are safe.
        assert_eq!(prove_no_overflow(&[Iv::new(0, 15)], &e), SymVerdict::Proven);
    }

    #[test]
    fn correlation_loss_yields_an_honest_unknown_not_a_false_refutation() {
        // x - x is always 0 and never underflows, but interval analysis treats the two occurrences as
        // independent and cannot see that. The correct answer is Unknown -- NOT Refuted, since no
        // assignment actually faults, and NOT Proven, since the abstraction cannot establish it.
        let e = Expr::var().sub(Expr::var());
        assert_eq!(
            prove_no_overflow(&[Iv::new(1, 100)], &e),
            SymVerdict::Unknown,
            "imprecision must surface as Unknown, never as a wrong verdict"
        );
        // And the soundness claim is real: no corner assignment actually faults.
        for xs in corner_assignments(&[Iv::new(1, 100)]) {
            assert!(e.eval_checked(&xs).is_ok(), "x - x never faults");
        }
    }

    #[test]
    fn nested_expressions_propagate_faults_from_subterms() {
        // (x * x) + 1: the inner multiplication is the fault, and it must not be masked by the outer add.
        let e = Expr::var().mul(Expr::var()).add(Expr::c(1));
        assert!(matches!(
            prove_no_overflow(&[Iv::full()], &e),
            SymVerdict::Refuted { .. }
        ));
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, 1000)], &e),
            SymVerdict::Proven
        );
    }

    #[test]
    fn masking_operations_never_fault() {
        // And/Or/Shr cannot overflow, so they are provably safe over any domain.
        let e = Expr::var().and(0xFF).or(0x0F).shr(2);
        assert_eq!(prove_no_overflow(&[Iv::full()], &e), SymVerdict::Proven);
    }
}
