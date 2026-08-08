//! AION OS — first-party proof engine (`aion_verify`).
//!
//! Checks a predicate against **every** input in a bounded domain, returning a [`Verdict`] of either
//! `Proven { cases }` (complete coverage — a proof) or `Refuted` **with the counterexample**. Over that
//! domain the guarantee is the real thing: not a sample, the whole space.
//!
//! # Automatic properties — not just the predicate you write
//!
//! A bounded model checker verifies properties nobody stated: index-out-of-bounds, arithmetic
//! overflow, `unwrap` on `None`, division by zero. Two modules cover that here:
//!
//! - [`safety::verify_no_panic`] (needs the `std` feature) runs the code over every input and catches
//!   any unwind. Rust already emits those checks as panics, so exhaustive execution proves none fire.
//! - [`symbolic::prove_no_overflow`] answers the same question symbolically, over unbounded domains
//!   and independent of the build profile — Rust only panics on integer overflow under
//!   `debug-assertions` and wraps silently in release.
//!
//! # What this still is not
//!
//! - **This crate does not read your code — but `aion_vlift` now does.** Tier 4 executes a closure
//!   you pass it, and tier 5 analyses an [`symbolic::Expr`]. Historically that `Expr` was always
//!   built BY HAND, and a model that drifts from the implementation proves things about the model,
//!   not the code — measured, not theorised: six defects induced in `aion_caps` were caught by its
//!   hand-written concrete anchors and by NONE of its hand-written symbolic contracts.
//!
//!   `crates/aion_vlift` closes that for a narrow-but-real subset: it lifts an `Expr` out of
//!   `rustc --emit=mir` (through `aion_vmir`'s CFG), so what the engine proves IS the function body.
//!   It covers unsigned-scalar arithmetic, bitwise ops, comparisons, branching and early returns,
//!   and it REFUSES by name — never silently — everything else (signed integers, floats, structs,
//!   references, calls, loops, projections). The engine itself deliberately keeps no dependency on
//!   it: `aion_verify` stays `no_std` with zero normal dependencies, and the MIR parser lives one
//!   crate away.
//! - **It only covers code that is reached.** Tier 4 covers exactly the paths the enumerated inputs
//!   take, and cannot see a function nobody called.
//!
//! Concrete enumeration also cannot span astronomically large domains (tier 5 exists for that, at the
//! cost of honest `Unknown` answers), and a passing verdict can still be hollow — see
//! [`Verdict::is_vacuous`]. **Kani (tier 5) remains the independent, third-party proof.**
//!
//! `no_std`, `#![forbid(unsafe_code)]`.
#![forbid(unsafe_code)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

/// Tamper-evident SHA-512 hash-chain proof ledger.
pub mod ledger;
/// Merkle (XMSS-style) many-time signatures over WOTS.
pub mod mss;
/// Post-quantum WOTS one-time signatures (hash-based).
pub mod pqsig;
/// Symbolic verification over large/unbounded domains (interval + affine relational + branch-and-bound
/// refinement + inductive invariants) — Phases A–G, the tier-5 companion to the tier-4 enumerator.
pub mod symbolic;

/// Automatic safety checking — panics (index-out-of-bounds, overflow, `unwrap`, division by zero)
/// found without writing a predicate, the way a bounded model checker does. Requires the `std`
/// feature. See [`safety`].
#[cfg(feature = "std")]
pub mod safety;

/// Runtime harvesting of `cases` — the figure a proof produces that its source does not contain, and
/// the one `aion_cover` needs to tell a real proof from a vacuous one. Requires the `std` feature and
/// an environment variable; inert otherwise. See [`harvest`].
#[cfg(feature = "std")]
pub mod harvest;

/// Record a combinator's case count, when harvesting is on. A no-op in every `no_std` build — the
/// kernel-side users of this crate compile this to nothing.
///
/// Deliberately NOT inside the combinators' hot loops: one call per combinator invocation, carrying
/// the total, so an enabled harvest cannot change the cost of a proof by more than a constant.
#[inline]
fn harvested(cases: u64) -> u64 {
    #[cfg(feature = "std")]
    harvest::record(cases);
    cases
}

/// The outcome of a proof attempt over a domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict<T> {
    /// The predicate held for every one of `cases` inputs — a proof over the domain.
    Proven { cases: u64 },
    /// The predicate failed; `counterexample` is the input that broke it, after `checked` passing inputs.
    Refuted { counterexample: T, checked: u64 },
}

impl<T> Verdict<T> {
    /// True when the predicate was never refuted.
    ///
    /// **Caution — this is also true for a vacuous proof.** `Proven { cases: 0 }` means nothing was
    /// ever checked. Prefer [`is_proven_nonvacuous`](Self::is_proven_nonvacuous) in assertions.
    pub fn is_proven(&self) -> bool {
        matches!(self, Verdict::Proven { .. })
    }

    /// True when the verdict is `Proven` but **zero inputs were checked** — a vacuous proof.
    ///
    /// The classic vacuity problem: [`for_all_where`] reports `Proven` when its precondition rejected
    /// every input, so the verdict reads as success while nothing was tested. This is how a proof suite
    /// silently stops proving anything — a precondition drifts out of sync with its domain and the tests
    /// stay green.
    pub fn is_vacuous(&self) -> bool {
        matches!(self, Verdict::Proven { cases: 0 })
    }

    /// [`is_proven`](Self::is_proven) plus the requirement that at least one input actually reached the
    /// predicate. This is what a tier-4 proof should assert on.
    ///
    /// Catches an *empty domain*, not a *trivial predicate*: `|x: i8| x <= 127` is true by the type's
    /// own range and proves nothing, but enumeration cannot tell it apart from a real property. Guard
    /// against that by comparing to an independently computed reference value.
    ///
    /// # It is also blind to a predicate that declines the input itself
    ///
    /// `cases` counts inputs the predicate **returned `true` for**, and an input the predicate walked
    /// away from returns `true` just like one it examined:
    ///
    /// ```ignore
    /// for_all_in(0, 1000, |x| {
    ///     if !interesting(x) { return true; }   // <- counted as a case; nothing was checked
    ///     real_property(x)
    /// })
    /// ```
    ///
    /// The verdict reads `Proven { cases: 1001 }` at any level of `interesting`, including none at
    /// all. No count can distinguish those skips from work — the skip happens on the far side of the
    /// combinator, where the engine cannot see it. That is the same defect as
    /// [`is_vacuous`](Self::is_vacuous) one layer in, and this predicate is structurally unable to
    /// catch it.
    ///
    /// A survey of this workspace counted **31 such early exits across 23 `proofs.rs` files**. They
    /// have since been migrated to the deciding combinators below and **none remain**; the only bare
    /// `return true;` left in any `tests/*.rs` is the deliberate demonstration in `vacuity_proofs.rs`,
    /// which exists to keep measuring the gap. The migration was not bookkeeping — it found that
    /// three proofs were reporting between 17% and 86% of their case counts as skips, and that one
    /// 40,000-case proof would have read `Proven { cases: 40000 }` with its engine proving nothing.
    ///
    /// [`for_all_deciding`] closes it: a predicate returning `Option<bool>` says `None` for an input
    /// it declines, so the skip crosses back into the engine and is counted separately.
    pub fn is_proven_nonvacuous(&self) -> bool {
        matches!(self, Verdict::Proven { cases } if *cases > 0)
    }

    /// Inputs examined (all of them on Proven; the ones that passed before the failure on Refuted).
    pub fn cases(&self) -> u64 {
        match self {
            Verdict::Proven { cases } => *cases,
            Verdict::Refuted { checked, .. } => *checked,
        }
    }
    pub fn counterexample(&self) -> Option<&T> {
        match self {
            Verdict::Refuted { counterexample, .. } => Some(counterexample),
            Verdict::Proven { .. } => None,
        }
    }
}

/// Prove `pred` holds for EVERY item produced by `inputs`. Complete coverage of the domain = a proof.
pub fn for_all<I, T, F>(inputs: I, pred: F) -> Verdict<T>
where
    I: IntoIterator<Item = T>,
    F: Fn(&T) -> bool,
{
    let mut n = 0u64;
    for x in inputs {
        if !pred(&x) {
            return Verdict::Refuted {
                counterexample: x,
                checked: harvested(n),
            };
        }
        n += 1;
    }
    Verdict::Proven {
        cases: harvested(n),
    }
}

/// Like [`for_all`] but only over inputs satisfying `precond` — the equivalent of a `kani::assume` guard.
/// Proves `pred` on every input where the precondition holds.
pub fn for_all_where<I, T, P, F>(inputs: I, precond: P, pred: F) -> Verdict<T>
where
    I: IntoIterator<Item = T>,
    P: Fn(&T) -> bool,
    F: Fn(&T) -> bool,
{
    let mut n = 0u64;
    for x in inputs {
        if !precond(&x) {
            continue;
        }
        if !pred(&x) {
            return Verdict::Refuted {
                counterexample: x,
                checked: harvested(n),
            };
        }
        n += 1;
    }
    // The vacuity case this crate exists to expose — a precondition that rejected every input —
    // records a genuine ZERO here, which is exactly what `aion_cover` must see. Skipping the record
    // when `n == 0` would make a vacuous proof indistinguishable from one that never ran.
    Verdict::Proven {
        cases: harvested(n),
    }
}

/// Exhaustive proof over the entire `u8` domain (all 256 values).
pub fn for_all_u8<F: Fn(u8) -> bool>(pred: F) -> Verdict<u8> {
    for_all(0u8..=255, |&x| pred(x))
}

/// Exhaustive proof over the inclusive range `[lo, hi]`.
pub fn for_all_in<F: Fn(u64) -> bool>(lo: u64, hi: u64, pred: F) -> Verdict<u64> {
    for_all(lo..=hi, |&x| pred(x))
}

/// Exhaustive proof over the cartesian product of two finite domains (binary invariants). Returns the
/// `(a, b)` pair that breaks `pred`, if any.
pub fn for_all_pairs<A: Clone, B: Clone, F: Fn(&A, &B) -> bool>(
    a: &[A],
    b: &[B],
    pred: F,
) -> Verdict<(A, B)> {
    let mut n = 0u64;
    for x in a {
        for y in b {
            if !pred(x, y) {
                return Verdict::Refuted {
                    counterexample: (x.clone(), y.clone()),
                    checked: harvested(n),
                };
            }
            n += 1;
        }
    }
    Verdict::Proven {
        cases: harvested(n),
    }
}

/// The outcome of a proof whose predicate is allowed to **decline** an input.
///
/// See [`for_all_deciding`] for why this type exists. The short version: `Verdict::Proven { cases }`
/// counts inputs the predicate returned `true` for, which includes every input it returned `true` for
/// *without looking at*. Here the two are separate numbers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Deciding<T> {
    /// The verdict over the inputs the predicate actually decided. `cases` is the DECIDED count.
    pub verdict: Verdict<T>,
    /// Inputs the predicate declined by returning `None`. Enumerated, never examined.
    pub skipped: u64,
}

impl<T> Deciding<T> {
    /// Inputs the predicate actually decided (and that held, on a `Proven` verdict).
    pub fn decided(&self) -> u64 {
        self.verdict.cases()
    }

    /// Inputs the predicate declined.
    pub fn skipped(&self) -> u64 {
        self.skipped
    }

    /// Inputs drawn from the domain: decided plus declined.
    ///
    /// On a `Refuted` verdict the refuting input is neither — it is reported as the counterexample —
    /// so this is the count of inputs that came back without a refutation.
    pub fn enumerated(&self) -> u64 {
        self.decided().saturating_add(self.skipped)
    }

    /// True when the predicate was never refuted **and it decided at least one input**.
    ///
    /// This is the assertion [`Verdict::is_proven_nonvacuous`] cannot make: a proof whose predicate
    /// declined every input reports `skipped = n, decided = 0` and is refused here, where the plain
    /// combinator would have reported `Proven { cases: n }` and passed.
    pub fn is_proven_nonvacuous(&self) -> bool {
        self.verdict.is_proven_nonvacuous()
    }

    /// True when the verdict is `Proven` but nothing was decided — every input was declined, or the
    /// domain was empty.
    pub fn is_vacuous(&self) -> bool {
        self.verdict.is_vacuous()
    }

    pub fn is_proven(&self) -> bool {
        self.verdict.is_proven()
    }

    pub fn counterexample(&self) -> Option<&T> {
        self.verdict.counterexample()
    }
}

/// Prove `pred` over every input it is willing to DECIDE, and count the ones it declines.
///
/// `pred` returns `Some(true)` (held), `Some(false)` (refuted, with this input as the counterexample)
/// or `None` (declined — out of scope for this property).
///
/// # The hole this closes
///
/// [`for_all_where`] takes the precondition as a separate closure, so the engine sees the filtering
/// and records a genuine zero when it admits nothing. A predicate that filters *internally* —
///
/// ```ignore
/// for_all(inputs, |x| {
///     let Some(parsed) = parse(x) else { return true };   // declined, counted as a case
///     parsed.is_canonical()
/// })
/// ```
///
/// — hides the filtering behind a `true`, and no `cases` figure can recover it. The proof reads as
/// healthy at any skip rate, up to and including 100%, and [`Verdict::is_proven_nonvacuous`] is
/// structurally blind to it: the skip and the pass are the same value by the time the engine sees
/// them. This is not hypothetical — 31 such early exits sat across 23 `proofs.rs` files in this
/// workspace, since migrated to this combinator and its two siblings. Measured on the way through:
/// `aion_verify`'s own A10 reported 40,000 cases and had decided 5,467 of them.
///
/// Written as `Option<bool>`, the decline crosses back into the engine and becomes a number.
///
/// The **harvest records the decided count, not the enumerated one**, so `aion_cover` sees the honest
/// figure: a proof that declined everything confers no coverage, which is exactly what it earned.
///
/// ```
/// use aion_verify::for_all_deciding;
///
/// // Only even inputs are in scope for this property.
/// let d = for_all_deciding(0u64..=99, |&x| (x % 2 == 0).then(|| x % 2 == 0));
/// assert!(d.is_proven_nonvacuous());
/// assert_eq!(d.decided(), 50);
/// assert_eq!(d.skipped(), 50);
///
/// // A predicate that declines EVERYTHING is refused, where a bare `return true` would have passed.
/// let empty = for_all_deciding(0u64..=99, |_| None::<bool>);
/// assert!(empty.is_vacuous());
/// assert!(!empty.is_proven_nonvacuous());
/// assert_eq!(empty.skipped(), 100);
/// ```
pub fn for_all_deciding<I, T, F>(inputs: I, pred: F) -> Deciding<T>
where
    I: IntoIterator<Item = T>,
    F: Fn(&T) -> Option<bool>,
{
    let mut decided = 0u64;
    let mut skipped = 0u64;
    for x in inputs {
        match pred(&x) {
            Some(true) => decided += 1,
            None => skipped += 1,
            Some(false) => {
                return Deciding {
                    verdict: Verdict::Refuted {
                        counterexample: x,
                        checked: harvested(decided),
                    },
                    skipped,
                }
            }
        }
    }
    // The DECIDED count is harvested, deliberately: `aion_cover` asks "did this proof examine
    // anything", and a declined input is the exact case where the answer is no.
    Deciding {
        verdict: Verdict::Proven {
            cases: harvested(decided),
        },
        skipped,
    }
}

/// [`for_all_deciding`] over the inclusive range `[lo, hi]` — the deciding form of [`for_all_in`].
///
/// Exists so migrating a proof off a bare `return true;` is a change of two tokens rather than a
/// change of shape. `for_all_in` is the combinator 22 of this workspace's 31 internal early exits sit
/// inside, and a migration that also has to restructure the domain expression is one that gets
/// deferred.
///
/// ```
/// use aion_verify::for_all_in_deciding;
///
/// // Only multiples of three are in scope; the other two thirds are declined, not passed.
/// let d = for_all_in_deciding(0, 29, |x| (x % 3 == 0).then_some(x % 3 == 0));
/// assert!(d.is_proven_nonvacuous());
/// assert_eq!((d.decided(), d.skipped(), d.enumerated()), (10, 20, 30));
/// ```
pub fn for_all_in_deciding<F: Fn(u64) -> Option<bool>>(lo: u64, hi: u64, pred: F) -> Deciding<u64> {
    for_all_deciding(lo..=hi, |&x| pred(x))
}

/// [`for_all_deciding`] over the cartesian product of two finite domains — the deciding form of
/// [`for_all_pairs`].
///
/// The pair combinator needs its own deciding form for a reason beyond convenience: a pair proof's
/// most common early exit is the DIAGONAL (`if a == b { return true; }`) or an ordering guard
/// (`if i >= j { return true; }`), which declines between a half and all-but-`n` of the product. Those
/// are the skips most likely to be mistaken for work, because the enumerated figure — `n²` — looks
/// impressive while the decided figure may be a fraction of it.
///
/// ```
/// use aion_verify::for_all_pairs_deciding;
///
/// let xs = [0u32, 1, 2, 3];
/// // Only ordered pairs say anything; the diagonal and the reverse are declined.
/// let d = for_all_pairs_deciding(&xs, &xs, |&a, &b| (a < b).then(|| a < b));
/// assert_eq!((d.decided(), d.skipped(), d.enumerated()), (6, 10, 16));
/// assert!(d.is_proven_nonvacuous());
/// ```
pub fn for_all_pairs_deciding<A: Clone, B: Clone, F: Fn(&A, &B) -> Option<bool>>(
    a: &[A],
    b: &[B],
    pred: F,
) -> Deciding<(A, B)> {
    let mut decided = 0u64;
    let mut skipped = 0u64;
    for x in a {
        for y in b {
            match pred(x, y) {
                Some(true) => decided += 1,
                None => skipped += 1,
                Some(false) => {
                    return Deciding {
                        verdict: Verdict::Refuted {
                            counterexample: (x.clone(), y.clone()),
                            checked: harvested(decided),
                        },
                        skipped,
                    }
                }
            }
        }
    }
    Deciding {
        verdict: Verdict::Proven {
            cases: harvested(decided),
        },
        skipped,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn for_all_proves_a_true_predicate_over_the_whole_domain() {
        let v = for_all_u8(|x| (x as u16) + 1 > x as u16);
        assert!(v.is_proven());
        assert_eq!(v.cases(), 256, "every u8 checked — a proof, not a sample");
    }

    #[test]
    fn for_all_refutes_and_returns_the_counterexample() {
        let v = for_all_u8(|x| x < 200);
        assert!(!v.is_proven());
        assert_eq!(v.counterexample(), Some(&200u8));
        assert_eq!(
            v.cases(),
            200,
            "200 values passed before the counterexample"
        );
    }

    #[test]
    fn for_all_where_applies_a_precondition() {
        let v = for_all_where(0u16..=255, |x| x % 2 == 0, |x| (x * 2) % 2 == 0);
        assert!(v.is_proven());
        assert_eq!(v.cases(), 128, "only the 128 even values were in scope");
    }

    #[test]
    fn for_all_in_covers_a_bounded_range() {
        let v = for_all_in(10, 20, |x| (10..=20).contains(&x));
        assert!(v.is_proven());
        assert_eq!(v.cases(), 11);
    }

    #[test]
    fn for_all_pairs_covers_the_product_and_finds_a_bad_pair() {
        let a = [1u32, 2, 3];
        let b = [10u32, 20];
        let good = for_all_pairs(&a, &b, |&x, &y| x + y == y + x);
        assert!(good.is_proven());
        assert_eq!(good.cases(), 6, "3 x 2 pairs all checked");
        let bad = for_all_pairs(&a, &b, |&x, &y| x + y != 12);
        assert_eq!(
            bad.counterexample(),
            Some(&(2u32, 10u32)),
            "2+10==12 breaks it"
        );
    }
}

// ── TIER 5 — third-party formal confirmation (Kani) ──────────────────────────────────────────────────
#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// Independent confirmation: for any bound b <= 16, for_all_in(0, b, |x| x <= b) is Proven and checks
    /// exactly b+1 cases. Kani proves it SYMBOLICALLY — every b in 0..=16 over all execution paths at once,
    /// confirming our enumerating engine's own claim about itself. Bounded to 16 (with a matching unwind so
    /// CBMC fully unwinds the enumeration loop and terminates); the tier-4 test already exercises the full
    /// 0..=255 range concretely, so this adds symbolic assurance on top rather than replacing it.
    #[kani::proof]
    #[kani::unwind(18)]
    fn for_all_in_is_sound() {
        let b: u64 = kani::any();
        kani::assume(b <= 16);
        let v = for_all_in(0, b, |x| x <= b);
        assert!(v.is_proven());
        assert!(v.cases() == b + 1);
    }
}
