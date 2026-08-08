<!--
  WHY THIS FILE DIFFERS FROM THE COPY IN THE AION OS WORKSPACE — read before "reconciling" it.

  `aion_verify` exists in two places: the copy inside the private AION OS workspace, and this one,
  which is published to crates.io. `src/**` is IDENTICAL between them modulo rustfmt — verified by
  formatting both with `rustfmt --edition 2021` and diffing, which produces byte-identical files.
  (The published crate's CI gates on `cargo fmt --all --check`; the workspace does not, so the two
  differ in whitespace and in nothing else. A drift check should compare formatted forms.)

  This README does NOT match the in-workspace one, on purpose. That one is a short internal note for
  people who already have the whole workspace in front of them. This one is the crate's front page on
  crates.io and docs.rs: it has to explain the engine to somebody who has never seen AION, be honest
  about what the engine cannot do, and say where Kani is still the better tool. Replacing it with the
  internal note would be a regression for every downloader, so the divergence is deliberate and this
  comment is the record of it.

  `tests/connection.rs` and `tests/grouping.rs` also differ deliberately; the reason is written at the
  top of each of those files.
-->

# aion_verify

[![crates.io](https://img.shields.io/crates/v/aion_verify.svg)](https://crates.io/crates/aion_verify)
[![docs.rs](https://docs.rs/aion_verify/badge.svg)](https://docs.rs/aion_verify)
[![license](https://img.shields.io/crates/l/aion_verify.svg)](#license)

**An exhaustive bounded proof engine for Rust.** Check a predicate against **every** input in a
finite or bounded domain and get back either a proof (`Proven { cases }` — complete coverage) or the
**exact counterexample** that broke it (`Refuted`). Not a random sample — the whole space.

- **`no_std`**, **zero dependencies**, `#![forbid(unsafe_code)]`.
- A real *proof* over the domain, not property-based fuzzing: if it says `Proven`, every input was checked.
- Returns the counterexample on failure, so a red result is immediately actionable.

> ## ⚠️ 3.9.0 fixes a soundness defect in 3.8.0 — upgrade if you use the `ledger` module
>
> **3.8.0 is live on crates.io and carries a defect our own internal proofs found after it was
> published.** A crate whose entire claim is that it tells you the truth about code cannot be vague
> about its own bugs, so here it is in full. See [What 3.9.0 fixes](#what-390-fixes-and-what-38-0-got-wrong).

## Why

Property-based testing (proptest, quickcheck) *samples* an input space and can miss the one value that
breaks your invariant. Symbolic model checkers (like [Kani](https://github.com/model-checking/kani))
prove properties over astronomically large spaces with a SAT/SMT backend, but need a toolchain and can
be slow. For the very common case of a **finite or small bounded** domain — every `u8`, a range, a
cartesian product of a few slices — you can just check *all of it*, fast, in plain safe Rust. That's
`aion_verify`.

It was built as the tier-4 engine of the AION OS verification stack, alongside Kani as the independent
tier-5 formal check. It complements Kani; it does not replace it.

## What 3.9.0 fixes, and what 3.8.0 got wrong

3.8.0 was published, then found defective by our own internal proofs, and is superseded by 3.9.0. It
has not been yanked and still works for everything outside the `ledger` module. Both problems below
were caught by AION's own verification work after release — which is, if nothing else, the engine
doing the job it exists for.

### 1. A soundness defect in `ledger`: a refutation could read back as a proof

**This is the most serious class of bug a verification tool can have.** In 3.8.0, `Ledger::record`
encoded the pair `(label, proven)` as `label ‖ 0x00 ‖ flag` — a NUL-terminated label. But `label` is
an arbitrary `&str`, and **a Rust `&str` may contain U+0000.** Any reader recovering the pair can
only cut at the *first* terminator, so a label with an embedded NUL made the reader take a byte out
of the middle of the label and treat it as the flag:

```text
  3.8.0:  record("aion_storage::nothing_spins\0\x01", proven = FALSE)
          reads back as ("aion_storage::nothing_spins", proven = TRUE)
```

A **refutation read back as a proof** — and `record("x\0\0", true)` read back as refuted, so the
corruption ran in both directions and the safe direction was not the default.

**Nothing detected it, and the hash chain is why it looked fine.** `Ledger::verify()` confirms the
stored bytes are the bytes that were written, and they were: no tampering occurred. The chain
protected the *transport* of a record whose *meaning* was destroyed at the moment of writing. A
tamper-evident log of unreadable records only proves that an unreadable thing was faithfully
preserved.

The one check that existed compared **hashes** — `record(l, true)` hashing differently from
`record(l, false)`. That is *injectivity*, not *readability*: two payloads can hash differently while
both decode to the same wrong flag, which is exactly what happened.

The deeper cause is a format that **had no reader at all**. The writer and the meaning of its bytes
were joined only by prose, and a format nothing reads is never forced to be readable.

**Fixed in 3.9.0.** The payload is now `flag ‖ label` — flag first at a fixed offset, label the
entire remainder. Both halves are recoverable for *every* label, with no scan and no terminator. And
`Ledger::read_record` now exists, so **the format has a reader in the same crate as its writer**,
with `tests/ledger_proofs.rs` pinning the round trip. `read_record` returns `None` for a flag byte
outside `{0, 1}` rather than guessing, because a payload from `append` is arbitrary bytes and is not
a proof record.

### 2. The tests that prove the engine's best claim were never shipped

To be precise, because the sloppy version of this claim is wrong: **3.8.0's test suite does compile
and pass for a downloader — 76 of 76.** The problem is what it does *not* contain.

The two tests where the engine proves **another crate's** invariants — the whole point of a proof
engine — reasoned about a private crate reached as a **`path` dev-dependency**. `cargo publish`
strips path-only dev-dependencies, so those two files could never be shipped in a form anyone could
compile. Every published version to date therefore demonstrated the engine only against itself, and
an engine checking a predicate it also defined proves only that it agrees with itself.

**Fixed in 3.9.0** by publishing the subject: see
[Proving *another crate's* invariants](#proving-another-crates-invariants--and-running-that-proof-yourself).
`tests/connection.rs` and `tests/grouping.rs` now ship, resolve, and run for everybody — **79 of 79
tests pass from the unpacked `.crate` artifact**, in a directory with no sibling paths to fall back
on.

### 3. Also in 3.9.0

- **The interval domain gains bitwise and shift transfer functions** (`and_e`, `or_e`, `xor_e`,
  `shl_e`, `shr_e`, plus precise `>>` on intervals). `(x >> 1) <= x` over all 2^64 values of `u64` is
  now decided outright by the plain interval domain, where 3.8.0 returned `Unknown`.
- **The `safety` module now measures the half of itself it previously did not.**
- Three symbolic tests were **re-aimed, not relaxed**: they used to assert `Unknown` for the shift
  property above. Left alone they would have gone red; edited to expect `Proven` they would have
  stopped testing soundness at all. They now state the same claims about `x * x >= x` over
  `[0, 1000]` — true everywhere in the domain, and genuinely undecidable by a non-relational domain,
  which treats the two occurrences of `x` as independent. The old property is kept as a test in its
  own right so the improvement is pinned rather than lost.

## Example

```rust
use aion_verify::{for_all_u8, for_all_in, for_all_pairs};

// Prove a property over the entire u8 domain (all 256 values):
let v = for_all_u8(|x| (x as u16) + 1 > x as u16);
assert!(v.is_proven());
assert_eq!(v.cases(), 256); // every input checked — a proof

// A failing property hands you the counterexample:
let v = for_all_u8(|x| x < 200);
assert_eq!(v.counterexample(), Some(&200u8));

// Bounded ranges and cartesian products of finite domains:
let v = for_all_in(0, 1000, |x| x * 2 >= x);
assert!(v.is_proven());

let a = [1u32, 2, 3];
let b = [10u32, 20];
let v = for_all_pairs(&a, &b, |&x, &y| x + y == y + x);
assert!(v.is_proven());
```

## API

| Combinator | Domain |
| --- | --- |
| `for_all(iter, pred)` | every item of any finite iterator |
| `for_all_where(iter, precond, pred)` | items satisfying a precondition (like a `kani::assume` guard) |
| `for_all_u8(pred)` | the full `u8` domain (256 values) |
| `for_all_in(lo, hi, pred)` | the inclusive range `[lo, hi]` |
| `for_all_pairs(&a, &b, pred)` | the cartesian product `a × b` (binary invariants) |

Each returns a `Verdict<T>`: `is_proven()`, `cases()`, and `counterexample() -> Option<&T>`.

### Vacuity — when a passing proof proves nothing

A proof over an empty domain trivially succeeds. If `for_all_where`'s precondition rejects every
input, the verdict is `Proven { cases: 0 }`: nothing was tested, yet `is_proven()` returns `true`.
This is the most common way a proof suite quietly stops proving anything — a precondition drifts out
of sync with the domain, and the tests stay green.

```rust
use aion_verify::for_all_where;

let hi = core::hint::black_box(100u8);
// No u8 is both > 200 and < 100, so the predicate below is never even reached.
let v = for_all_where(0u8..=255, |&x| x > 200 && x < hi, |_| false);

assert!(v.is_proven());            // reads as success
assert!(v.is_vacuous());           // but nothing was checked
assert!(!v.is_proven_nonvacuous()); // the assertion you actually want
```

Prefer **`is_proven_nonvacuous()`** in test assertions. It is `is_proven()` plus the requirement that
at least one input reached the predicate.

One caveat, stated plainly: this catches an *empty domain*, not a *trivial predicate*. A predicate
like `|x: i8| x <= 127` is true by the type's own range and proves nothing about the code under test,
but it is indistinguishable from a hard-won property by enumeration alone. Guard against that by
comparing against an independently computed reference value, or by checking that the proof fails when
you deliberately mutate the implementation.

## Automatic safety — properties you never wrote a predicate for

A bounded model checker verifies things you never stated: index-out-of-bounds, arithmetic overflow,
`unwrap` on `None`, division by zero. Those come from the language, not from an assertion the author
made. Two routes here cover that ground.

**By execution** (needs the `std` feature) — Rust already emits those checks as runtime panics, so
running every input in the domain and catching the unwind proves none of them can fire:

```rust
use aion_verify::safety::verify_no_panic;

let table = [10u32, 20, 30];
// No predicate written. The out-of-bounds index is found anyway.
let s = verify_no_panic(0usize..=3, |&i| { let _ = table[i]; });

assert!(s.panicked());
assert_eq!(s.failing_input(), Some(&3));
assert!(s.message().unwrap().contains("index out of bounds"));
```

`for_all_safe` combines this with a predicate, and distinguishes "the code crashed" from "the
invariant is false" — collapsing those would hide a latent crash inside an ordinary refutation.

**Symbolically** — over *unbounded* domains, and independent of the build profile. This matters:
Rust only panics on integer overflow under `debug-assertions` and wraps silently in release, so the
execution route above cannot answer the question for a release build.

```rust
use aion_verify::symbolic::{prove_no_overflow, Expr, Iv, SymVerdict};

// x + 1 over the full u64 domain overflows at x = u64::MAX -- with a confirmed witness.
let e = Expr::var().add(Expr::c(1));
assert!(matches!(prove_no_overflow(&[Iv::full()], &e), SymVerdict::Refuted { .. }));

// Constrain the domain and the same expression is provably safe.
assert_eq!(prove_no_overflow(&[Iv::new(0, 1000)], &e), SymVerdict::Proven);
```

A `Refuted` is always backed by an assignment confirmed with checked arithmetic, never by interval
imprecision alone. Where the abstraction loses correlation between variables — `x - x` is the
canonical case — the answer is an honest `Unknown`, never a wrong verdict.

### Requirements

The `safety` module needs `features = ["std"]` and an unwinding panic profile (`panic = "abort"`
leaves nothing to catch). It raises the crate MSRV to **1.81** when enabled. The crate is `no_std`
with zero dependencies by default, unchanged.

## Proving *another crate's* invariants — and running that proof yourself

The claim worth testing about a proof engine is not that it agrees with itself. It is that you can
point it at ordinary code, written without it in mind, and have it establish — or refute, *with a
witness* — that code's invariants over the whole of a finite domain.

`tests/connection.rs` and `tests/grouping.rs` do exactly that, against
**[`aion_verify_subject`](https://crates.io/crates/aion_verify_subject)**: a tiny published
access-control domain (badges, roles, clearances, wings, revocation) that has **zero dependencies —
including no dependency on `aion_verify`**. The arrow runs one way only.

```console
cargo test --test connection --test grouping
```

Four invariants, each by complete coverage rather than sampling:

| Invariant | Domain | Cases |
| --- | --- | --- |
| A role granted exactly one clearance holds that one **and no other** | `Clearance::ALL` | 10 |
| Covering one wing never covers another | `Wing × Wing` | 144 |
| A revoked badge holds **no** clearance | `Clearance::ALL` | 10 |
| A badge never issued holds nothing | `Clearance::ALL` | 10 |

The first one is the one worth dwelling on. The obvious authorization test — *grant `c`, assert the
holder may do `c`* — **cannot fail in the direction that matters**, because it never looks at what
leaked. The proof here ranges over the whole `Clearance` domain and asserts
`may(badge, x) == (x == granted)` for every `x`.

> **Before 3.9.0 these two tests existed but could not be published.** Their subject was a private
> crate reached as a `path` dev-dependency, and `cargo publish` strips path-only dev-dependencies —
> so the two tests that demonstrate the entire point of the engine were exactly the two nobody
> outside could compile. `aion_verify_subject` is the fix: published separately, depended on **by
> version**, resolvable by everybody.

## What this still is not

Two real gaps remain against a compiler-driven checker like Kani:

- **It does not read your code.** Kani compiles actual Rust MIR. Tier 4 here executes a closure you
  pass it; tier 5 analyses an `Expr` you build by hand. A model that drifts from the implementation
  proves things about the model, not the code.
- **It only covers code that is reached.** Tier 4 covers exactly the paths the enumerated inputs
  take, and cannot see a function nobody called.

It complements Kani; it does not replace it.

## Tier 5 — symbolic proofs over *unbounded* domains (`symbolic` module)

**Tier 5 is this crate, not a different one.** It is worth being exact about what that does and does
not mean, because "we do tier 5 too" is the kind of claim that quietly stops being true:

- `symbolic` proves properties over **unbounded** integer domains — all 2^64 values of a `u64`, over
  any number of variables — without enumerating them.
- It is **sound but incomplete**. Every transfer function over-approximates, so the answer is
  `Proven`, `Refuted` *with a concrete witness*, or an honest **`Unknown`** when the abstraction is
  too imprecise to decide. It never returns a false `Proven` and never a false `Refuted`.
- `Unknown` is not rare or hypothetical: relational and correlated properties — where the same
  variable appears more than once, so the interval domain loses the correlation between its
  occurrences — routinely land there. Branch-and-bound refinement and the affine layer recover many
  of them; not all.
- **An SMT-based checker such as Kani/CBMC decides cases this returns `Unknown` on.** That is the
  honest summary of the relationship: Kani is a *stronger independent second opinion*, not something
  this replaces.

Tier 4 enumerates, so it needs a finite domain. Tier 5 proves properties over the **entire** domain —
including all 2^64 values of `u64` — **without enumerating it**, by interval abstract interpretation.
Because it must *reason about* an expression (not just call it), tier-5 predicates use a small
first-party `Expr`/`Prop` DSL:

```rust
use aion_verify::symbolic::{prove_forall, Expr, Iv, Prop, SymVerdict};

// Prove `(x & 0xFF) <= 255` for EVERY u64 — symbolically, no enumeration:
let p = Prop::Le(Expr::var().and(0xFF), Expr::c(255));
assert_eq!(prove_forall(Iv::full(), &p), SymVerdict::Proven);

// A false property comes back with a concrete witness:
let q = Prop::Le(Expr::var(), Expr::c(100));
matches!(prove_forall(Iv::full(), &q), SymVerdict::Refuted { .. });
```

**Multiple variables and function contracts.** Variables are addressed by index (`Expr::var_at(i)`),
and `prove_contract(&doms, &precond, &postcond)` proves `precond -> postcond` over the variables'
domains — the core of verifying a function or component (validate inputs, guarantee the postcondition):

```rust
use aion_verify::symbolic::{prove_contract, Expr, Iv, Prop, SymVerdict};

// Contract over x ∈ [0,1000]: if x <= 1000 then x + 1 <= 1001.
let pre  = Prop::Le(Expr::var(), Expr::c(1000));
let post = Prop::Le(Expr::var().add(Expr::c(1)), Expr::c(1001));
assert_eq!(prove_contract(&[Iv::new(0, 1000)], &pre, &post), SymVerdict::Proven);
```

`SymVerdict` is `Proven` (holds for all), `Refuted { witness }` (a real counterexample — a value per
variable), or `Unknown`
(the interval abstraction was too weak) — **never a false Proven or Refuted**. Pure Rust, no external
solver.

**Correlated properties via refinement.** A plain interval domain is non-relational, so it returns
`Unknown` on properties that couple a variable to itself (e.g. `(x >> 1) <= x`). `prove_forall_refine`
recovers these with **branch-and-bound**: when a box is undecided it bisects the widest variable and
proves each half (the property holds on the whole iff it holds on both), up to a split budget — still
sound, and `Unknown` if the budget runs out.

```rust
use aion_verify::symbolic::{prove_forall_refine, Expr, Iv, Prop, SymVerdict};
let p = Prop::Le(Expr::var().shr(1), Expr::var());          // correlated, true for all u64
assert_eq!(prove_forall_refine(&[Iv::full()], &p, 256), SymVerdict::Proven);
```

**Loops & state via inductive invariants.** Everything above reasons about *values*. `prove_inductive`
reasons about a *loop*: it proves a property holds on **every** iteration by induction — **initiation**
(it holds in the initial states) plus **consecution** (if it holds and the guard is true, it still holds
after one transition) — with no unrolling. Consecution uses **assume-narrowing**: the invariant and guard
are assumed by shrinking the state box first, so the proof lands over **unbounded** state (the whole
`u64` range) with no splitting. A non-inductive invariant is refuted with the concrete state that breaks it.

```rust
use aion_verify::symbolic::{prove_inductive, Expr, Iv, Prop, SymVerdict};
// A counter starting at 5 that only increments: prove `i >= 5` on every iteration, over ALL of u64.
let init = &[Iv::new(5, 5)];
let guard = Prop::Le(Expr::var(), Expr::c(1_000_000_000));   // loop while i <= 1e9
let step = &[Expr::var().add(Expr::c(1))];                   // i' = i + 1
let inv = Prop::Ge(Expr::var(), Expr::c(5));                 // i >= 5
assert_eq!(prove_inductive(init, &guard, step, &inv, &[Iv::full()], 8), SymVerdict::Proven);
```

## Tamper-evident proof ledger (`ledger` module)

A proof is only trustworthy if its result can't be quietly forged or deleted. `ledger` records each
verdict in a **hash chain** (with a self-contained pure-Rust **SHA-512**): every entry carries the hash
of the one before it, so altering *any* past record — or deleting one — changes every hash after it and
is caught by `verify()`.

```rust
use aion_verify::ledger::Ledger;
use aion_verify::pqsig::{keygen, sign, verify};

let mut log = Ledger::new();
log.record("x + 1 > x over u8", true);   // a proven result
log.record("x <= 100 over u64", false);  // a refuted result, recorded just the same
let head = log.head();                   // 64-byte fingerprint of the whole history
assert_eq!(log.verify(), Ok(()));        // an untampered chain verifies

// Sign the head with a POST-QUANTUM (hash-based WOTS) signature so the log is provably yours:
let seed = [7u8; 64];                    // one-time secret; never reuse
let public_key = keygen(&seed);          // publish this as the anchor
let seal = sign(&seed, &head);
assert!(verify(&public_key, &head, &seal));
```

Persist the entries, reload with `Ledger::from_entries(..)`, and `verify()` again to detect any on-disk
tampering. Publish the public key + signed head; a later divergence is proof the log was cut or rewritten.

**Post-quantum.** The whole scheme rests only on SHA-512 — hashes are quantum-resistant (Grover is just a
quadratic speedup, and SHA-512 keeps a full 256-bit collision margin), and the signature is hash-based
(WOTS), so nothing here falls to Shor's algorithm. No RSA/ECC anywhere. It's a blockchain's core guarantee
(an immutable, verifiable, *signed* history) without the distributed-consensus machinery a single
authority doesn't need. (WOTS is one-time per key — lift to many-time with XMSS/SPHINCS+ over the same
primitive.)

## When to reach for something else

Linear relational facts (a variable compared against a linear combination of itself and others, like
`x <= x + y`) are proven directly by an **affine layer** that cancels shared terms — no splitting, sound
under u64 wrapping (it only applies where the operands provably can't overflow). Beyond that, refinement
is bounded by its split budget, and neither it nor the interval domain handles arbitrary
non-linear or unbounded-arity logic. For those, a mature symbolic tool such as
[Kani](https://github.com/model-checking/kani) remains a good complement while this engine's decision
procedures grow.

## License

Licensed under the **[Mozilla Public License 2.0](LICENSE)** (MPL-2.0) — a file-level copyleft.

In plain terms: you can use `aion_verify` in any project, including proprietary ones, **but any
modifications you make to its source files must themselves be released under the MPL-2.0** (i.e. kept
open source). Improvements to the engine stay free for everyone; the wider project you build around it
does not have to be. Contributions submitted for inclusion are licensed under the same terms.

> Note: `0.1.0` was briefly published under MIT/Apache-2.0 and has been yanked; `0.2.0` onward is MPL-2.0.
