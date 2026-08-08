# Changelog

## 3.9.0

**Supersedes 3.8.0, which was published and later found defective by our own internal proofs.**
3.8.0 has not been yanked and remains usable for everything outside the `ledger` module.

### Fixed — soundness defect in `ledger` (present in 3.8.0 and earlier)

`Ledger::record` encoded `(label, proven)` as `label ‖ 0x00 ‖ flag` — a NUL-terminated label. A Rust
`&str` may contain U+0000, so any reader recovering the pair cut at the **first** terminator and took
a byte out of the middle of the label as the flag:

```text
record("aion_storage::nothing_spins\0\x01", proven = FALSE)
  reads back as ("aion_storage::nothing_spins", proven = TRUE)
```

**A refutation read back as a proof**, and `record("x\0\0", true)` read back as refuted — the
corruption ran both ways, and the safe direction was not the default. For a verification engine this
is the most serious class of defect there is.

Nothing detected it, and the hash chain is why it looked fine: `verify()` confirms the stored bytes
are the bytes that were written, and they were. The chain protected the *transport* of a record whose
*meaning* was destroyed at the moment of writing. The one existing check compared hashes —
injectivity, not readability — and two payloads can hash differently while both decode to the same
wrong flag.

The root cause is that the format **had no reader at all**; a format nothing reads is never forced to
be readable.

- Payload is now `flag ‖ label`: flag first at a fixed offset, label the entire remainder. Both halves
  recoverable for every label, no scan, no terminator.
- **New: `Ledger::read_record`** — the format now has a reader in the same crate as its writer. It
  returns `None` for an empty payload or a flag byte outside `{0, 1}` rather than guessing, because a
  payload from `append` is arbitrary bytes and is not a proof record.

### Fixed — the tests proving the engine's best claim were never shipped

3.8.0's test suite *does* compile and pass for a downloader (76 of 76). The defect is what it omits:
the two tests where the engine proves **another crate's** invariants reasoned about a private crate
reached as a `path` dev-dependency, and `cargo publish` strips path-only dev-dependencies. So the
tests demonstrating the entire point of the engine were exactly the ones nobody outside could run.

- **New companion crate [`aion_verify_subject`](https://crates.io/crates/aion_verify_subject) 1.0.0**
  — a small access-control domain with zero dependencies, including **no dependency on
  `aion_verify`**. `tests/connection.rs` and `tests/grouping.rs` now depend on it **by version**, so
  they ship and run for everybody: **79 of 79 tests pass from the unpacked `.crate` artifact**.

### Added

- Bitwise and shift transfer functions in the interval domain: `Expr::and_e`, `or_e`, `xor_e`,
  `shl_e`, `shr_e`, and a precise `>>` rule. `(x >> 1) <= x` over all 2^64 values of `u64` is now
  decided by the plain interval domain, where 3.8.0 returned `Unknown`.
- `src/harvest.rs` (behind the `std` feature): runtime harvesting of the `cases` figure a proof
  produces, which its source does not contain.

### Changed

- The `safety` module now measures the half of itself it previously did not.
- Three symbolic tests were **re-aimed, not relaxed.** They asserted `Unknown` for `(x >> 1) <= x`,
  which the improved shift rules now decide. Left alone they would have gone red; edited to expect
  `Proven` they would have stopped testing soundness. They now state the same claims about
  `x * x >= x` over `[0, 1000]` — true everywhere in the domain, and genuinely undecidable by a
  non-relational domain. The old property is kept as its own test so the improvement is pinned.
- The crate description now states plainly that **tier 5 is this crate**, via `symbolic`, and that it
  is **sound but incomplete**: `Proven`, `Refuted` with a concrete witness, or an honest `Unknown`,
  never a false `Proven` or `Refuted`. An SMT-based checker such as Kani/CBMC decides cases this
  returns `Unknown` on, so Kani remains a stronger independent second opinion rather than something
  this replaces.

## 3.8.0

Automatic safety properties: find faults nobody wrote a predicate for.

## 3.7.1

Correct an overstated claim in the crate docs.

## 3.7.0

Vacuity detection (`Verdict::is_vacuous`, `is_proven_nonvacuous`) — a `Proven { cases: 0 }` reads as
success but proves nothing. Repository moved to `NubbyNubkins`.

## 3.6.0

Phase G: assume-narrowing — inductive invariants over unbounded state.

## 3.5.0

Phase F: inductive invariants — reasoning about loops and state, not just values.
