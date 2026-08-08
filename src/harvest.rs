//! Case-count harvesting — the one number a proof produces that its source code does not contain.
//!
//! # The gap this closes
//!
//! [`Verdict::Proven { cases }`](crate::Verdict) carries how many inputs a proof actually examined,
//! and `aion_cover::Proof::is_evidence()` is false when that figure is zero. A proof whose
//! precondition rejected every input reports `Proven` and covers nothing — the vacuity defect this
//! workspace has been bitten by more than once. But `cases` exists **only at runtime**: it is not in
//! the source, `cargo test` prints only `ok`, and there is no static way to recover it.
//!
//! So `aion_cover` could not be run across this tree at all. The suite's own note said as much, and
//! said why supplying a placeholder would be worse than not running: a placeholder makes
//! `is_evidence()` true for proofs that examined nothing, which is precisely the thing the class
//! exists to expose.
//!
//! # Why this needs no change to any of the 229 proof files
//!
//! Every tier-4 proof in this workspace goes through one of the five combinators in the crate root.
//! They are the funnel, so the count is recorded there — once per call, not once per case.
//!
//! Attribution comes from `std::thread::current().name()`. Rust's test harness runs each `#[test]`
//! on a thread **named after the test function**, so a combinator called from
//! `proof_p1_no_terminator_survives` records under exactly that name with no cooperation from the
//! proof, no macro, and no edit to a single test file. Calls from an unnamed thread are recorded
//! under `<unnamed>` rather than dropped: silently discarding them would understate the total, and
//! an understated total makes proofs look vacuous that are not.
//!
//! # Off unless asked, and it says so
//!
//! Recording happens only when the environment variable [`OUT_VAR`] names a file. Absent it this
//! module is a branch on a `OnceLock` and nothing else, so an ordinary `cargo test` is unaffected —
//! which matters, because a measurement apparatus that changes the thing it measures is not one.
//!
//! The whole module is behind `feature = "std"`. `no_std` builds — every kernel-side user of this
//! crate — compile [`record`] to an empty inline function that cannot touch a file, an allocator or
//! a lock. That is not an optimisation; a proof engine that opens files is not deployable in a
//! kernel, and the OS is where this crate actually runs.
//!
//! # The format, and why it is append-only lines rather than a structure
//!
//! One record per line, `name<TAB>cases`. Tests run in parallel, so the file is written under a
//! mutex and each line is one `write_all` of a complete record — a partial line would be read as a
//! smaller `cases` figure, and a smaller figure biases toward *reporting vacuity that is not there*.
//! Duplicate names are expected and correct: a proof that calls three combinators emits three lines,
//! and the reader sums them. Summing rather than taking the maximum is deliberate — a proof that
//! examined 256 inputs in each of three domains examined 768, and the question `is_evidence()` asks
//! is only ever "was it more than zero".

use std::fs::OpenOptions;
use std::io::Write;
use std::sync::{Mutex, OnceLock};

/// The environment variable that names the harvest file. Unset means do nothing.
pub const OUT_VAR: &str = "AION_COVER_OUT";

/// The sink, resolved once. `None` when [`OUT_VAR`] is unset or the file could not be opened.
///
/// A failure to open is a permanent `None` rather than a retry per call: a proof run that stalls on
/// a filesystem error every time a combinator is entered would be a measurement apparatus that
/// dominates the measurement.
fn sink() -> Option<&'static Mutex<std::fs::File>> {
    static SINK: OnceLock<Option<Mutex<std::fs::File>>> = OnceLock::new();
    SINK.get_or_init(|| {
        let path = std::env::var(OUT_VAR).ok()?;
        if path.is_empty() {
            return None;
        }
        OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .ok()
            .map(Mutex::new)
    })
    .as_ref()
}

/// Record that a combinator examined `cases` inputs, attributed to the current test thread.
///
/// Called by every combinator in the crate root. Cheap and total: it never panics, never propagates
/// an error, and does nothing at all when [`OUT_VAR`] is unset. A harvester that can fail a proof
/// run would be a measurement that changes the verdict it is measuring.
pub fn record(cases: u64) {
    let Some(m) = sink() else { return };
    let name = std::thread::current()
        .name()
        .unwrap_or("<unnamed>")
        .to_string();
    // A lock poisoned by an unrelated panicking test must not silence the rest of the run: the
    // guard is recovered rather than propagated, because losing every subsequent record would make
    // proofs after the first failure look vacuous.
    let mut f = match m.lock() {
        Ok(g) => g,
        Err(p) => p.into_inner(),
    };
    let _ = f.write_all(format!("{name}\t{cases}\n").as_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recording_is_inert_when_the_variable_is_unset() {
        // The default path, and the one that must cost nothing: an ordinary `cargo test` in this
        // workspace runs 1027 suites and none of them asked to be measured.
        //
        // This asserts the OBSERVABLE consequence — whether a sink exists — rather than re-reading
        // the same `env::var` the code reads, which would prove only that `std::env` is
        // deterministic.
        //
        // BOTH environments are asserted, in the branch each one lands in. The earlier form asserted
        // the variable was unset and then checked inertness, which made it **fail during the one run
        // it exists to support**: `AION_COVER_OUT=<path> cargo test --workspace` is how the harvest
        // is regenerated, and this test went red on every regeneration. A precondition assertion
        // that only holds outside the interesting case is not a check of the interesting case, and a
        // red that everyone learns to expect is a red nobody reads.
        let asked = std::env::var(OUT_VAR).ok().filter(|p| !p.is_empty());
        record(4242);
        match asked {
            None => assert!(sink().is_none(), "no sink may exist with {OUT_VAR} unset"),
            Some(path) => assert!(
                sink().is_some(),
                "{OUT_VAR} names {path:?}, so a sink must exist — a harvest run that silently \
                 recorded nothing would report every proof in the workspace as vacuous"
            ),
        }
    }

    #[test]
    fn the_test_harness_names_its_threads_after_the_test() {
        // The whole attribution scheme rests on this and nothing else, so it is asserted rather
        // than assumed. If a future harness stops naming threads, every record collapses into
        // `<unnamed>`, every proof looks like one giant proof, and `aion_cover` would silently
        // report crate-wide coverage from a single bucket. That must break loudly here first.
        let this = std::thread::current();
        let name = this.name().unwrap_or("");
        assert!(
            name.ends_with("the_test_harness_names_its_threads_after_the_test"),
            "libtest no longer names test threads after the test — harvest attribution is broken; got {name:?}"
        );
    }
}
