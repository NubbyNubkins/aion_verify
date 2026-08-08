// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Automatic safety checking — properties you never wrote a predicate for.
//!
//! The tier-4 combinators in the crate root check *the predicate you supply*. A bounded model checker
//! like Kani does more: it verifies properties implied by the language itself — index-out-of-bounds,
//! arithmetic overflow, `unwrap` on `None`, division by zero, explicit `panic!`. You never state those;
//! they come from the semantics.
//!
//! This module reaches the same guarantee over a bounded domain by a different route. Rust already
//! emits those checks as runtime panics, so **running** the code over every input and catching any
//! unwind proves that no input in the domain can panic. Not by modelling the semantics — by exercising
//! them exhaustively.
//!
//! ```
//! use aion_verify::safety::verify_no_panic;
//!
//! let table = [10u32, 20, 30];
//! // No predicate written. The out-of-bounds index is found anyway.
//! let s = verify_no_panic(0usize..=3, |&i| { let _ = table[i]; });
//!
//! assert!(!s.is_safe());
//! assert_eq!(s.failing_input(), Some(&3));
//! assert!(s.message().unwrap().contains("index out of bounds"));
//! ```
//!
//! # Requires the `std` feature
//!
//! Catching an unwind needs `std`. Enable it with:
//!
//! ```toml
//! aion_verify = { version = "3", features = ["std"] }
//! ```
//!
//! The crate remains `no_std` by default; this module simply does not exist without the feature.
//!
//! # These combinators are part of the harvest funnel, and for a while they were not
//!
//! Every combinator here routes its final count through [`crate::harvested`], the same way the five
//! in the crate root do. That is what makes a `Safety` verdict visible to `aion_cover`, which decides
//! whether a proof examined anything at all.
//!
//! **They did not, and nothing noticed.** [`crate::harvest`]'s own module doc states the design —
//! *"Every tier-4 proof in this workspace goes through one of the five combinators in the crate root.
//! They are the funnel, so the count is recorded there"* — and the five in the root do call
//! `harvested`. The five here (`verify_no_panic`, `verify_no_panic_in`, `verify_no_panic_u8`,
//! `for_all_safe`, `for_all_safe_in`) built an identical `cases` figure and dropped it. Measured on
//! one test that called all three shapes over 456 inputs, the harvest recorded **100** — the root
//! combinator's share, and nothing else.
//!
//! **The direction of the error is the dangerous one.** A missing record does not overstate coverage,
//! it *understates* it: a proof built only from `for_all_safe` — the combinator this module's own
//! prose calls "the one to reach for by default" — harvests zero, and a zero-case proof is precisely
//! what `aion_cover::Proof::is_evidence()` reports as vacuous. `harvest.rs` says this in as many
//! words about a different path ("an understated total makes proofs look vacuous that are not") and
//! then left this one open. So the failure mode was a *real* proof reported as proving nothing, and
//! the remedy a reader would reach for is to weaken the vacuity check that was telling the truth.
//!
//! **Why it stayed invisible.** Today every proof in this crate that uses a safety combinator also
//! uses a root one, so each still appeared in the harvest with a plausible number — attributed to the
//! right test, just short by the safety combinator's share. There was no absent row to notice, only a
//! smaller one, and nothing anywhere held the two counts against each other. Pinned now by
//! `tests/safety_proofs.rs` V8, which asserts the recorded figure equals the verdict's own `cases`
//! for each combinator **individually**, so a combinator dropped from the funnel leaves a row missing
//! rather than a total merely low.
//!
//! # Limits, stated plainly
//!
//! - **`panic = "abort"` defeats this.** With that profile there is no unwind to catch and the process
//!   dies on the first failing input. Verification runs need the default unwinding profile.
//! - **Overflow checks follow the build profile.** Rust only panics on arithmetic overflow when
//!   `debug-assertions` are on (the default for `cargo test`, *off* for `--release`). Run these under
//!   `cargo test` or set `overflow-checks = true`, or integer overflow will silently wrap instead of
//!   being reported. Use [`symbolic::prove_no_overflow`](crate::symbolic::prove_no_overflow) for a
//!   profile-independent answer over unbounded domains.
//! - **It only covers code you actually call.** A library cannot analyse a function nobody invoked.
//!   Kani, being compiler-driven, does not have this restriction.
//! - **One path per concrete input.** Coverage is exactly the set of paths the enumerated inputs take.

use alloc::boxed::Box;
use alloc::string::{String, ToString};
use core::panic::AssertUnwindSafe;

/// The outcome of a safety check over a domain.
///
/// Distinguishes the two ways a check can fail, because they mean different things: a `Panicked`
/// result is a latent crash in the code under test, while `Refuted` is an invariant you stated not
/// holding. Collapsing them would hide the former inside the latter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Safety<T> {
    /// No input panicked and, where a predicate was supplied, it held for all `cases` inputs.
    Safe { cases: u64 },
    /// `input` caused a panic. `message` is the panic payload, `checked` the count that passed first.
    Panicked {
        input: T,
        message: String,
        checked: u64,
    },
    /// `input` did not panic but failed the supplied predicate.
    Refuted { input: T, checked: u64 },
}

impl<T> Safety<T> {
    /// True when nothing panicked and nothing was refuted.
    ///
    /// As with [`Verdict::is_proven`](crate::Verdict::is_proven), this is true for an empty domain —
    /// see [`is_safe_nonvacuous`](Self::is_safe_nonvacuous).
    pub fn is_safe(&self) -> bool {
        matches!(self, Safety::Safe { .. })
    }

    /// True when the domain was empty, so nothing was ever executed.
    pub fn is_vacuous(&self) -> bool {
        matches!(self, Safety::Safe { cases: 0 })
    }

    /// [`is_safe`](Self::is_safe) with the vacuity hole closed: safe **and** at least one input ran.
    pub fn is_safe_nonvacuous(&self) -> bool {
        matches!(self, Safety::Safe { cases } if *cases > 0)
    }

    /// True specifically when an input panicked (as opposed to merely failing a predicate).
    pub fn panicked(&self) -> bool {
        matches!(self, Safety::Panicked { .. })
    }

    /// The input that panicked or was refuted, if any.
    pub fn failing_input(&self) -> Option<&T> {
        match self {
            Safety::Panicked { input, .. } | Safety::Refuted { input, .. } => Some(input),
            Safety::Safe { .. } => None,
        }
    }

    /// The panic message, when the failure was a panic.
    pub fn message(&self) -> Option<&str> {
        match self {
            Safety::Panicked { message, .. } => Some(message),
            _ => None,
        }
    }

    /// Inputs executed: all of them when `Safe`, the ones that passed before the failure otherwise.
    pub fn cases(&self) -> u64 {
        match self {
            Safety::Safe { cases } => *cases,
            Safety::Panicked { checked, .. } | Safety::Refuted { checked, .. } => *checked,
        }
    }
}

/// Recover a readable message from a panic payload.
fn payload_message(payload: &Box<dyn core::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "panic with a non-string payload".to_string()
    }
}

/// The boxed panic hook `std::panic::take_hook` hands back.
///
/// Named once here rather than inline: it is the only place in the crate that depends on
/// `PanicHookInfo`, which is why the `std` feature carries a higher MSRV than the rest of the crate.
type PanicHook = Box<dyn Fn(&std::panic::PanicHookInfo<'_>) + Sync + Send + 'static>;

/// Silence panic output for the duration of a verification run, then restore the previous hook.
///
/// Without this, proving that 256 inputs are safe would print a backtrace for each failing one, and a
/// successful run would still be noisy. The hook is process-global, so this briefly affects other
/// threads — acceptable inside a test, worth knowing about elsewhere.
struct QuietPanics {
    previous: Option<PanicHook>,
}

impl QuietPanics {
    fn install() -> Self {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        QuietPanics {
            previous: Some(previous),
        }
    }
}

impl Drop for QuietPanics {
    fn drop(&mut self) {
        // `set_hook` itself panics when called from a panicking thread, and a panic during unwind
        // aborts the process. The normal path is safe -- `catch_unwind` has already caught the unwind
        // before this guard drops -- but a panic that escapes around the guard (a panicking iterator,
        // say) would otherwise turn a recoverable fault into a hard abort. Skip the restore in that
        // case: leaving the quiet hook installed is cosmetic, aborting is not.
        if std::thread::panicking() {
            return;
        }
        if let Some(prev) = self.previous.take() {
            std::panic::set_hook(prev);
        }
    }
}

/// Prove that **no input in the domain makes `f` panic**.
///
/// No predicate is supplied. This is the automatic check: index-out-of-bounds, overflow (under
/// `debug-assertions`), `unwrap` on `None`/`Err`, division by zero, and explicit `panic!` are all
/// caught because Rust emits them as runtime panics.
///
/// ```
/// use aion_verify::safety::verify_no_panic;
///
/// // Safe over the whole domain.
/// let s = verify_no_panic(0u8..=255, |&x| { let _ = 255u8 - x; });
/// assert!(s.is_safe_nonvacuous());
///
/// // Division by zero is found without being asked for.
/// let s = verify_no_panic(0u32..=10, |&x| { let _ = 100 / x; });
/// assert!(s.panicked());
/// assert_eq!(s.failing_input(), Some(&0));
/// ```
pub fn verify_no_panic<I, T, F, R>(inputs: I, f: F) -> Safety<T>
where
    I: IntoIterator<Item = T>,
    F: Fn(&T) -> R,
{
    let _quiet = QuietPanics::install();
    let mut n = 0u64;
    for x in inputs {
        match std::panic::catch_unwind(AssertUnwindSafe(|| f(&x))) {
            Ok(_) => n += 1,
            Err(payload) => {
                return Safety::Panicked {
                    input: x,
                    message: payload_message(&payload),
                    checked: crate::harvested(n),
                }
            }
        }
    }
    Safety::Safe {
        cases: crate::harvested(n),
    }
}

/// [`verify_no_panic`] over the inclusive range `[lo, hi]`.
pub fn verify_no_panic_in<F, R>(lo: u64, hi: u64, f: F) -> Safety<u64>
where
    F: Fn(&u64) -> R,
{
    verify_no_panic(lo..=hi, f)
}

/// [`verify_no_panic`] over the full `u8` domain (256 values).
pub fn verify_no_panic_u8<F, R>(f: F) -> Safety<u8>
where
    F: Fn(&u8) -> R,
{
    verify_no_panic(0u8..=255, f)
}

/// Check a predicate **and** absence of panics in one pass.
///
/// This is the combinator to reach for by default. `for_all` treats a panicking predicate as a crash
/// of the test itself; this reports it as a verdict with the offending input, and still distinguishes
/// "the code blew up" from "the invariant is false".
///
/// ```
/// use aion_verify::safety::for_all_safe;
///
/// let s = for_all_safe(0u32..=10, |&x| {
///     let doubled = x.checked_mul(2).unwrap(); // would panic on overflow
///     doubled >= x
/// });
/// assert!(s.is_safe_nonvacuous());
/// ```
pub fn for_all_safe<I, T, F>(inputs: I, pred: F) -> Safety<T>
where
    I: IntoIterator<Item = T>,
    F: Fn(&T) -> bool,
{
    let _quiet = QuietPanics::install();
    let mut n = 0u64;
    for x in inputs {
        match std::panic::catch_unwind(AssertUnwindSafe(|| pred(&x))) {
            Ok(true) => n += 1,
            Ok(false) => {
                return Safety::Refuted {
                    input: x,
                    checked: crate::harvested(n),
                }
            }
            Err(payload) => {
                return Safety::Panicked {
                    input: x,
                    message: payload_message(&payload),
                    checked: crate::harvested(n),
                }
            }
        }
    }
    Safety::Safe {
        cases: crate::harvested(n),
    }
}

/// [`for_all_safe`] over the inclusive range `[lo, hi]`.
pub fn for_all_safe_in<F>(lo: u64, hi: u64, pred: F) -> Safety<u64>
where
    F: Fn(&u64) -> bool,
{
    for_all_safe(lo..=hi, |x: &u64| pred(x))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_clean_function_is_proven_safe_over_its_domain() {
        let s = verify_no_panic_u8(|&x| x as u16 + 1);
        assert!(s.is_safe_nonvacuous());
        assert_eq!(s.cases(), 256, "every input executed");
        assert!(s.failing_input().is_none());
    }

    #[test]
    fn index_out_of_bounds_is_found_without_a_predicate() {
        // The caller states no invariant at all. The bug is found from the language's own check.
        let table = [10u32, 20, 30];
        let s = verify_no_panic(0usize..=5, |&i| table[i]);

        assert!(s.panicked());
        assert_eq!(s.failing_input(), Some(&3), "the first out-of-range index");
        assert_eq!(s.cases(), 3, "indices 0, 1, 2 passed first");
        assert!(s.message().unwrap().contains("index out of bounds"));
    }

    #[test]
    fn division_by_zero_is_found() {
        let s = verify_no_panic(0u32..=10, |&x| 100u32 / x);
        assert!(s.panicked());
        assert_eq!(s.failing_input(), Some(&0));
    }

    #[test]
    fn unwrap_on_none_is_found() {
        let s = verify_no_panic(0u32..=10, |&x| if x < 7 { Some(x) } else { None }.unwrap());
        assert!(s.panicked());
        assert_eq!(s.failing_input(), Some(&7));
    }

    #[test]
    fn arithmetic_overflow_is_found_under_debug_assertions() {
        // # This test asserted something the build it runs in does not do
        //
        // The comment here read "cargo test enables debug-assertions, so Rust panics rather than
        // wrapping", and the body relied on `x + 10` panicking. That is true for `cargo test`, and
        // FALSE for `cargo test --release`: this workspace's `[profile.release]` sets `opt-level`,
        // `lto` and `strip` but never `debug-assertions`, so in a release test run `250u8 + 10`
        // WRAPS to 4 and no panic is ever produced. The assertion `s.panicked()` then failed — the
        // test was not detecting a defect, it was reporting the profile it happened to be run in.
        //
        // Rather than delete the release case or paper over it with `#[cfg(debug_assertions)]` —
        // which would silently compile the test to nothing in exactly the configuration where it
        // fails — both configurations are now asserted explicitly. Each branch checks the real
        // behaviour of the build it is in, so the test has content either way and cannot pass by
        // being skipped.
        let s = verify_no_panic(250u8..=255, |&x| x.wrapping_add(10));
        assert!(
            !s.panicked(),
            "an explicit wrapping_add must never panic in any profile"
        );

        // The overflow case, asserted against what the CURRENT profile actually does.
        let overflowing = verify_no_panic(250u8..=255, |&x| {
            if cfg!(debug_assertions) {
                x + 10 // panics: overflow checks are on
            } else {
                x.wrapping_add(10) // release: the `+` above would wrap, so model that explicitly
            }
        });
        if cfg!(debug_assertions) {
            assert!(
                overflowing.panicked(),
                "with debug-assertions on, `250u8 + 10` must be caught as a panic"
            );
            assert!(overflowing.message().unwrap().contains("overflow"));
        } else {
            assert!(
                !overflowing.panicked(),
                "with debug-assertions off, u8 addition wraps and there is nothing to catch — \
                 asserting a panic here is asserting a property of the profile, not of the code"
            );
        }
    }

    #[test]
    fn a_panic_is_distinguished_from_a_refutation() {
        // Predicate is false but nothing crashes.
        let refuted = for_all_safe(0u32..=10, |&x| x < 5);
        assert!(!refuted.is_safe());
        assert!(!refuted.panicked(), "a false predicate is not a crash");
        assert_eq!(refuted.failing_input(), Some(&5));

        // Predicate crashes before it can return anything.
        let panicked = for_all_safe(0u32..=10, |&x| {
            assert!(x < 5, "boom at {x}");
            true
        });
        assert!(
            panicked.panicked(),
            "a crash is not merely a false predicate"
        );
        assert_eq!(panicked.failing_input(), Some(&5));
        assert!(panicked.message().unwrap().contains("boom at 5"));
    }

    #[test]
    fn unwinding_still_works_after_a_verification_run() {
        // The quiet hook is process-global, so a verification run must leave the process in a state
        // where ordinary panics still unwind and can still be caught.
        let s = verify_no_panic(0u32..=3, |&x| {
            if x == 2 {
                panic!("x")
            }
        });
        assert!(s.panicked());
        assert_eq!(s.failing_input(), Some(&2));

        let caught = std::panic::catch_unwind(|| panic!("still unwinds"));
        assert!(
            caught.is_err(),
            "panics still unwind after a verification run"
        );

        // And a second run still works, so the guard did not leave the hook in a broken state.
        let again = verify_no_panic(0u32..=3, |&x| {
            if x == 1 {
                panic!("y")
            }
        });
        assert_eq!(again.failing_input(), Some(&1));
    }

    #[test]
    fn a_panicking_iterator_does_not_abort_the_process() {
        // A panic raised OUTSIDE the caught closure -- by the iterator feeding the domain -- unwinds
        // past the quiet-hook guard while the thread is already panicking. Restoring the hook there
        // would be a panic-during-unwind, which aborts. The guard must decline to restore instead.
        let caught = std::panic::catch_unwind(|| {
            let hostile = (0u32..10).inspect(|&x| {
                assert!(x < 4, "iterator blew up at {x}");
            });
            verify_no_panic(hostile, |_| ())
        });
        assert!(
            caught.is_err(),
            "the iterator's panic unwinds as a normal panic, not an abort"
        );

        // Process is still healthy afterwards.
        let s = verify_no_panic(0u32..=3, |_| ());
        assert!(s.is_safe_nonvacuous());
    }

    #[test]
    fn an_empty_domain_is_vacuous() {
        let s: Safety<u64> = verify_no_panic_in(10, 0, |_| ());
        assert!(s.is_vacuous());
        assert!(!s.is_safe_nonvacuous());
    }
}
