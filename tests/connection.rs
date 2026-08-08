//! TIER 2 — CONNECTION: the first-party engine proving **another crate's** invariant.
//!
//! # Why this file differs from the copy in the AION OS workspace — read before "fixing" it
//!
//! `aion_verify` exists in two places. The copy inside the AION OS workspace
//! (`10_core/aion_os/crates/aion_verify`) is the one AION itself builds against; this copy is the one
//! published to crates.io. **`src/**` is identical between them by policy, and a difference there is a
//! defect** — published users must be running the same engine code we prove against.
//!
//! `tests/connection.rs` and `tests/grouping.rs` are the two deliberate exceptions, and this is the
//! reason:
//!
//! - The in-workspace copy proves the invariants of `aion_provision`, a private AION crate that is not
//!   published and never will be. It reaches it as a **path** dev-dependency.
//! - `cargo publish` strips path-only dev-dependencies. So the in-workspace versions of these two
//!   files could never ship in a form a downloader could compile — the two tests that demonstrate the
//!   entire point of the engine were exactly the two nobody outside could run.
//! - This copy therefore proves the same *shape* of invariant over
//!   [`aion_verify_subject`](https://crates.io/crates/aion_verify_subject), a companion crate
//!   published for the purpose: same access-control shape, resolvable by version, zero dependencies,
//!   and — importantly — no dependency on `aion_verify`. An engine checking a predicate it also
//!   defined proves only that it agrees with itself.
//!
//! So: **the subject differs on purpose; the claim does not.** Both copies establish that a principal
//! granted exactly one authority holds that one and no other, over the whole of a finite domain, by
//! complete coverage rather than by sampling. If you are reconciling the two trees, reconcile the
//! *claims*, not the text.
//!
//! # What this file proves
//!
//! Using [`for_all`] over the whole `Clearance` domain, that a badge-holder granted exactly one
//! clearance holds that one **and no other**. Note what the predicate ranges over: every clearance
//! `c`, asserting `may(badge, c) == (c == granted)`. The obvious version of this test — grant `c`,
//! assert the holder may do `c` — cannot fail in the direction that matters, because it never looks
//! at what leaked.

use aion_verify::{for_all, Verdict};
use aion_verify_subject::{BadgeId, Clearance, Door, Site, ROLE_STAFF};

#[test]
fn engine_proves_clearance_grant_is_exact() {
    // For every clearance c, a staff badge granted only c may do exactly c.
    let v: Verdict<Clearance> = for_all(Clearance::ALL, |&granted| {
        let mut s = Site::new(
            BadgeId(1),
            Door {
                building: 4,
                number: 12,
            },
            "north-gate",
        );
        s.commission();
        s.issue(BadgeId(2), ROLE_STAFF);
        s.grant(ROLE_STAFF, granted);
        Clearance::ALL
            .iter()
            .all(|&c| s.may(BadgeId(2), c) == (c == granted))
    });
    assert!(v.is_proven(), "counterexample: {:?}", v.counterexample());
    assert_eq!(
        v.cases(),
        Clearance::ALL.len() as u64,
        "proven over the whole clearance domain"
    );
    // The denominator is a disclosure, not a score: state it, so a domain that silently shrank to one
    // element cannot pass as a proof over ten.
    assert_eq!(Clearance::ALL.len(), 10);
}
