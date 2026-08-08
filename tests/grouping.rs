//! TIER 3 — GROUPING: the engine driving several of another crate's core invariants at once, each a
//! complete-coverage proof (`Proven { cases }`) or a counterexample.
//!
//! # Why this file differs from the copy in the AION OS workspace — read before "fixing" it
//!
//! The same reason as [`connection.rs`](../connection.rs), stated again here because a reason that
//! lives in only one of two files rots in the other:
//!
//! `aion_verify` exists in two places. **`src/**` is identical between them by policy**, because
//! published users must be running the same engine code we prove against. `tests/connection.rs` and
//! `tests/grouping.rs` are the two deliberate exceptions. The in-workspace copy proves the invariants
//! of `aion_provision`, a private AION crate reached as a **path** dev-dependency; `cargo publish`
//! strips path-only dev-dependencies, so those two files could never ship in a form a downloader
//! could compile. This copy proves the same shape of invariant over
//! [`aion_verify_subject`](https://crates.io/crates/aion_verify_subject), published for the purpose,
//! which depends on nothing — including `aion_verify` itself.
//!
//! **The subject differs on purpose; the claims do not.** Reconcile claims, not text.
//!
//! # What this file proves
//!
//! 1. **Independence.** Covering one wing never covers another — over the *product* `Wing × Wing`,
//!    so a leak in either direction is visible. Checking only "the wing I asked for is covered"
//!    cannot fail on a leak.
//! 2. **Revocation is total.** For every clearance, a revoked badge holds none of it — after being
//!    granted *all* of them, so the check has something to find.
//! 3. **Outsiders hold nothing.** A badge that was never issued holds no clearance, however
//!    generously the roles were granted.

use aion_verify::{for_all, for_all_pairs};
use aion_verify_subject::{BadgeId, Clearance, Door, Site, Wing, ROLE_STAFF};

fn site() -> Site {
    let mut s = Site::new(
        BadgeId(1),
        Door {
            building: 7,
            number: 3,
        },
        "grouping",
    );
    s.commission();
    s
}

#[test]
fn engine_proves_the_access_control_invariants() {
    // 1) Every wing is independent: covering one never covers another (product of ALL x ALL).
    let indep = for_all_pairs(&Wing::ALL, &Wing::ALL, |&w, &other| {
        let mut s = site();
        s.cover_wing(w);
        w == other || !s.covers(other)
    });
    assert!(indep.is_proven(), "wing leak: {:?}", indep.counterexample());
    assert_eq!(
        indep.cases(),
        (Wing::ALL.len() * Wing::ALL.len()) as u64,
        "proven over the whole product domain"
    );

    // 2) Revocation is total: for every clearance, a revoked badge holds none of it.
    let removal = for_all(Clearance::ALL, |&cl| {
        let mut s = site();
        s.issue(BadgeId(2), ROLE_STAFF);
        for c in Clearance::ALL {
            s.grant(ROLE_STAFF, c);
        }
        // Before revocation the badge really did hold it — otherwise the check below would pass on a
        // badge that never had anything, and prove nothing at all.
        assert!(s.may(BadgeId(2), cl), "precondition: grant did nothing");
        s.revoke(BadgeId(2));
        !s.may(BadgeId(2), cl)
    });
    assert!(
        removal.is_proven(),
        "revocation leaked: {:?}",
        removal.counterexample()
    );
    assert_eq!(removal.cases(), Clearance::ALL.len() as u64);

    // 3) An outsider holds no clearance at all.
    let outsider = for_all(Clearance::ALL, |&cl| {
        let mut s = site();
        for c in Clearance::ALL {
            s.grant(ROLE_STAFF, c);
        }
        !s.may(BadgeId(999), cl)
    });
    assert!(
        outsider.is_proven(),
        "outsider had authority: {:?}",
        outsider.counterexample()
    );
    assert_eq!(outsider.cases(), Clearance::ALL.len() as u64);

    // The denominators, disclosed: 10 clearances and 12 wings, so a silently narrowed domain cannot
    // pass as a proof over the full one.
    assert_eq!(Clearance::ALL.len(), 10);
    assert_eq!(Wing::ALL.len(), 12);
}
