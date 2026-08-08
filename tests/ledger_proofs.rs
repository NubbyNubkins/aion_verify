// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Tests for the tamper-evident proof ledger.
//!   P1 the pure-Rust SHA-256 matches the FIPS 180-4 known-answer vectors (the crypto is correct).
//!   P2 a well-formed chain verifies; the head changes with every record.
//!   P3 altering ANY past record's payload is detected by verify() (tamper-evidence).
//!   P4 deleting a record from the middle is detected (the log can't be silently cut).

use aion_verify::ledger::{sha512, Ledger};

fn hex(b: &[u8]) -> String {
    let mut s = String::new();
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

#[test]
fn sha512_matches_fips_known_answers() {
    assert_eq!(
        hex(&sha512(b"")),
        "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
    );
    assert_eq!(
        hex(&sha512(b"abc")),
        "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
    );
    assert_eq!(
        hex(&sha512(
            b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
        )),
        "204a8fc6dda82f0a0ced7beb8e08a41657c16ef468b228a8279be331a703c33596fd15c13b1b07f9aa1d3bea57789ca031ad85c7a71dd70354ec631238ca3445"
    );
}

#[test]
fn a_well_formed_chain_verifies_and_the_head_moves() {
    let mut l = Ledger::new();
    assert_eq!(l.head(), [0u8; 64], "empty ledger has a zero head");
    let h1 = l.record("x+1 > x over u8", true);
    let h2 = l.record("x <= 100 over u64", false); // a REFUTED result is recorded too
    let h3 = l.record("(x>>1) <= x refined", true);
    assert!(h1 != h2 && h2 != h3, "the head advances with every record");
    assert_eq!(l.len(), 3);
    assert_eq!(l.head(), h3);
    assert_eq!(l.verify(), Ok(()), "an untampered chain verifies");
}

#[test]
fn altering_a_past_record_is_detected() {
    let mut l = Ledger::new();
    l.record("proof A", true);
    l.record("proof B", true);
    l.record("proof C", true);

    // Reload the chain, then flip a "proven" flag on the FIRST record (forging a false proof).
    let mut entries = l.entries().to_vec();
    let last = entries[0].data.len() - 1;
    entries[0].data[last] ^= 1; // true -> false
    let tampered = Ledger::from_entries(entries);
    assert_eq!(
        tampered.verify(),
        Err(0),
        "altering record 0's payload is caught at seq 0"
    );
}

#[test]
fn deleting_a_record_is_detected() {
    let mut l = Ledger::new();
    for i in 0..5 {
        l.record("proof", i % 2 == 0);
    }
    // Cut the middle record out of the persisted chain.
    let mut entries = l.entries().to_vec();
    entries.remove(2);
    let cut = Ledger::from_entries(entries);
    // The entry now at index 2 has seq 3 -> sequence gap detected immediately.
    assert!(cut.verify().is_err(), "a deleted record breaks the chain");
    assert_eq!(cut.verify(), Err(2));
}

#[test]
fn a_diverged_head_proves_rewriting_against_an_anchor() {
    // The real deletion defence: anchor the head, later re-derive it; divergence = proof of rewriting.
    let mut a = Ledger::new();
    a.record("r0", true);
    a.record("r1", false);
    let anchored_head = a.head();

    // A rewritten history (r1 flipped to proven) produces a different head — detectable against the anchor.
    let mut b = Ledger::new();
    b.record("r0", true);
    b.record("r1", true);
    assert_ne!(
        b.head(),
        anchored_head,
        "any rewrite diverges from the anchored head"
    );
}

// ── P6 — the record is READABLE, not merely distinct (the 3.8.0 soundness defect) ─────────────────
//
// Until 3.9.0, `record` encoded `(label, proven)` as `label ‖ 0x00 ‖ flag`. A Rust `&str` may contain
// U+0000, so any reader had to cut at the FIRST terminator and took a byte out of the middle of the
// label as the flag: `record("...spins\0\x01", proven = false)` read back as `proven = true`. A
// REFUTATION READ BACK AS A PROOF, and the corruption ran both ways.
//
// Nothing caught it. `verify()` confirms the stored bytes are the bytes written, and they were — the
// chain protected the TRANSPORT of a record whose MEANING was destroyed at the moment of writing. The
// one check that existed compared HASHES, which is injectivity, not readability: two payloads can hash
// differently and both decode to the same wrong flag. That is exactly what happened.
//
// So the property below is deliberately about READABILITY and not about distinctness, and its domain
// deliberately contains embedded NULs and the empty label — the inputs the old encoding died on.

/// Labels chosen so the proof cannot pass by avoiding the hard cases. Three contain U+0000, one is
/// empty, one is a lone NUL; both counts are asserted below so the domain cannot silently narrow.
const LABELS: [&str; 8] = [
    "aion_storage::nothing_spins",
    "aion_storage::nothing_spins\u{0}\u{1}", // the original counterexample
    "x\u{0}\u{0}",                           // corruption in the other direction
    "\u{0}",                                 // a label that is nothing but a terminator
    "",                                      // the empty label
    "a",
    "unicode ✓ label",
    "a::b::c::very_long_label_with_no_terminator_at_all",
];

#[test]
fn p6_every_record_reads_back_as_exactly_what_was_written() {
    // The domain must actually contain the hard cases, or "it round-trips" is a claim about easy input.
    assert_eq!(LABELS.iter().filter(|l| l.contains('\u{0}')).count(), 3);
    assert_eq!(LABELS.iter().filter(|l| l.is_empty()).count(), 1);

    let v = aion_verify::for_all_pairs(&LABELS, &[true, false], |&label, &proven| {
        let mut l = Ledger::new();
        l.record(label, proven);
        match Ledger::read_record(&l.entries()[0].data) {
            Some((back, flag)) => back == label && flag == proven,
            None => false,
        }
    });
    assert!(
        v.is_proven(),
        "a record did not read back as written: {:?}",
        v.counterexample()
    );
    assert_eq!(
        v.cases(),
        (LABELS.len() * 2) as u64,
        "16 cases, all of them"
    );
}

#[test]
fn p6_the_flag_survives_independently_of_the_label() {
    // The specific 3.8.0 failure, stated as its own claim: the SAME label recorded both ways must read
    // back both ways. Under the old encoding this failed for every label containing U+0000.
    let v = aion_verify::for_all(LABELS, |&label| {
        let mut t = Ledger::new();
        t.record(label, true);
        let mut f = Ledger::new();
        f.record(label, false);
        let (lt, pt) = Ledger::read_record(&t.entries()[0].data).unwrap();
        let (lf, pf) = Ledger::read_record(&f.entries()[0].data).unwrap();
        lt == label && lf == label && pt && !pf
    });
    assert!(v.is_proven(), "flag lost: {:?}", v.counterexample());
    assert_eq!(v.cases(), LABELS.len() as u64);
}

#[test]
fn p6_a_non_record_payload_is_refused_rather_than_guessed_at() {
    // `append` takes arbitrary bytes, which are not a proof record. Every flag byte outside {0,1} must
    // be refused — all 254 of them, not a sample — and an empty payload too.
    let v = aion_verify::for_all_u8(|b| {
        if b <= 1 {
            return true; // a valid flag; covered by the proofs above
        }
        let mut l = Ledger::new();
        l.append(&[b, b'x']);
        Ledger::read_record(&l.entries()[0].data).is_none()
    });
    assert!(v.is_proven(), "guessed at a flag: {:?}", v.counterexample());
    assert_eq!(v.cases(), 256);

    let mut empty = Ledger::new();
    empty.append(&[]);
    assert!(Ledger::read_record(&empty.entries()[0].data).is_none());
}
