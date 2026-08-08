// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! **Many-time post-quantum signatures** — a Merkle Signature Scheme (XMSS-style) over the one-time
//! WOTS of [`crate::pqsig`].
//!
//! WOTS signs one message per key. This builds a binary Merkle tree of `2^height` WOTS keypairs; the
//! **single published public key is the tree root**, and each signature carries a WOTS signature under
//! one leaf plus the `height` sibling hashes (the *authentication path*) that let a verifier recompute
//! the root. So one 64-byte published key authenticates `2^height` proofs — an unbounded-in-practice
//! signed proof stream, still resting only on SHA-512 (post-quantum, no Shor exposure), still zero-dep.
//!
//! **Stateful.** Each leaf must sign at most once, so [`MerkleKey::sign`] advances an internal index and
//! refuses to reuse a leaf. Keep `height` modest (keygen builds all `2^height` WOTS keys): 8–12 gives
//! 256–4096 signatures per published key.

use crate::ledger::sha512;
use crate::pqsig;
use alloc::vec::Vec;

const N: usize = 64;

/// The largest `height` this scheme can represent.
///
/// The leaf index is a `u32`, so `2^32` leaves is the arithmetic ceiling and `1u32 << 32` is already
/// out of range — it panics under `debug-assertions` and masks to `1u32 << 0` in a release build,
/// which is worse, because the result looks like a working one-leaf tree. Nothing at or beyond this
/// height is constructible in any case: [`MerkleKey::keygen`] performs `2^height` WOTS keygens, so
/// the practical ceiling is far lower (8–12, as the module says). This constant exists so the two
/// functions a caller can reach with an arbitrary `height` — [`MerkleKey::capacity`] and [`verify`] —
/// are TOTAL rather than profile-dependent.
pub const MAX_HEIGHT: u32 = 31;

/// Domain-separated leaf hash of a WOTS public key.
fn leaf_hash(wots_pk: &[u8; N]) -> [u8; N] {
    let mut b = Vec::with_capacity(1 + N);
    b.push(0x00);
    b.extend_from_slice(wots_pk);
    sha512(&b)
}

/// Domain-separated internal-node hash of two children.
fn node_hash(left: &[u8; N], right: &[u8; N]) -> [u8; N] {
    let mut b = Vec::with_capacity(1 + 2 * N);
    b.push(0x01);
    b.extend_from_slice(left);
    b.extend_from_slice(right);
    sha512(&b)
}

/// The one-time WOTS seed for leaf `i`, derived from the master seed (domain-separated from WOTS's own
/// per-chain derivation).
fn leaf_seed(seed: &[u8; N], i: u32) -> [u8; N] {
    let mut b = Vec::with_capacity(N + 5);
    b.extend_from_slice(seed);
    b.push(0x02);
    b.extend_from_slice(&i.to_be_bytes());
    sha512(&b)
}

fn build_levels(leaves: &[[u8; N]]) -> Vec<Vec<[u8; N]>> {
    let mut levels = alloc::vec![leaves.to_vec()];
    while levels.last().map(Vec::len).unwrap_or(0) > 1 {
        let cur = levels.last().unwrap();
        let mut next = Vec::with_capacity(cur.len() / 2);
        for pair in cur.chunks(2) {
            next.push(node_hash(&pair[0], &pair[1])); // leaf count is 2^height, so pairs are complete
        }
        levels.push(next);
    }
    levels
}

/// A stateful many-time Merkle key. The public value is [`MerkleKey::root`]; keep the whole struct
/// secret (it holds the seed) and let it track which leaf to use next.
pub struct MerkleKey {
    seed: [u8; N],
    pub height: u32,
    pub root: [u8; N],
    next: u32,
    leaves: Vec<[u8; N]>,
}

/// A many-time signature: which leaf signed, the WOTS signature, and the authentication path to the root.
///
/// `Clone`/`Debug`/`PartialEq` so callers can store, log and compare signatures — an attestation type
/// that wraps one needs all three, and a signature is public data, so there is nothing to protect.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MerkleSig {
    pub index: u32,
    pub wots: pqsig::Signature,
    pub path: Vec<[u8; N]>,
}

impl MerkleKey {
    /// Generate a key with `2^height` one-time leaves. Cost is `2^height` WOTS keygens — keep `height`
    /// modest (≤ ~12).
    ///
    /// **`height` above [`MAX_HEIGHT`] is a caller error and panics** (in a release build the shift
    /// masks instead, and the tree that comes back is wrong rather than absent). Stated here rather
    /// than left to be discovered: unlike [`capacity`](MerkleKey::capacity) and [`verify`], keygen has
    /// no honest total answer to give — a 2^32-leaf tree is not something it can decline to build and
    /// then pretend it built.
    pub fn keygen(seed: &[u8; N], height: u32) -> MerkleKey {
        match MerkleKey::try_keygen(seed, height) {
            Some(k) => k,
            None => panic!(
                "MerkleKey::keygen: height {height} exceeds MAX_HEIGHT ({MAX_HEIGHT}); \
                 use try_keygen for a total form"
            ),
        }
    }

    /// [`keygen`](MerkleKey::keygen) without the panic: `None` when `height` exceeds [`MAX_HEIGHT`].
    ///
    /// The panicking form stays because a `MerkleKey` return type has no honest way to say "I did not
    /// build a tree", and clamping would hand back a key of a height the caller did not ask for and
    /// will publish a root for. What was missing was any total path at all, so a caller computing a
    /// height — from a config file, a peer, a capacity estimate — had no way to ask the question
    /// without risking the process. That is now this function, and `keygen` is its unwrap.
    ///
    /// The bound is the only thing checked, deliberately. A height inside it is merely expensive
    /// (`2^height` WOTS keygens); a height outside it is not slow, it is **wrong** — `1u32 << 32`
    /// panics under `debug-assertions` and masks to `1u32 << 0` in a release build, so the release
    /// answer was a one-leaf tree wearing the label of a 2^32-leaf one.
    pub fn try_keygen(seed: &[u8; N], height: u32) -> Option<MerkleKey> {
        if height > MAX_HEIGHT {
            return None;
        }
        let n = 1u32 << height;
        let mut leaves = Vec::with_capacity(n as usize);
        for i in 0..n {
            let wots_pk = pqsig::keygen(&leaf_seed(seed, i));
            leaves.push(leaf_hash(&wots_pk));
        }
        let root = build_levels(&leaves).last().unwrap()[0];
        Some(MerkleKey {
            seed: *seed,
            height,
            root,
            next: 0,
            leaves,
        })
    }

    /// Whether `height` still agrees with the leaves this key was actually built from.
    ///
    /// [`height`](MerkleKey::height) is a **public field**, so a caller holding a key can set it to
    /// anything, and every one of this type's other methods derives its behaviour from it. This is the
    /// one predicate that says whether that has happened.
    pub fn is_consistent(&self) -> bool {
        self.height <= MAX_HEIGHT && self.leaves.len() == 1usize << self.height
    }

    /// Number of signatures already produced.
    pub fn used(&self) -> u32 {
        self.next
    }
    /// Total capacity (`2^height`).
    ///
    /// Saturates rather than shifting out of range: `1u32 << height` panics under `debug-assertions`
    /// for `height >= 32` and silently masks the shift in a release build, so the plain shift gave
    /// two different wrong answers depending on the profile. `MAX_HEIGHT` is the real ceiling —
    /// beyond it there are no leaves to have a capacity of.
    pub fn capacity(&self) -> u32 {
        1u32.checked_shl(self.height).unwrap_or(u32::MAX)
    }

    /// Sign the next message. Returns `None` once every leaf has been used (never reuse a leaf), and
    /// `None` for a key whose [`height`](MerkleKey::height) no longer matches its leaves.
    ///
    /// # The desynchronised height, which was neither refused nor survivable
    ///
    /// `height` is a public field. Raise it on a key `keygen` built, and `capacity()` — which is
    /// `1 << height` and nothing else — grows past the number of leaves that exist. `sign` then
    /// walked past the end of level 0 (`lv[(idx ^ 1) as usize]` at an `idx` beyond `leaves.len()`) and
    /// **panicked with an index out of bounds**, inside the signer, from a field assignment.
    ///
    /// Lowering it is quieter and no better: the authentication path is built by
    /// `levels.iter().take(self.height)`, so a short `height` yields a short path, `verify` folds
    /// fewer levels than the tree has and never reaches the published root. The key would have
    /// emitted signatures that cannot verify, one per call, with no error anywhere.
    ///
    /// So the check is [`is_consistent`](MerkleKey::is_consistent) rather than a bound on `height`:
    /// both directions of the desynchronisation are wrong, and neither is something a signature can
    /// be produced across. `capacity` and `verify` are total under the same abuse.
    pub fn sign(&mut self, msg: &[u8; N]) -> Option<MerkleSig> {
        if !self.is_consistent() {
            return None;
        }
        if self.next >= self.capacity() {
            return None;
        }
        let index = self.next;
        self.next += 1;
        let wots = pqsig::sign(&leaf_seed(&self.seed, index), msg);
        let levels = build_levels(&self.leaves);
        let mut path = Vec::with_capacity(self.height as usize);
        let mut idx = index;
        for lv in levels.iter().take(self.height as usize) {
            path.push(lv[(idx ^ 1) as usize]);
            idx >>= 1;
        }
        Some(MerkleSig { index, wots, path })
    }
}

/// Verify a many-time signature against the published `root` and tree `height`. Recovers the leaf WOTS
/// public key, then folds the authentication path up to a root and checks it equals `root`.
///
/// A `height` above [`MAX_HEIGHT`] is refused rather than shifted. No honest signature is lost — such
/// a tree cannot be generated — and the alternative was `1u32 << height` panicking under
/// `debug-assertions`, which turns a rejected signature into a crashed verifier.
pub fn verify(root: &[u8; N], height: u32, msg: &[u8; N], sig: &MerkleSig) -> bool {
    if height > MAX_HEIGHT || sig.path.len() != height as usize || sig.index >= (1u32 << height) {
        return false;
    }
    let leaf_pk = match pqsig::pk_from_sig(msg, &sig.wots) {
        Some(pk) => pk,
        None => return false,
    };
    let mut node = leaf_hash(&leaf_pk);
    let mut idx = sig.index;
    for sib in &sig.path {
        node = if idx & 1 == 0 {
            node_hash(&node, sib)
        } else {
            node_hash(sib, &node)
        };
        idx >>= 1;
    }
    node == *root
}
