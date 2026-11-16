# Profile-fibre entropy: independent implementation audit

**Verdict: approve the implemented two definitions and PF1–PF4 against the frozen contract.** No changed assumption, hidden count-compatibility condition, nonemptiness premise, finiteness premise, or altered exceptional cutoff was found.

Reviewed snapshot:

- `PROFILE_FIBRE_CONTRACT.md`, frozen status dated 2026-09-17T21:38:13.059821+00:00, SHA-256 `fd6179e138a30c6c9c96f1ad2c13c8f8186258cfce6e2d994c86ed89035ceab2`.
- `FirstMomentModel/ProfileFibreEntropy.lean`, SHA-256 `afc20a05f07eda489a9219dec9012e815fc1b7a79a1edad3c90a53936843da3f`.

This is a source/interface and adversarial proof review. The coordinator is separately running the compiler and transitive foundation audit; I did not duplicate that active build or modify any Lean file, contract, or frozen prereview report.

## Exact interfaces

`profileKeyCounts` (lines 14–16) reads the existing flattened count vector using exactly `finProdFinEquiv (a,l)`. `ProfileFibre` (18–24) is literally the subtype of the existing `ProfileWord` whose existing encoder equals the supplied arbitrary key. In particular, actual admissible boundary pairs, stable membership, and the original real exceptional cutoff remain in the domain.

All four theorem binders match the contract. The file exports exactly these two definitions and four theorems; all auxiliary sets, functions, witnesses, and facts are proof-local. PF1 concludes equality of the full cell/digit count functions. PF2 concludes `Finite` rather than assuming it. PF3 uses `Nat.card` of the actual fibre and the exact stored natural-count entropy. PF4 has the same cardinal and the prescribed real power, with no extra logarithm, alphabet, or entropy-sign hypothesis.

## Finiteness is proved, not hidden

PF2 derives legality from actual stable membership, then sends a word to its length-`K` digit function with sentinel `k` beyond its legal length. Equal keys already supply the same boundary words and length; equal function values then reconstruct every actual list digit. This is a genuine injection into a finite function space (`Finite.of_injective`, line 70). It does not exploit the totalized value of `Nat.card` for an infinite type.

The padded representation appears only in this finiteness proof. PF3 does not count padded words or include a factor for their suffixes.

## Exact free-position injection

PF3 splits into empty/nonempty fibre cases inside the proof. In the nonempty case its common set `J` is precisely the half-open interval from the common join length to the common stable-word length, with the fixed exceptional set removed (87–90).

The equivalence `hJ` (91–117) proves separately for every fibre member that membership in `J` is equivalent to being in that member's continuation interval and having a good selected digit. It uses equality of exceptional supports, not an assumption that goodness is independent of the digit. Thus arbitrary `good : Fin K → Nat → Prop` is correctly handled.

The restriction to `J` is reindexed by `Fin J.card`. `hcounts` (125–150) is an actual bijection of the counted positions, preserving both the fixed cell map and actual digit. PF1 and key equality then put the restriction in the existing `typeClass` with exactly the key's counts. No compatibility of an arbitrary key is presumed, and no surjectivity onto the type class is required.

Injectivity (162–204) reconstructs the list in three exhaustive cases: digits before the join are fixed by the actual join prefix; exceptional digits use the explicit label equality from `encodeProfile_eq_data`; remaining digits are the restricted word. This expressly uses exceptional **values**, not merely positions. The resulting genuine injection into the finite type class justifies the cardinal inequality and the application of `type_class_card_le_exp_entropy` (205–220). Alphabet positivity is derived from `D.two_le_k` inside the proof.

## Degenerate cases and normalization

Unrealized keys take the empty-fibre branch, whose cardinal is zero and whose arbitrary entropy has positive exponential. The proof never asserts that an unrealized key has compatible or zero counts. A realized fibre with no free positions embeds into the unique empty function and has cardinal at most one. Terminal words, empty continuations/cells, zero counts, `K=0`, and negative exceptional cutoffs receive no new hypothesis; the real cutoff in `ProfileWord` is untouched.

PF4 uses only `D.one_lt_N` to obtain positive base and nonzero positive logarithm. `Real.rpow_def_of_pos` and cancellation prove the exact identity `N^(H/log N)=exp H` for the stored real entropy. No lower bound on `H` is required. The implementation does not assert the still-separate identification with `TimeProfile.profileH`, nor any constancy of exact `cL` within a fibre.

The static declaration/forbidden-token scan found no `axiom`, `sorry`, `admit`, `unsafe`, `partial`, `implemented_by`, opaque declaration, or additional exported helper. No correction is requested.

