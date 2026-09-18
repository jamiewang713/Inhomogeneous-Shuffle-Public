# Actual profile-fibre entropy: supplemental contract

Status: FROZEN at 2026-09-17T21:38:13.059821+00:00, after three independent exact-document approvals. No implementation existed at freeze.

This supplements the three existing immutable contracts without changing any definition, assumption or theorem in them. The mathematical sources are the three user-authorized files. The source target of this bridge is the within-class entropy bound used in the first-moment proof. This is a deterministic counting result, not an edge-density or localization assertion.

Implementation file: `FirstMomentModel/ProfileFibreEntropy.lean`. Namespace: `InhomogeneousShuffle.FirstMoment.Model`. Exactly the following two definitions and four exported theorems are planned. Auxiliary sets, maps, injections and intermediate facts may be local to proofs. No additional scientific hypothesis, finiteness hypothesis, count-compatibility hypothesis or axiom is permitted.

## Definitions

1. `profileKeyCounts`, for arbitrary natural `K,k,qb,qe,c` and `key : ProfileKey K k qb qe (c*k)`, is the function `Fin c -> Fin k -> Nat` given by

   `fun a l => (key.2.2.2.1 (finProdFinEquiv (a,l))).val`.

   It reads the existing flattened count vector exactly, without altering the key or rounding any stored count.

2. For the existing model `D : Riffle.Model`, setup `A : Riffle.Setup D`, natural `c`, data `cell : Fin D.K -> Fin c`, `good : Fin D.K -> Nat -> Prop`, `alpha : Real`, `route : ProfileWord A good alpha -> Fin 4`, and

   `key : ProfileKey D.K D.k (boundaryBudget A) (exceptionalBudget A alpha) (c*D.k)`,

   `ProfileFibre A cell good alpha route key` is exactly the subtype

   `{p : ProfileWord A good alpha // encodeProfile A cell good alpha route p = key}`.

   The previous real exceptional cutoff, admissible pair and actual stable membership remain inside `ProfileWord`. No independent legality or retention field is added. The key need not be realized.

## Exhaustive theorem interfaces

Each theorem has only the universally quantified definition data above. No extra hypothesis is implicit in the descriptions below.

PF1. `profileKeyCounts_encode`: for every `p : ProfileWord A good alpha`,

`profileKeyCounts (c := c) (encodeProfile A cell good alpha route p) = goodDigitCount A cell good p.val.1 p.val.2.1 p.val.2.2`.

The conclusion is equality of functions on the cell/digit pair, not only equality of their sums.

PF2. `profileFibre_finite`: for every key of the specified type,

`Finite (ProfileFibre A cell good alpha route key)`.

Finiteness is a proved conclusion. It is not assumed as a typeclass premise, and the totalized value of `Nat.card` on infinite types cannot substitute for this result.

PF3. `profileFibre_card_le_exp_entropy`: for every such key,

`(Nat.card (ProfileFibre A cell good alpha route key) : Real) <= Real.exp (typeEntropy (profileKeyCounts (c := c) key))`.

Here `typeEntropy` is exactly the existing frozen natural-count entropy. The bound has no asymptotic or exceptional-label loss.

PF4. `profileFibre_card_le_rpow_entropy`: for every such key,

`(Nat.card (ProfileFibre A cell good alpha route key) : Real) <= (D.N : Real) ^ (typeEntropy (profileKeyCounts (c := c) key) / Real.log (D.N : Real))`.

The power is the real power. The equality converting the right-hand side of PF3 to this expression uses only `D.one_lt_N`. No separate positive logarithm, positive alphabet or entropy sign hypothesis is added; the model already has `N>1` and `k>=2`.

## Proof obligations and source identification

For a nonempty fibre, choose a witness inside the proof. Equality of its key with any other element supplies equal boundary words, stable lengths, exceptional sets and exceptional labels by the proved `encodeProfile_eq_data`. The common free positions are precisely the positions after the common boundary join and before that common stable length, excluding the fixed exceptional set. Even when `good` depends on the digit, equality of the exceptional sets makes this the good-position set for each word in the fibre.

Stable membership gives legality and the common join prefix by `Riffle.stable_desc` and `Riffle.admissiblePair_rawPair`. Restricting a word to the common free positions, and reindexing their finite set by `Fin` of its cardinality, maps the actual fibre into the existing `typeClass` with the exact stored natural counts. The map is injective: the prefix digits, exceptional digits and free digits reconstruct the whole stable word; the two boundary words are already fixed. This is injectivity of the restriction within one fibre, not injectivity of `encodeProfile` on all words.

Apply the existing `type_class_card_le_exp_entropy` on exactly those free positions. Do not count padded full-length words, charge exceptional labels twice, or infer count compatibility for unrealized keys. An empty fibre is finite and has cardinal zero; `exp` is positive for its arbitrary stored entropy. Empty continuations, terminal singleton words, empty cells, zero counts and negative exceptional cutoffs are included without additional premises.

The exponent in PF4 is the exact natural-count version of the source normalized entropy. Identifying it with another package's `TimeProfile.profileH` still requires the concrete cell-map, digit-count and normalization equalities. This contract does not postulate that identification. Exact `cL` may vary within a fibre and is not asserted constant. A routing function may further divide classes without requiring probabilistic routing correctness for this finite theorem.

All four theorems must compile and pass the standard-foundation audit. The three earlier freezes and the original TeX/PDF hashes must remain unchanged.
