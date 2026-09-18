# Independent algebra review of the profile-fibre implementation

Decision: **PASS**. `FirstMomentModel/ProfileFibreEntropy.lean` implements exactly the two definitions and PF1--PF4 in the frozen `PROFILE_FIBRE_CONTRACT.md`, with no extra assumptions or weakened conclusions.

Reviewed hashes:

- frozen contract: `fd6179e138a30c6c9c96f1ad2c13c8f8186258cfce6e2d994c86ed89035ceab2`;
- implementation: `afc20a05f07eda489a9219dec9012e815fc1b7a79a1edad3c90a53936843da3f`.

This is a source/interface/proof review. The root agent separately runs compilation and the standard-foundation dependency audit; this review does not claim to have rerun those checks.

## Definitions and statements

`profileKeyCounts` reads exactly the natural value of the stored vector coordinate indexed by `finProdFinEquiv (a,l)`. `ProfileFibre` is exactly the encoder-equality subtype of the actual `ProfileWord`, preserving its admissibility, Stable membership, and real exceptional cutoff.

All four theorems retain the frozen universally quantified model/setup, cell, good predicate, alpha, route, and word/key data. No nonempty-fibre, count-compatibility, finite-type, positive-alpha, regularity, or probability premise has been added. Arbitrary unrealized keys are still allowed.

## PF1 and genuine finiteness

PF1 proves the complete two-variable function equality by the inverse law of `finProdFinEquiv`. It does not merely compare total counts.

PF2 derives legality of each stable list from `stable_desc`. It maps each fibre element into the finite function type `Fin K -> Fin (k+1)`, storing its actual digits before the length and sentinel k afterwards. Equality of keys supplies equal boundaries and equal lengths; equality of padded functions then supplies all actual digits, hence the list, triple, and both subtype layers. `Finite.of_injective` proves actual finiteness. No use of the infinite-type zero convention for `Nat.card` occurs.

This padded function is used only to prove finiteness. It is **not** counted by the entropy argument, so the contract's restriction against charging fixed/padded positions is respected.

## PF3: exact free-position restriction

For an inhabited fibre, the proof chooses p0 internally and defines J as the positions from its literal boundary join to its stable length, excluding its exceptional support. The local `hJ` lemma proves for **every** fibre element p that J is exactly p's own good-position set in its extension interval. It uses equal boundaries, length, and exceptional support obtained from `encodeProfile_eq_data`; it does not assume goodness is independent of the digit.

The equivalence `J.equivFin.symm` enumerates precisely these positions. `restriction p` stores the actual legal digit at each enumerated position. The `hcounts` proof is a full finite-set bijection:

- a selected restricted index maps to its underlying Fin K position;
- the map is injective by the equivalence and subtype extensionality;
- every original good position with the prescribed cell/digit has its inverse under the equivalence.

It proves exact equality with the original natural `goodDigitCount`, including the conversion between equality of `Fin k` values and equality of their natural values. PF1 and the actual fibre equation then identify these counts with the supplied key counts. Thus each restriction lies in the correct existing `typeClass` on **J.card** positions.

The restriction injection reconstructs the original list at every in-bounds position through three cases:

1. Before the boundary join, the actual prefix from `stable_desc` and `digit_prefix` fixes the digit; equal boundary words identify the literal joins.
2. At an exceptional position, `encodeProfile_eq_data` supplies equality of the actual stored label.
3. At a remaining extension position, `hJ` puts it in J; the inverse equivalence and equality of restriction functions recover the digit.

`List.ext_getElem` then uses the already equal lengths, and subtype extensionality recovers the actual fibre element. The totalized `Riffle.digit` is unfolded only with the required in-bounds proofs. The proof does not infer encoder injectivity on the whole domain.

The resulting injection into the finite type-class subtype gives a genuine natural-cardinality inequality via `Finite.card_le_of_injective`. That mathlib theorem constructs finiteness of the source from the injection into its finite target; it does not exploit `Nat.card=0` for infinite types. The right-hand natural cardinal is explicitly converted to the finite-set cardinal before applying the existing `type_class_card_le_exp_entropy` theorem. Its required k>0 is derived from `D.two_le_k`.

The empty-fibre branch installs an actual `IsEmpty` proof, rewrites its cardinal to zero, and uses positivity of exp for the arbitrary stored entropy. It does not assume unrealized keys satisfy any count compatibility.

The final bound is exactly `exp(typeEntropy keyCounts)`, with no extra factor for fixed prefix positions, exceptional positions/labels, or routing data.

## PF4 and boundary cases

PF4 derives N>1 and nonzero log N from `D.one_lt_N`, rewrites real power to exp, cancels the logarithm, and applies PF3. The power exponent is exactly `typeEntropy keyCounts/log N`. No entropy sign premise or asymptotic error appears.

The proofs accommodate K=0, an empty continuation, J.card=0, unused or empty cells, zero counts, negative exceptional cutoffs, and unrealized keys without additional premises. Terminal and fallback words remain in the actual domain. In a realized empty-free-position fibre, the reconstruction gives at most one element; no extra word variation is hidden in proof fields. An arbitrary route can only split the fibre further.

Inspection found exactly the two frozen top-level definitions and four frozen top-level theorems. All enumerations, padded maps, restriction maps, cardinality equalities, and injectivity facts are proof-local. No extra exported theorem, `axiom`, `sorry`, or `admit` appears.

This bridge establishes the actual fibre cardinality bound. The later identification with `TimeProfile.profileH`, numerical estimates, and stochastic first-moment assembly remain separate tasks, as required by the frozen contract.
