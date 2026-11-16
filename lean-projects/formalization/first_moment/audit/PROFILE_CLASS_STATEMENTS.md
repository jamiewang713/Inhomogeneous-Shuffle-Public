# Independent profile-class statement-design sign-off

Reviewed the exact proposed `PROFILE_CLASS_CONTRACT.md` on 2026-09-17, after independently rereading the authorized unified TeX's space-time profile definition, truncation/counting argument, and final first-moment class decomposition. Relevant current project Lean and trusted mathlib finite-type interfaces were also inspected.

**Decision: approve without corrections.** This approves the exact six definitions and P1–P4 for the root agent's freeze procedure. It does not itself freeze or implement them. Both earlier frozen contracts remain unchanged.

## Definitions

The actual domain is the existing admissible boundary pair together with an actual stable word and the literal real exceptional cutoff. No legality, retention, finite-type, or integer-budget premise is added. `Riffle.stable_desc` and `Riffle.admissiblePair_rawPair` supply legality when constructing stored digits and lengths. `Riffle.admissiblePair_retained` recovers the source's retained condition.

The extension interval is exactly `(join y z).length ≤ i.val < x.length`. It corresponds to the source's one-based interval after the boundary join, not merely after the ambient prefix. The natural counts and labeled exceptional assignment are the right finite data. Their dimensions and bounds are `c*D.k` coordinates, each in `Fin (D.K+1)`, with the stated `finProdFinEquiv` convention.

The real exceptional inequality must remain in `ProfileWord`, as specified. Its floor consequence is valid for every actual domain element by `Nat.le_floor`. Replacing the domain with the floor inequality would incorrectly admit zero-exception words for a negative cutoff; the exact contract excludes that change.

`ProfileClass` is the range subtype inside the frozen finite key type. This directly gives realized classes and avoids a false injection of individual stable words. The arbitrary `Fin 4` route is legitimate deterministic data for counting and is not asserted to satisfy a density classification.

## Theorem checks

* **P1:** The real bound in the domain yields the exact natural exceptional budget. No separate sign premise is needed.
* **P2:** Every good count is the cardinality of a filtered `Fin D.K`, so the unconditional upper bound `D.K` is valid even for arbitrary words and boundaries.
* **P3:** Boundary injectivity recovers the two original boundary words. The length and count vector give the exact stated equalities. Equality of the dependent sparse assignment gives equality of support and of the actual labels at every support position, not just cardinalities. The final field gives route equality. The absence of stable-word equality and exact-`cL` equality is necessary and correct.
* **P4:** Subtype projection embeds the realized class type into the existing finite `ProfileKey`. Finiteness is therefore derived, and the already proved frozen count gives exactly the displayed bound with dimension `c*D.k`. No finite enumeration of the word domain is assumed or needed for this class count.

## Edge cases and source limits

`K=0`, an empty continuation, and a terminal singleton give zero counts and empty exceptional support. A negative `alpha` leaves the real-budget domain empty. A budget above `K` is harmless because the existing sparse-count formula already includes zero binomial terms above `K`. No positive-cell-count premise is necessary: when `c=0`, the provided function `Fin K → Fin 0` already controls which instances of the universal statement can exist.

Labels at zero piles need no extra hypothesis, since actual stable words are legal. Arbitrary words in P2 need no legality because only the finite column support is counted. Empty or unused profile cells contribute zero count coordinates.

The source specialization must still identify the joint time/simplex cell map, the representative-mass good predicate, and the cutoff. Natural count equality then implies normalized count equality at the fixed `N`. The source's later explicit exceptional-value refinement supports the labeled key. Coarser source classes are projections of these realized refined classes.

The contract correctly leaves source routing correctness, discarded mass, within-class entropy, exact cost replacement, and the eventual small-exponent parameter choice to separate results. None is smuggled into the finite-count assumptions or conclusion.

No Lean code or contract was edited during this exact-document review. The independent interface analysis is available in `PROFILE_CLASS_INTERFACE_CANDIDATE.md`.
