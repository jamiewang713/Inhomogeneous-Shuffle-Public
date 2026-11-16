# Independent implementation audit: relative model and deck

I independently compared `Relative/Model.lean` and `Relative/Deck.lean` with `frozen_relative_contract.md`, read every definition and proof body, and checked the compiled signatures and axiom dependencies. I did not edit either implementation or any frozen artifact. I separately implemented and compiler-checked the assigned `Relative/Density.lean`; those checks are identified separately below and are not presented as an independent review of my own proofs.

**Verdict: the three definitions and R.01–R.07 match the freeze and correctly distinguish arbitrary-shift counting from actual ambient recentering. No hidden assumption, coordinate error, or extra declaration was found.**

## Model fidelity

`relativeInternalEdges` is exactly the filter of `range (N−1)` testing membership of `i+s` in the existing absolute edge set. It never applies unguarded truncated subtraction to absolute edges. `relativeEdgeDensity` is exactly the sum of squared membership probabilities for that set with the supplied sample-dependent shift. `ambientLeft` is exactly the cardinality of the strict-below-prefix filter of `range N`, with the existing list lexicographic order explicitly imported.

The offset has no added one, so it is the source's zero-based cut before the ambient cylinder. All three definitions have the frozen argument orders and no new probability, sorting, legality, or shift constraints. The Model file contains exactly these three declarations, without a new instance or alias.

## Deterministic theorem review

- **R.01:** filter membership supplies the exact fixed support, for every N, row map, target prefix, and shift.
- **R.02:** the zero-shift equality proves both membership directions, using addition by zero and the already proved absolute edge support. It neither assumes nor asserts equality for nonzero shifts.
- **R.03:** the map i↦i+s is proved to send every relative edge to an absolute edge, and natural addition cancellation proves injectivity. Its conclusion is only the frozen cardinality inequality, with no bound on s or sorting premise.
- **R.04:** the ambient cut's cardinality is bounded by the full range N. This is valid for arbitrary rows and permits an empty cylinder whose cut equals N.
- **R.05:** the proof locally converts the strict comparison with [] into `List.Lex` and excludes that relation by the trusted empty-right lex theorem. Thus the root offset is proved to be zero for all rows, without relying on an incompatible list-order instance or an added order premise.
- **R.06:** internal-edge membership supplies the valid natural row index and target-prefix membership. Prefix transitivity gives an ambient-prefix witness. The proof explicitly handles an empty appended suffix by equality and a nonempty suffix by the trusted lexicographic append theorem, deriving the needed weak row comparison. For each row counted below the ambient prefix, it constructs valid `Fin N` indices from existing memberships and applies the already proved sorting monotonicity. The contradictory case i≤j is ruled out, so the counted set is contained in range i. No sorting, containment, legality, common-row-length, hn, or positive-N premise is supplied externally.
- **R.07:** the arbitrary-shift injection gives one cardinality inequality. For the reverse, each absolute edge j is mapped to j−s only after R.06 proves s≤j. The proof verifies its relative support and uses `(j−s)+s=j` for membership. It proves injectivity by adding s back, again with the two derived lower bounds. This is exact preservation of all child internal edges under the computed ambient cut, including empty edge sets.

The Deck file contains exactly the seven frozen theorems. Every additional lexical comparison, row-index bound, and subtraction identity is a local proved fact. The natural-index adapters use the original `sortedRows` construction and its original row permutation; no substitute sort or residual population is introduced.

## Empty cases and source meaning

N=0 and N=1 require no new assumptions: their edge ranges are empty. In R.06 an edge membership premise rules out an invalid index before a `Fin N` value is constructed. R.07's injections and inverse bounds do not select an element from an empty set. Empty or absent cylinders, overlong arbitrary list prefixes, sorting ties, empty words, and empty matrix columns are all covered by the literal formulas and existing data types.

Arbitrary shifts may discard edges before their cut, exactly as R.03 permits. For actual sorted matrices and the stated list-prefix relation, R.06 excludes those discarded child edges and R.07 establishes no loss. The source's one-based left endpoint minus one is therefore the correct implemented offset. This justifies shifting the entire internal graph; it does not identify its squared location-probability density or two-copy overlap with the absolute versions.

The source's vector prefix relation implies the list-prefix relation used here through the existing finite-list representation. The frozen upper-bound wrappers need no separate containment assumption because their inequalities hold for every shift; the no-loss branch supplies the actual ambient graph interpretation independently.

## Independent verification and assigned density checks

Building `EdgeLocalization.Relative.Density` completed successfully at default limits and checked the current Model/Deck dependency chain. A separate Lean import checked the full signatures of all three definitions and all seven Deck theorems. Their `#print axioms` results contain only `propext`, `Classical.choice`, and `Quot.sound`. A declaration/source scan found precisely the frozen inventory and no `axiom`, `sorry`, `admit`, unsafe declaration, or unproved placeholder.

My assigned Density implementation contains exactly R.08–R.13 and compiled on its first build at default limits. Separate complete-signature and axiom queries confirmed their frozen domains and only those same trusted foundational dependencies. R.08 and R.09 compare expected relative cardinality with the expected absolute edge count or occupancy; R.12 uses the already proved expected-edge bound and a justified nonnegative square comparison. No relative≤absolute density comparison is used. R.11 evaluates each copy's shift at its own outcome, and R.10 claims density equality only for the zero shift. These are implementation checks; independent review of Density is left to the other agents.

The accepted finite coordinate and counting results do not prove the printed spatial −c_F improvement, endpoint windows, stable localization, a conditional exploration law, or global first-moment aggregation.
