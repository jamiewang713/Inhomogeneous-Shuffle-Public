# LB-03 exact and residual factorial implementation delivery, v1

Status: **CHECKED**. The concrete arbitrary joint factorial identity and prescribed/deleted-row identity are implemented without a dependency on any LB-01 or LB-02 declaration.

## Exported declarations

```lean
RiffleLowerV2.Factorial.exactJointFactorial :
  RiffleLowerV2.Targets.ExactJointFactorial

RiffleLowerV2.Factorial.residualJointFactorial :
  RiffleLowerV2.Targets.ResidualJointFactorial
```

These are the exact unchanged frozen target types. The first is in `RiffleLowerV2/Factorial/Exact.lean`; the second is in `RiffleLowerV2/Factorial/Residual.lean`.

The additional first-moment bridge, also in `Residual.lean`, has the following type inside namespace `RiffleLowerV2.Factorial` with `TimeProfile` open:

```lean
theorem conditional_wordCount_eq_residualWordMean {k N K b : ℕ}
    (cuts : Cuts k N K) (p : RowPrescription N k K b) (hb : b < N)
    (hp : Function.Injective p.row)
    (hprob : 0 < probability (fixedCountPMF cuts) (prescriptionEvent p))
    (w : Word k K) :
    conditionalExpect (fixedCountPMF cuts)
      (fun ω => ((wordCount w ω -
        (Finset.univ.filter fun q => p.word q = w).card : ℕ) : ℝ))
      (prescriptionEvent p) = Targets.residualWordMean cuts p w
```

Thus the residual numerical expression is identified with the actual conditional expected deleted-row occupancy; the identity is a proved output, never an assumed moment premise.

## Proof/dependency ledger

| Ingredient | Status and implementation |
| --- | --- |
| Count color-preserving embeddings | Checked `coloredEmbeddingsEquiv`, `coloredEmbeddings_card`, and `coloredEmbeddings_natCard` in `Requests.lean` |
| Product falling factorials equals disjoint ordered row requests | Checked `groupedEmbeddingsEquiv` and `factorialProduct_eq_requests`; full-word injectivity is used to prove global row injectivity |
| Canonical one-column request probability | Checked `column_request_probability` in `Exact.lean`; uniform assignment invariance under row permutations and embedding double counting |
| Canonical independent-column product | Checked `request_column_product`, derived from the shared canonical average adapter and finite product/sum identities |
| Arbitrary concrete joint factorial identity | Checked `request_probability` and `exactJointFactorial` |
| Positive prescription gives valid residual counts | Checked local `prescription_exists`, `residual_count_eq`, `residual_cuts_exists`, and `residual_balance` |
| Actual conditional law is the residual matrix law | Checked restriction/gluing equivalence and `residualConditionalExpect`; no law axiom or asserted moment family |
| Natural subtraction is genuine deletion | Checked local `residual_word_count` on the conditioning event |
| Exact residual factorial formula | Checked `residualJointFactorial`, specializing the exact theorem on the transported residual sample |
| Conditional residual order-one mean | Checked `conditional_wordCount_eq_residualWordMean` |
| Uniform quantitative original/residual estimates | Owned by the numerical implementer; these exact modules are the concrete probability inputs |
| Consolidated axiom closure/compiled target inventory | To be recorded by the root coordinator's single final all-export audit; this report does not substitute source inspection for that audit |

The source correspondence is the labelled-row calculation in `lem:fixed-column-factorial`, plus the explicitly assigned residual extension and the residual mean identity used before `eq:collision-conditional-stability`. These results by themselves do not claim occupancy approximation.

## Edge cases and hypothesis preservation

The exact export preserves full-word injectivity and the frozen total-order domain `R≤N`, with no positive-pile assumption. The underlying embedding identity also works when no embeddings exist. Empty request types, empty products, `R=0`, and `K=0` are handled by finite cardinal/product identities.

The residual export preserves `b<N`, row-map injectivity, positive prescription probability, distinct tested words, and `R≤N-b`. Repeated prescribed words are allowed. The complete-word occupancy subtraction occurs only through a proof on the prescription event; no unjustified cast of natural subtraction is used. The conditional mean bridge uses residual order one and the positivity `N-b≥1` furnished by `b<N`.

## Build and imports

Successful command, run from `formalization/lower_bound_v2`:

```text
python3 scripts/lane.py LB03 RiffleLowerV2.Factorial.Residual
```

Result: `LB03 BUILD_OK`, recorded in `audit/LB03/exact_build_08.log`. This rebuilt all owned dependencies in `.build/lanes/LB03/lib/lean` and checked both target declarations and the conditional mean bridge. Earlier numbered logs retain development failures and are not certification receipts.

Downstream numerical wrappers should import `RiffleLowerV2.Factorial.Exact` and `RiffleLowerV2.Factorial.Residual`. The local graph is `Requests → Exact → Residual`, with `Basic` also imported by `Exact`. No sibling implementation lane is imported. The frozen shared definitions, contract files, compiler pins, manuscript, and original packages were not edited.

## Provenance and resolved implementation findings

`Requests.lean` and the arbitrary mixed-moment counting proof in `Exact.lean` are new implementations using pinned mathlib cardinality and permutation-extension APIs. The elementary canonical product-average calculation follows the same finite sum/product identity as the shared model foundation; it uses no sibling theorem.

The residual restriction/gluing construction was source-ported from the existing direct proof in `RiffleLowerV2/Thinning/Residual.lean`, rebuilt independently in the factorial namespace against local expectation helpers. Exact source SHA-256, destination hashes, source declaration range, adaptations, and successful log hash are preserved in `exact_residual_provenance_v2.json`; the earlier pending provenance v1 is retained unchanged.

Compiler differences between generic classical equality and native finite equality caused instance mismatches in fiber cardinalities. The resolved design provides an instance-independent `Nat.card` version of the generic counting theorem and a `DecidableEq` parameter for generic count splitting. Potentially recursive unrestricted simplification of subtype cardinality/sums was replaced with explicit finite-sum rewrite lists. Neither issue changed the mathematical theorem, hypotheses, or conclusion.

The independent pre-proof representation report remains `representation_review_v1.md`. A subsequent independent mathematical/quantifier review of the numerical implementation is recorded in `exact_numerical_review_v1.md` and found no substantive issue.
