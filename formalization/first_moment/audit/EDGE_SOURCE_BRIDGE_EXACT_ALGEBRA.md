# Edge-to-source identities: exact algebra sign-off

## Decision

I approve the exact candidate `audit/EDGE_SOURCE_BRIDGE_STATEMENTS.md`, SHA-256

`a94791b91adafcc3ed3f2b347a7cdfa8d4fcc770ff69c0b9ad11f6243fb751ed`.

Its one definition, all ten ES1–ES10 interfaces, and all five proof-local schemas are correct as written. No assumption, binder, endpoint, coefficient, or conclusion correction is needed. This report is a pre-freeze review only; no implementation or frozen file was changed.

The independent broad reconstruction is in `EDGE_SOURCE_BRIDGE_ALGEBRA.md`. I compared this exact candidate with the authorized TeX's ambient and tail definitions (lines 490–516), literal EdgeLocalization collision and exponent definitions, and the proved `StableNumericalBridge`. The candidate uses the original finite definitions and their exact count array, without a graph-law identification.

## Definition and common types

`prefixVector x hx` is exactly the restriction of `legalVector x hx` through `Fin.castLE hx.1`, with domain `Fin x.length` and codomain `Fin D.k`. No padding coordinate lies in this domain. The definition contains no new legality, positivity, or horizon premise.

The implicit D for ES1–ES8 is determined by `Riffle.Legal D x` or `Riffle.Setup D`. ES9 and ES10 explicitly bind D instead, as the candidate specifies. The count array throughout is literally `(asCuts D).count`. Its finite dimensions and coordinates match the EdgeLocalization inputs, and its column totals are already proved in `asCuts`. No redefined or approximately equal array is substituted.

## Exact theorem checks

**ES1 — `prefixVector_digit`: approved.** Apply `legalVector_digit x hx` at `Fin.castLE hx.1 t`. The cast preserves t.val, and t.isLt gives the exact required inequality before x.length. The padding branch is irrelevant. The conclusion identifies natural digit values, which is the useful form for the later list and count expressions.

**ES2 — `prefixVector_word`: approved.** `prefixWord` is `List.ofFn` of the finite digit values. Its length is x.length. Entrywise, ES1 identifies each value with `Riffle.digit x i`, and the in-range definition of that digit gives the corresponding list element. List extensionality yields literal equality. No cylinder-event equivalence, sorting property, or probability assumption is substituted for this exact list statement.

**ES3 — `prefixVector_legal`: approved.** Unfolding the existing natural-count legality predicate and `asCuts.count`, the target at t is `0<D.n t.val (prefixVector x hx t).val`. By ES1 this is precisely the positive-count component of `hx.2 t.val t.isLt`. The proposal correctly uses natural pile positivity on actual coordinates. It needs no full-support premise and makes no claim that the padded suffix of `legalVector` is legal.

**ES4 — `prefixVector_ambient`: approved.** The cast from `Fin A.w.length` to `Fin x.length` uses `hprefix.length_le`, derived from the displayed prefix relation. Applying `Fin.ext` and ES1 on both sides reduces the target to `digit x t.val = digit A.w t.val`. This is the reverse of the already proved `Riffle.digit_prefix hprefix t.isLt`. The ambient legality proof is exactly the existing `A.w_legal` field. The two composed casts to the model's horizon have the same value; their proof fields do not add a mathematical condition.

**ES5 — `edge_ambientSizeExponent_eq`: approved without an ambient-prefix premise.** Reindex the finite set of `t : Fin x.length` satisfying `A.w.length≤t.val` by t.val onto `Finset.Ico A.w.length x.length`. Injectivity is finite-value extensionality. A target interval index has the strict upper bound needed to construct its inverse finite coordinate. ES1 and the literal `asCuts.count` definition identify the summands. Both expressions retain exactly A.b and divide the same sum by `log D.N`. No logarithm transformation is required. If the ambient length exceeds x.length, both sums are empty and both sides equal A.b. The absence of `A.w<+:x` is therefore deliberate and valid.

**ES6 — `edge_prefixMean_source_eq`: approved.** For each finite column and digit, `singleFactor D.N ((asCuts D).count j) l` and `TimeProfile.prob (asProfile D j) l` both reduce to the same count divided by D.N. Map `t : Fin x.length` to `Fin.castLE hx.1 t`. This is a bijection onto `TimeProfile.positions D.K 0 x.length`: the inverse is the same natural coordinate equipped with the strict bound from position membership. The vector values agree by the proposed restriction definition. Thus the two product expressions agree, and multiplying by the same N gives the result. It is essential that the left side is `prefixMean`; EdgeLocalization's `prefixMass` alone would be missing N. No mean approximation, logarithm identity, or distributional equality is used here.

**ES7 — `edge_prefixMean_expectedCount_eq`: approved.** ES6 gives the source product mass. The existing `expectedCount_cylinder_eq x hx x List.prefix_rfl` has the opposite equality between the actual real-coerced weighted count and that product mass. Compose the two equalities. This theorem requires only x and hx. It does not assume the expectation of an arbitrary probability law or reprove a sample-law equivalence.

**ES8 — `edge_ambientMeanError_eq`: approved.** Apply ES7 to the actual ambient word A.w and its existing legality proof, then unfold the existing `ambientMeanError`. This yields precisely the signed expression in the statement, with no continuation word or prefix premise. The expected-count coercion is from `NNReal` to `Real`, exactly as in the proved cylinder identity. For an empty ambient word, the population is N and `log N/log N=1` because the model gives N>1, so the signed error is `1-A.b`, as the candidate says. Neither zero nor nonnegativity of this error is asserted.

For a later continuation x, the existing `ambientApproximation_iff` identifies the source approximation with the absolute value of ES8's right side. This yields the required upper bound eb when that approximation is supplied. Keeping ES8 in actual expected-count form therefore avoids a redundant continuation/prefix premise and loses no needed integration fact. The inequality proofs in later EdgeLocalization applications may use `hprefix.length_le.trans hx.1` in place of `A.w_legal.1`; both are proofs of the same length proposition and the finite casts are unchanged by proof irrelevance.

**ES9 — `edge_columnPsiTwo_eq`: approved.** The literal single-factor/profile-probability equality identifies every base. The trusted real-power identity at natural exponent two identifies the source power with the natural square, including base zero. Finite sum congruence and application of the same negated logarithm prove the result. No positive-coordinate premise, division by a pile probability, or logarithm of an individual zero pile is introduced. Explicit D and `j : Fin D.K` provide all required indices.

**ES10 — `edge_tailEdgeExponent_eq`: approved for every natural M.** The EdgeLocalization support `univ.filter (M≤j.val)` equals `TimeProfile.positions D.K M D.K`, since the latter's upper bound is already j.isLt. Filter extensionality proves this for any M, not only for M≤D.K. Rewrite the summands by ES9 and unfold `logScale`; the sign and denominator agree. At or beyond the horizon both sums are empty, giving zero. This correctly identifies the square-sum exponent, not the factorial two-row collision probability.

## The five proof-local schemas

All five are approved, with no additional exported helper required beyond the candidate's ten statements.

1. The cast/digit/ofFn schema gives ES1–ES3 directly. Its only digit positions are strictly below the actual length, so suffix padding and out-of-range default digits do not enter any equality.
2. The prefix and interval-sum schema gives ES4–ES5. In the interval reindexing, the natural index's upper bound constructs the finite inverse. No lower-before-upper premise is missing: empty intervals satisfy the same equality.
3. The probability/product schema gives ES6. Both products have the factor N after unfolding their respective mean definitions. The already proved cylinder identity gives ES7, and the signed-error definition gives ES8 without new logarithmic assumptions.
4. The natural-square/real-power schema gives ES9 for the literal nonnegative probabilities, including zeros. The finite sum and logarithm are applied only after proving equality of their inputs.
5. The filter equality and ES9 give ES10 for arbitrary lower endpoints. No claim that squared one-row probabilities equal two-row sampling-without-replacement probabilities is made.

## Edge cases and scope

Empty words and K=0 use empty products equal to one, so both means equal N. Full-length words are included with the identity finite cast. The cL identity permits an ambient length larger than the word length, whereas the separate mean-extension/density application will use ES4's genuine prefix relation. Tail lengths larger than K give empty sums. Zero piles outside the legal prefix remain allowed, and all selected prefix piles have positive integer counts from hx.

No identity requires AlmostLike, regular partitions, source error bounds, a horizon floor, stability, admissibility, a variational inequality, or asymptotic ambient normalization. These remain later application inputs. The new finite representation does not change existing frozen word or profile definitions.

ES6–ES8 establish exact deterministic mean/expected-count identities using already proved finite expectations. ES2 establishes a literal prefix-list identity. None of these statements equates `matrixLaw` with another sample measure, changes sorting/rank conventions, or identifies two graph event definitions. Such law and graph work remains separate if the final assembly requires it. The stated scope and all ten exact interfaces are approved for freezing.
