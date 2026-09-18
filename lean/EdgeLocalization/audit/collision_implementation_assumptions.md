# Independent implementation assumptions audit: collision model

I independently inspected the implemented `Collision/FiniteLaw.lean`, `Collision/Column.lean`, and `Collision/Model.lean` against `frozen_collision_contract.md`, including its final signature conventions. I did not edit any implementation, frozen contract, source, or pre-freeze review. This review is independent of these files' implementation authors; my implementation ownership was the separate Rows module.

**Verdict: the three inspected modules faithfully implement their frozen definitions and statements. No additional mathematical assumption, assumed probability identity, or false independent-row substitution was found.**

## Actual law and definitions

- `FixedColumn N k n` is exactly the finite subtype of assignments `Fin N → Fin k` with the prescribed histogram. Its only subtype conditions are those count identities.
- `fixedColumn_nonempty` constructs a feasible assignment from an equivalence between `Fin N` and the disjoint union of the `Fin(n a)` fibers. It proves each histogram by an explicit finite bijection. Nonemptiness is derived from `sum n=N`, not an assumed constructor field.
- `FiniteLaw.uniform` has constant reciprocal-cardinality weights and proves normalization from the necessary nonempty finite domain. `columnLaw` obtains this domain condition by the proved nonemptiness theorem.
- `FixedColumn.reindex` proves histogram preservation for precomposition with a row permutation and supplies the actual inverse. Its use in probability arguments is justified by the proved uniform finite change-of-variables theorem.
- `FiniteLaw.pi` has the product of coordinate weights and proves normalization by finite product/sum factorization. Its signature has only the frozen finite types and their given normalized laws; it has no hidden independent-coordinate or nonempty-coordinate hypothesis.
- `FixedMatrix N n` is the dependent product of prescribed column assignments, and `matrixLaw n hn` is exactly the product of their constructed uniform laws. Columns are independent by construction and the proved event factorization. Rows are not taken independent. Repeated count vectors still correspond to different product coordinates, so they do not accidentally share one random permutation.
- The explicit `fixedMatrixFintype` uses the ordinary finite dependent-function enumeration with a classical equality decision instance. This is derived enumeration data matching the product constructor, not a probability assumption, a new axiom, or a population restriction.
- `prefixWord` and `rawRow n ω` use `List.ofFn` in coordinate order. The natural-index adapter has the frozen `[]` value only outside the actual row range. `rawRows n ω` uses that adapter without altering row data.
- All numerical factors retain explicit N. Prefix coordinates use `Fin.castLE hM`; the tail finset consists exactly of absolute times `j.val≥M`. Empty products are the ordinary product 1. `prefixMean` is the expression N times prefix mass; it does not assume its later expectation identity.
- The diagonal pair factor is the natural falling factorial n(a)(n(a)−1) divided by N(N−1), with natural subtraction cast to the reals. The off-diagonal factor is n(a)n(b) over the same denominator. Their definitions remain total when N≤1 exactly as frozen.

## Statement fidelity

| Frozen statements | Result of inspection |
|---|---|
| C.01–C.02 | Exact uniform event-cardinality formula and equivalence reindexing; no event-positivity condition or invariance assumption was added. |
| C.03–C.04 | Product-event formulas follow from the actual product weights. Restricted-coordinate events use true events outside the selected finset. Empty selections remain valid. |
| C.05 | The only additional premise is the frozen generic disjointness condition. It is used pointwise to show at most one alternative contributes. |
| C.06–C.08 | Exact feasible-column construction, derived pile bound, and deterministic histogram reindexing. No positive-pile or positive-alphabet premise was added. |
| C.09 | Ordered distinct label pairs are the finite off-diagonal set, with cardinality N(N−1), including the zero/single-label cases. |
| C.10 | The equal-digit case removes the diagonal from one fiber. The unequal-digit case uses the product of disjoint fibers and proves distinctness from a≠b. Both branches keep zero counts. |
| C.11 | The two-swap construction sends the first ordered pair to the second. The intermediate image of j is proved different from i′, so the second swap preserves the first target. The pairs need not be disjoint; reversal and overlapping labels are allowed. |
| C.12 | Column probability invariance is a consequence of the constructed uniform law and the constructed equivalence. |
| C.13 | One-label probabilities are identified by summing exchangeable marginals over all N labels and using the fixed histogram. Existence of the label supplies N>0 before division. |
| C.14 | Two-label probabilities are identified by summing over all ordered distinct labels and using C.10. The premise i≠j supplies N≥2 before the denominator is shown nonzero. The a=b and a≠b branches are explicit. |
| C.15 | Equal-digit probability is the disjoint union over actual alphabet digits of diagonal two-digit events. It sums only the diagonal pair factors. |
| C.16 | A zero pile makes its digit impossible pointwise for every row; this is proved from the empty histogram fiber. |
| C.40–C.41 | Nonnegativity holds for the total arithmetic factors without feasibility or positivity assumptions, as frozen. |
| C.42 | Exactly the frozen feasibility identity and N≥2 are used. Count zero is split off; for positive counts the natural-subtraction cast is justified by n(a)≥1, which also includes count one. The upper bound n(a)≤N is derived. No n(a)≥2 premise is introduced. |

All named declarations in these files are the planned constructors, two finite instances, and their allocated frozen theorems. There is no extra named project helper or unproved estimate standing in for a missing counting argument.

## Denominator and finite-case checks

The two-label averaging proof gives

```
N(N−1) * P(column_i=a and column_j=b)
  = n(a)(n(a)−1)       when a=b,
  = n(a)n(b)            when a≠b.
```

It sums over ordered distinct row labels. No factor 1/2 belongs in this marginal calculation. The later unordered collision count must supply `choose N 2`; that later expectation interface is outside these three files and is not assumed here.

- **N=0:** feasible counts are all zero, and the assignment domain is empty. The equivalence used for column existence handles empty types. There is no row label at which a marginal theorem could be instantiated. The uniform column law itself is nonvacuous: the unique empty assignment remains an outcome.
- **N=1:** there are no distinct row labels. C.14 cannot be instantiated with impossible distinct labels, and its proof derives N≥2 rather than cancelling a zero denominator. The single-row probability remains correct. Algebraic pair factors are zero because division is total; no two-row probability interpretation is claimed in this case.
- **k=0:** if a column is present, feasibility forces N=0 and the constructed assignment is the empty function. No default digit is chosen. The proofs quantified over a digit have no instance in the empty alphabet.
- **K=0:** the matrix sample is the unique empty dependent function, and the product weight is 1. All rows are empty words. The definitions require no nonempty alphabet, and prefix length M≤K forces M=0 in bounded prefix applications.
- **Zero/one piles:** the falling factorial gives zero exactly; the direct histogram argument remains valid. In particular, an occupied single row is not confused with an equal pair.
- **One pile of size N:** it is permitted. Its column is deterministic, and for N≥2 its diagonal coincidence factor is 1. No good-column or nondegeneracy condition has appeared.
- **Empty prefix/tail and zero products:** prefix mass/pair products and tail products use their frozen conventions. No division by a prefix event or tail coincidence factor occurs.
- **Arbitrary ambient or exploration conditioning:** these files make no such claim. N remains the original matrix population. A future residual-law or occupancy-conditioning result is not supplied by a hidden interface here.

## Verification and remaining scope

I independently ran Lean 4.24.0 on all three current source files. Each exited successfully with no errors or warnings. I also inspected their declaration inventory and checked the compiled axiom dependencies of all 19 allocated named theorems and the principal uniform/product/reindexing/column/matrix law constructors. Every dependency report contained only trusted `propext`, `Classical.choice`, and `Quot.sound`; there was no `sorryAx` or custom axiom. A source scan found no prohibited placeholder, axiom declaration, unsafe proof escape, or `native_decide` use.

There is no correction requested for the inspected code. The exact full-matrix uniform weight identity C.17, product prefix events, expectations, final density inequalities, and the independent audit of the sorting implementation belong to other allocated modules/reviewers. This report does not count those statements as verified merely from the soundness of the present model. Likewise, the optional occupancy-slice component, exponent conversion, spatial localization, and exploration-conditioned model remain outside the selected additive freeze.
