# Independent Lean design review: exact expected masses

Status: comparison report for `EXPECTATION_EXTENSION_DRAFT.md`; no Lean implementation has been written for this new interface. All P01–P08 are approved as currently stated, with the dependency clarification below. No additional scientific assumption is needed.

## Source law and representation

I re-read the authorized 2510 extract at lines 397–419, the unified article at the matrix construction around lines 443–458 and the side-piece definitions around lines 605–638, and the 2103 extract's iid-string construction around lines 250–275. The fixed-count paper explicitly chooses uniformly among all matrices with the prescribed column counts. The iid-row construction of the earlier homogeneous paper must not be transferred to this law.

The proposed dependent product sample space is exact:

* `ColumnAssignments cuts j` is the subtype of functions `Fin N -> Fin k` whose fibers have the specified cardinalities.
* `ShuffleSample cuts := (j : Fin K) -> ColumnAssignments cuts j`.
* `fixedCountPMF cuts := PMF.uniformOfFintype (ShuffleSample cuts)` and `fixedCountMeasure cuts := (fixedCountPMF cuts).toMeasure`.
* `sampleEntry sample row col := (sample col).val row` and `sampleRow sample row := fun col => sampleEntry sample row col`.

Each subtype is finite. Its nonemptiness is a theorem from `cuts.sum_count`, proved before installing its `Nonempty` instance. Choose an equivalence `Fin N ≃ Sigma l : Fin k, Fin (cuts.count j l)` using equal cardinalities, and project to its first coordinate. Each fiber is equivalent to `Fin (cuts.count j l)`. The choice occurs inside the construction; there is no canonical-array datum supplied by the user and no premise that a sample space has the desired properties.

This works for all natural k,N,K, including N=0 and K=0. When k=0 and N>0, a cuts object can only have K=0; the dependent product is still a singleton. Probability formulas involving `cuts.profile hN` require N>0 exactly as stated in the draft. Source applications already have N>=2.

Use discrete measurable spaces on these finite types. All functions and events in this interface are measurable and integrable by finiteness. These are representation instances, not assumptions about an external stochastic process. A transpose-and-pack equivalence with the subtype of row-major fixed-count matrices can be implemented if useful for documentation; it should not become a new law hypothesis.

## Finite proof route

The useful primitive is the exact finite-average identity

`integral f d(uniformOfFintype A).toMeasure = (sum_a f a)/(Fintype.card A : Real)`.

For a finite nonempty type A, it follows directly from `PMF.integral_eq_sum` and `PMF.uniformOfFintype_apply`. The probability and integrability instances are supplied by the actual PMF on the finite discrete space. No integral formula is postulated.

For each column, precomposition by a row permutation is an equivalence of `ColumnAssignments cuts j`. Fiber cardinalities are invariant under a permutation. Its inverse is precomposition by the inverse permutation, with the usual reversal in the composition order. `Equiv.sum_comp` gives invariance of the finite average under this equivalence.

To prove a row marginal, first prove that its expected value of g is the same at every labelled row, using the transposition of the two row labels. Pointwise column-count conservation gives

`sum_row g(a row) = sum_l (cuts.count j l : Real)*g l`.

Average over all assignments and exchange the two finite sums. The left side is N times the common labelled-row expectation; divide by N using N>0. This proves the full real-function marginal directly, avoids factorial/multinomial enumeration, and automatically handles zero piles and arbitrary signed g.

For factorization, expand the uniform average over the dependent product and use `Fintype.prod_sum` together with `Fintype.card_pi`. The normalization factors because each column-assignment type is nonempty. This proves

`E(product_j F_j(sample j)) = product_j E_column_j(F_j)`

for arbitrary real F_j, including K=0. No row independence enters this argument.

For a fixed labelled row, write the indicator of box membership as the product of its column indicators. Factorization and the column marginal give the product of category probabilities. Summing this identity over labelled rows proves the box-count expectation. The last step only uses linearity of expectation, so dependence between rows is harmless.

Trusted library APIs verified for this route include `PMF.integral_eq_sum`, `PMF.uniformOfFintype_apply`, `PMF.toMeasure_uniformOfFintype_apply`, `Fintype.prod_sum`, `Fintype.card_pi`, `Fintype.card_sigma`, `Fintype.equivOfCardEq`, `Fintype.equivFinOfCardEq`, `Equiv.sum_comp`, and finite fiber-counting identities. These are enough without invoking a general independence framework.

## Predicate and observable definitions

For arbitrary row-word predicate B, define

`rowCount rows B := (univ.filter (fun i => B (rows i))).card`,

where `rows : Fin N -> (Fin K -> Fin k)`. Classical decidability is internal to the finite filter; it is not a new hypothesis on B. `boxRows`, `prefixRows`, and the two side-row sets can be defined as finite filters, with their cardinalities passed to the expectation as real casts.

For box data `A : Fin K -> Finset (Fin k)`, the predicate is `forall j, row j belongs to A j`.

For prefix x and length M, the predicate is `forall j, j.val<M -> row j=x j`. Later columns are unrestricted. Its box representation takes a singleton before M and the full digit set after M. Thus the box formula reduces to the existing `prefixMass` by `sum_prob` and the product over `positions K 0 M`.

For side column j, use the first j.val exact digits and then the strict inequality at j. The side box uses singletons at h<j, the lower or upper digit set at j, and the full digit set at h>j. There is no constraint on future entries, including the entries between j and a longer continuation endpoint M. Its mean is

`N*(product_{h<j} p_h[x_h])*(sum_{l<x_j} p_j[l])`

or the analogous upper-digit sum. Split the prefix product at w to obtain the existing `sideMass`, with the essential hypothesis w<=j.val. This is the unconditional expected count of global rows satisfying the ambient prefix and the side event. It is not a conditional expectation given the realized ambient subset or its size.

Every sampled row uses only positive-count digits: its own row label witnesses membership in the corresponding column fiber, whose cardinality is the prescribed count. This is a direct constituent of P01 count conservation and identifies these row predicates with the source's predicates restricted to legal strings. No full-support assumption is needed.

## Expected fluctuation exponent

For each side, define its expected maximum by the same `Real.toNNReal` and finite supremum representation as `sideMaximum`, replacing the deterministic side-mass expression at j with the integral of the corresponding side-row cardinality. Use the exact existing `positions K w v`; the empty supremum remains zero. Then define the expectation-based fluctuation exponent by the same square root, `logExponent`, and minimum construction as `cF`.

P06 identifies each term in this finite supremum because membership in `positions K w v` implies w<=j.val. The two maxima and the exponent are therefore equal to the old definitions. This holds when a side is empty, when the index set is empty, and when cF is bottom.

The definition must not use E[max_j count_j], E[sqrt(max_j count_j)], or E[random cF]. Those are different quantities. The source exponent is a deterministic function of the separate expected counts, which is exactly the draft's proposed interface.

## Row reindexing and sorting

For an arbitrary matrix and arbitrary predicate B on its complete row words,

`rowCount (fun i => rows (sigma i)) B = rowCount rows B`

follows by reindexing the finite sum of indicators or by a bijection of the filtered row sets. It is pointwise for every row permutation sigma. Hence it also holds when sigma is selected as an arbitrary function of the sample, and therefore holds for a lexicographic sorting permutation. No probabilistic independence of that permutation is required.

This only identifies cardinalities of the source row families; it does not establish graph localization or interval endpoints. Marginal-law statements must continue to refer to the unsorted labelled rows. For example, with one balanced two-row column, the first sorted digit is deterministic, even though either unsorted labelled row has the uniform marginal.

## Exact P01–P08 verdict and dependencies

| Item | Verdict | Dependencies and suggested public components |
|---|---|---|
| P01 | Approved | `columnAssignments_nonempty`, finite/nonempty instances for columns and samples, exact `sample_column_counts`, positive-count support as its direct consequence, probability-measure instance, `fixedCount_integral_eq_average`. Uses only cuts conservation and finite-type APIs. |
| P02 | Approved | `columnRowPermEquiv`; column-average invariance; `column_row_marginal` for real g; `sample_row_marginal` for real g; digit-event probability corollaries. Column part uses P01. Full-matrix part can use P03 below. |
| P03 | Approved | `fixedCount_integral_prod` for arbitrary real F_j. Uses only P01 and finite product-of-sums factorization. It does not depend on a marginal theorem. |
| P04 | Approved | `expected_box_count cuts hN A`. Uses P02 column marginal and P03, then finite linearity over rows. No legality or row-independence premise. |
| P05 | Approved | `expected_prefix_count cuts hN x hMK`; the exact cL/log expected-prefix identity using the existing D04 domain. Impossible prefixes are allowed in the first identity. |
| P06 | Approved | `expected_left_side_count cuts hN x j hwj`, `expected_right_side_count` with the same arguments. Uses P04 and finite product splitting. No legality or positive-side premise. |
| P07 | Approved | Left/right expected-maximum identities and `expected_fluctuation_eq_cF cuts hN x hwv hvK`; deterministic equalities in the original real/WithBot representations, including all zero cases. Uses P06. |
| P08 | Approved | General pointwise `rowCount_reindex`, sample-dependent version, and expected prefix/side count consequences after arbitrary row reindexing. Uses finite bijections and P05/P06. |

The dependency clarification is that P02's column marginal is proved before P03, while P02's full-matrix marginal may be proved after P03. This is an implementation-order split of one item, not a new hypothesis or changed statement. A consistent build order is P01; P02-column; P03; P02-full; P04; P05/P06/P08-pointwise; P07/P08-expectation corollaries.

All integral statements use the actual fixed-count uniform measure. All sample-law, nonemptiness, finiteness, and factorization assertions are proved; none is supplied as a field pretending to represent the source law. No time-profile hypothesis occurs in this interface, and no existing source definition needs to change.

## Stable pre-implementation API proposal

The proposed owner module is `RiffleTimeProfile/FixedCountModel.lean`. It will import the existing `Ambient` definitions and the trusted uniform-distribution/PMF-integral files. The following names and argument order are proposed before the separate expectation freeze. No Lean implementation is present yet.

Definitions and instances:

* `ColumnAssignments (cuts : Cuts k N K) (j : Fin K)` is exactly the count-constrained function subtype described above. Install `Fintype`, `Nonempty`, the discrete `MeasurableSpace`, and `MeasurableSingletonClass` after proving existence.
* `ShuffleSample (cuts : Cuts k N K)` is the dependent function type `(j : Fin K) -> ColumnAssignments cuts j`, with finite/nonempty/discrete instances.
* `columnPMF cuts j := PMF.uniformOfFintype (ColumnAssignments cuts j)` and `columnMeasure cuts j := (columnPMF cuts j).toMeasure`.
* `fixedCountPMF cuts := PMF.uniformOfFintype (ShuffleSample cuts)` and `fixedCountMeasure cuts := (fixedCountPMF cuts).toMeasure`.
* `sampleEntry (sample : ShuffleSample cuts) (row : Fin N) (col : Fin K) := (sample col).val row`.
* `sampleRow (sample : ShuffleSample cuts) (row : Fin N) : Fin K -> Fin k := fun col => sampleEntry sample row col`.
* `rowsSatisfying (rows : Fin N -> Fin K -> Fin k) (B : (Fin K -> Fin k) -> Prop) : Finset (Fin N)` is the finite filter of row labels satisfying B.
* `rowCount rows B : Nat := (rowsSatisfying rows B).card`.
* `boxRows (A : Fin K -> Finset (Fin k)) (sample : ShuffleSample cuts) : Finset (Fin N)` uses `rowsSatisfying (sampleRow sample) (fun row => forall j, row j belongs to A j)`.
* `prefixRows (x : Fin K -> Fin k) (M : Nat) (sample : ShuffleSample cuts) : Finset (Fin N)` uses `forall j, j.val<M -> row j=x j`.
* `leftSideRows (x : Fin K -> Fin k) (j : Fin K) (sample : ShuffleSample cuts) : Finset (Fin N)` uses `(forall h, h.val<j.val -> row h=x h) and row j<x j`.
* `rightSideRows` has the identical argument order and uses `x j<row j`.

The P07 expected-side maxima and expected fluctuation exponent definitions are left to that item’s owner, using these exact side-row observables and `fixedCountMeasure`.

P01 exported facts:

* `columnAssignments_nonempty (cuts : Cuts k N K) (j : Fin K) : Nonempty (ColumnAssignments cuts j)`; the `Nonempty` instance uses this proved fact.
* `columnAssignments_count (a : ColumnAssignments cuts j) (l : Fin k)` is the exact defining fiber-cardinality identity.
* `sample_column_counts (sample : ShuffleSample cuts) (j : Fin K) (l : Fin k)` is the same identity expressed with `sampleEntry`.
* `sample_entry_count_pos (sample : ShuffleSample cuts) (row : Fin N) (j : Fin K)` proves `0 < cuts.count j (sampleEntry sample row j)`.
* `sample_row_legal (hN : 0<N) (sample : ShuffleSample cuts) (row : Fin N)` proves `LegalPrefix (cuts.profile hN) (sampleRow sample row) K`.
* `columnMeasure` and `fixedCountMeasure` get proved `IsProbabilityMeasure` instances from their PMFs.
* Generic `uniform_integrable (f : A -> Real)` is for `[Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]` and proves integrability against `(PMF.uniformOfFintype A).toMeasure` from finiteness.
* Generic `uniform_integral_eq_average (f : A -> Real)` under those same representation classes proves `integral f d(PMF.uniformOfFintype A).toMeasure = (sum_a f a)/(Fintype.card A : Real)`.
* `column_integral_eq_average (cuts : Cuts k N K) (j : Fin K) (f : ColumnAssignments cuts j -> Real)` is the preceding identity for `columnMeasure cuts j`.
* `fixedCount_integral_eq_average (cuts : Cuts k N K) (f : ShuffleSample cuts -> Real)` is the preceding identity for `fixedCountMeasure cuts`.

The generic helper’s finite/discrete representation classes are proved instances in every source application. No integrability, normalization, symmetry, or independence hypothesis is added to an expected-mass theorem.

## Post-freeze P01 implementation audit

After the separate expectation contract was frozen, `FixedCountModel.lean` was implemented with exactly the proposed definitions, predicates, argument order, and instances. The complete module compiles with the pinned compiler. The two initially missing trusted library modules were compiled unchanged into the project-local dependency overlay; the external pinned library cache was not modified.

The construction and audit confirm that:

* column existence is proved internally from the sigma-type cardinality identity, including empty fibers;
* the concrete sample law is uniform on the actual dependent product of count-constrained assignments;
* conservation, positive observed counts, and full sampled-row legality are proved;
* all generic and model-specific finite integrability/average statements have no extra integrability or normalization premise;
* all row predicates preserve the frozen convention that future coordinates are unrestricted.

All eleven exported P01/helper theorems were checked with Lean's foundation-dependency audit. Their only logical foundations are `propext`, `Classical.choice`, and `Quot.sound`; no new axiom or incomplete proof was introduced. P02–P08 remain owned by the other implementing agents.
