# Independent review of LB-06 MassBins, v1

Reviewed `RiffleLowerV2/Types/MassBins.lean` against the unchanged frozen `TypeDataSpec` in `Shared/Geometry.lean` and manuscript `lem:type-estimates`. This review changed no implementation or shared file.

Reviewed source SHA-256: `990b31c1b9850ec0374cc1a1ef41c3c21cfbfc97262296d7945732a01fc748fb`.

Verdict: no mathematical or representation defect found. The module proves the finite deterministic selection and exact export obligations from concrete rounded-count facts. It correctly leaves count construction/cardinality and spatial approximation to their respective modules.

## Deterministic choice and tie rule

`exists_maximal_indexFiber` maximizes over the finite nonempty image of the raw class and separately proves that indices outside that image have empty fibers. `leastMaxBin` then uses `Nat.find` on the global maximality predicate. `leastMaxBin_tie` applies minimality to an arbitrary natural index having the same cardinality, so it proves the exact frozen least-index tie rule over all natural indices. This is a deterministic natural index; dependence on a proof of nonemptiness does not introduce another tie convention.

`leastMaxBin_nonempty` compares to the fiber containing a selected raw-class element. Thus positive cardinality is proved before logarithms, and the infinitely many empty fibers cannot be mistaken for maximal bins. `leastMaxBin_card_bound` is a genuine finite fiber pigeonhole inequality. `leastMaxBin_log_loss` uses positivity of both finite cardinalities and its positive numerical bin-count bound before applying product logarithms. It supplies both the nonnegative loss and its logarithmic upper bound.

## Positivity, floors, and bin count

`massOn_pos` derives strict positivity from every used coordinate. `massOn_le_one` uses the actual simplex probabilities; it does not assume a global pile lower bound. `massOn_cost_bounds` requires positive `xi` and actual used-coordinate lower bounds, proves the mass positive, and proves the product log formula using nonzero factors. It yields the exact range `0≤-log mass≤card(I)*log(1/xi)`.

`massBin_eq_indexFiber` explicitly requires raw-class mass positivity and combines it with the simplex upper bound before invoking the natural-floor interval equivalence. This prevents totalized `log 0=0` from admitting fake zero-mass bin-zero elements. The positivity hypothesis covers the entire raw class, as required to identify every fiber and every bin.

`floor_image_card_bound` proves a subset of the natural interval ending at `floor(M)`; it is valid even for negative inputs because natural floor is nonnegative and monotone. At its use in `typeDataSpec_of_counts`, both the actual cost nonnegativity and `M≥0` are established. Its bound `2+M` is a harmless slackening of `floor(M)+1` and matches the frozen numerical bound.

## Exact mass and exponent identities

`selectedClass_exact_mass` uses the defining bin inequalities `b≤-log mass<b+1` and proven positive mass. The resulting interval has exactly the required strict lower and weak upper endpoint: `exp(-1)*N^(-J)<mass≤N^(-J)`. The algebraic adapter `rpow_neg_typeJ` requires `N≥2`, so cancellation of `log N` is justified. Mass exactly one lies in bin zero and is handled correctly.

`card_eq_rpow_log_div` requires positive natural cardinality and `N≥2`. `typeDataSpec_of_counts` obtains positive selected cardinality first, then establishes `H≥0`, `J≥0`, and the exact `card=N^H` identity. No zero-cardinality logarithm is used as evidence of nonemptiness.

## Concrete specification adapter

`roundedClass_actual_lower` obtains a positive occurrence count for the digit at a chosen position. Supported counts force the representative coordinate to exceed `2xi`, and regularity then supplies the actual coordinate lower bound. It does not infer support from the value of a totalized logarithm.

`selectBinData` changes only `binIndex`; the raw class and count data remain definitionally unchanged. `typeDataSpec_of_counts` uses this fact to assemble every frozen conjunct in order: totals, support, rounding, denominator positivity, raw and selected nonemptiness, bin count, exact multinomial cardinality, maximality, least-index tie, nonnegative exponents, exact cardinality and mass interval, and actual lower probability on the entire raw class.

The adapter assumes the separately owned combinatorial conclusions `hC` and `hcard`; this is a valid modular interface and not completion of the final target by itself. The caller still must discharge them using the counting construction. Its additional elementary helper hypothesis `xi≤1` follows from the final theorem's cutoff and `k≥2`; it does not weaken the frozen target when specialized.

## Degenerate cases and remaining integration work

For the empty selected set, a valid raw class is the singleton empty word with mass one. The finite image is `{0}`, the selected index is zero, and every selection/exponent/log-loss lemma applies. Empty cells do not enter this module's binning logic except through already proved count data. No positive block-length hypothesis is present.

This review approves the mathematical structure and frozen-spec alignment. The root's reported successful lane build supplies compilation evidence; this independent read does not replace the final module or package axiom audit. The source error estimate `TypeApproximation`, uniform asymptotic constants, and the complete `RoundedTypeTarget` remain outside this module and must be assembled from checked counting, truncation, entropy and word-cost results.
