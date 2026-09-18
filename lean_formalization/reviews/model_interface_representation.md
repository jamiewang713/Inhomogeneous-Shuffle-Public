# Representation review of the available project interfaces

This inventory reads only the five project-code files named by the
coordinator: `RiffleTimeProfile/Base.lean`, `Digits.lean`, `Analysis.lean`,
`Ambient.lean`, and `RiffleShuffle/Profiles.lean`. Their imported files were
not opened. The mathematical interpretation is still restricted to the
three authorized source documents. No Lean implementation or other project
file was edited for this review.

The new interfaces make concrete finite profile bridges possible without
changing our frozen F01–F20 definitions or assumptions. They do **not** supply
time measurability of the profile, arbitrary-interval target additivity, or
a shuffle-matrix expectation identity. Those distinctions are material.

## Exact available names and the interfaces they supply

### Simplex, cut data, and time indices (`TimeProfile` namespace)

From `Base.lean`:

- `Simplex k` is the subtype of `stdSimplex ℝ (Fin k)`.
- `prob`, `prob_nonneg`, `prob_le_one`, and `sum_prob` provide real
  coordinate masses in `[0,1]` summing to one.
- `Cuts k N K` stores `count : Fin K -> Fin k -> Nat` and `sum_count`.
  `Cuts.profile` turns a column into a simplex point under `0<N`.
  `Cuts.profile_prob` identifies its coordinate with the count divided by
  `N`; `Cuts.profile_pos_iff` identifies legality with a positive pile count.
- `logScale N`, `logScale_pos`, `columnTime N j`, `horizonDepth N T`,
  `horizonDepth_error`, and `horizonDepth_zero` provide exact normalization
  and the terminal floor error. Lean column `j` corresponds to paper column
  `j.val+1`; its time is `(j.val+1)/logScale N`.

These discharge the nonnegative-vector, upper-bound, normalization, and
legal-positive hypotheses of our finite statements. They do not require
the local-good condition or an almost-like condition.

### Exact regularity and one-column costs

From `Base.lean`:

- `pileMax`, `prob_le_pileMax`, `pileMax_nonneg`, `pileMax_pos`,
  `pileMax_le_one`, `inv_card_le_pileMax`, and `exists_prob_pos` supply the
  maximum-mass prerequisites for F09.
- `digitCost z = log(1/z)`, `maxCost`, `powerSum`, `psi`, `tiltedWeight`,
  `tiltedCost`, `shannonEntropy`, and `tiltedEntropy` are concrete source
  definitions. Our frozen cost is `-log z`; `digitCost z = -log z` follows
  from the trusted real-log inverse identity. In the physical selected-digit
  interpretation legality still supplies positivity, as frozen.
- `BorelPartition` contains `cellCount`, `classify`, `measurable_classify`,
  `rep`, and `classify_rep`. Its `cell` is the fibre of the classifier.
- `BorelPartition.IsRegular` has the source fields `psi_oscillation`,
  `maxCost_oscillation`, `good_digit`, and `exceptional_digit`.
- `BorelPartition.IsGoodDigit` is exactly the source strict comparison
  `2*chi < representative coordinate`.
- The exported regularity consequences are
  `BorelPartition.IsRegular.good_prob_pos`, `.good_actual_gt`,
  `.good_digitCost_error`, `.exceptional_actual_le`,
  `.maxCost_rep_error`, and `.psi_rep_error`.

From `Analysis.lean`:

- `powerSum_pos` proves positivity with the displayed premise `1<=theta`.
- `powerSum_le_one` works for `theta in [2,4]` and `2<=k`.
- `maxCost_bounds` gives `0<=maxCost<=log k`.
- `psi_bounds` gives `0<=psi<=4*log k` uniformly for `theta in [2,4]`.
  The constant is four, not the sharper three proposed in the earlier
  review. Frozen F15 uses a generic bound `M`, so taking `M=4*log k`
  requires no change to it.
- `exists_regular_partition` gives a Borel partition satisfying
  `IsRegular chi 1`, under the source `2<=k` and `0<chi<1/k`. Its proof
  constructs a finite coordinate-grid classification and proves the
  regularity properties. This removes the need to assume partition
  existence as an extra axiom. It does not give an explicit bound on the
  number of cells as a function of `chi`.
- `finite_gibbs` is a complete finite entropy inequality on a simplex
  vector, including the zero-total branch and support-only positivity.
  It uses `theta>=1`. Our frozen F14 retains its more general `theta>0`
  statement with an explicit positive normalizer; the narrower project
  result must not replace or strengthen that frozen theorem. At the source
  range `[3,4]` either theorem applies.

For an already specified source partition, use that partition and its
regularity proof. Choosing the partition from `exists_regular_partition`
must not silently change an existing profile classification.

### Exact prefix and fluctuation data

From `Ambient.lean`:

- `positions K a b` is the finite set `a<=j.val<b`, corresponding exactly
  to paper columns `a<j<=b`.
- `LegalPrefix p x M`, `prefixWeight`, `prefixMass`, `cL`, and `cE` use
  a full function `x : Fin K -> Fin k` and a natural prefix length.
  `cL` starts at the exact ambient length `w`, not `floor(r log N)`.
- `AmbientBlock` and `AmbientApproximation` keep ambient legality and the
  time/mass errors explicit.
- `prefixWeight_pos`, `prefixWeight_le_one`,
  `prefixWeight_extension_le`, and `prefixMass_pos` supply the finite
  product prerequisites.
- `cL_split`, `cL_extension_le`, and `cL_exact_mass_exponent` give the exact
  split, monotonicity, and mass-exponent relation including the ambient
  discrepancy. These agree with the frozen F05/F11 design.
- `cE_nonpos` and `cE_terminal` cover the tail sign and zero terminal tail.
- `leftProbability`, `rightProbability`, `sideMass`, `sideMaximum`,
  `logExponent`, and `cF` are present. `logExponent` takes values in
  `WithBot ℝ` and returns bottom at zero; the zero-fluctuation case is not
  silently represented by `Real.log 0`.
- `Crossings` records an actual left and right side-probability witness,
  each at least `chi`, before the boundary length `v`.
- `ParentCrossing` contains `0<M`, `v<=M-1`, and the parent inequality
  `delta<=cL(parent)-F`.

No exported side-mass lower bound or positive `cF` comparison occurs in
these inspected files. F10/F11 can provide that finite step after product
factorization and extraction of the two crossing witnesses.

`StableAt` uses `cL-F<=delta`. The source's first-crossing test is strict
`cL-F<delta`. Therefore `StableAt` is an auxiliary relaxed inequality,
not a replacement for the source stable-prefix definition. `ParentCrossing`
does not by itself define a first stopping prefix or prove a stable
partition. No change to our frozen F12 is needed or permitted.

### Digit profiles

From `Digits.lean`:

- `goodPositions`, `exceptionalPositions`, `digitKey`, `digitCount`, and
  `digitTotal` identify the finite space-time/digit bins.
- `profileS`, `profileQ`, `profileR`, and `profileH` are concrete versions
  of the source quantities.
- `SameCoarseProfile` requires equality of the count array and exceptional
  position set only; exceptional digit labels are not inserted.
- `digitCount_nonneg`, `digitTotal_nonneg`, `profileR_nonneg`, and
  `positive_count_support` provide the input facts for F14/F15.
- `profile_count_partition` proves
  `sum digitTotal + profileR = (M-v)/logScale N` under `v<=M<=K`.
- `profileS_nonneg`, `profileQ_nonneg`, and `profileH_nonneg` are present.
  Their signatures carry regularity, positivity, and legality data even
  when some individual proof steps need less. Those signatures must not
  be used to add hypotheses to our already frozen general finite helpers.
- `profile_cost_replacement` already proves the concrete `cL` decomposition
  error, first with `C*chi*card(good)/logScale N`, then with
  `C*chi*(M-v)/logScale N`. It has explicit `C>=0` for enlarging the
  cardinal factor, as well as exact endpoint ordering and legality.
- `profile_entropy_bound` already proves the literal finite source entropy
  inequality for `theta in [3,4]`; it needs no almost-like assumption.
- `same_profile_S_H_R` proves constancy of exactly `S,H,R` on a coarse
  profile. It correctly does not assert constancy of `Q` or `cL`.

`digitCount` is a normalized real value. Its raw natural count is the card
of the filtered `goodPositions` set appearing in its definition. For F19
one can encode those raw cards in `Fin(K+1)`, prove each is at most `K`,
and use `logScale N>0` to show that equality of normalized counts is
equivalent to equality of raw counts. This is an adapter, not a change to
either profile definition.

### Existing foundational word probabilities

The inspected `RiffleShuffle/Profiles.lean` provides the following names:

- `RiffleShuffle.PileProfile.countAt_of_lt`, `.countAt_of_ge`,
  `.count_le_deck`, `.prob_nonneg`, `.prob_le_one`, `.prob_pos_iff`,
  `.prob_sum`, `.exists_positive_digit`, and `.normalized`.
- `RiffleShuffle.mass_empty`, `.mass_nonneg`, `.mass_le_one`,
  `.mass_pos_iff_legal`, `.mass_sum`, and `.mass_append`.

`PileProfile` is parameterized as `(N,k,K)`, whereas `TimeProfile.Cuts`
is parameterized as `(k,N,K)`. The code uses `PileProfile.count`, `.total`,
and `.deck_pos`; these are sufficient to propose the direct cut-data
conversion. The definitions of imported `PileProfile`, `NormalizedProfile`,
`Word`, `Legal`, and `mass` were not opened, so no definitional equality
between their representations and `TimeProfile` types is asserted here.

The proofs show that `Word` is related to `Fin m -> Fin k` by
`Equiv.vectorEquivFin`; the word mass is the product of `probAt j.val`.
Thus the finite product law can be connected to our `wordWeight` and to
`TimeProfile.prefixWeight` by an explicit finite-word equivalence. No
matrix-row expectation theorem appears in this inspected file.

## Concrete bridges that preserve the frozen contracts

The following are mathematical/type-level adapter plans, not newly written
Lean statements or changed frozen assumptions.

1. **Cost and regularity adapter (F01–F04).** For `N>=2`, take
   `L=TimeProfile.logScale N`, actual selected mass
   `TimeProfile.prob (p j) (x j)`, and representative selected mass
   `TimeProfile.prob (P.rep(P.classify(p j))) (x j)`. Use `digitCost=-log`
   and the four regularity consequences. Restricted to
   `TimeProfile.positions K v M`, the good/exceptional finite sets are
   exactly the existing `goodPositions` and `exceptionalPositions`.
   Legality supplies the frozen positive actual masses.

2. **Prefix split adapter (F05).** Use the two disjoint sets
   `positions K w v` and `positions K v M` under `w<=v<=M<=K`.
   `cL_split` is already the exact source-level identity. No macroscopic
   `r` or ambient-error limit is introduced.

3. **Finite maximal and power-sum replacements (F06/F08/F09).** For any
   finite column set `J`, classify columns by `P.classify(p j)`. Set actual
   values to `maxCost(p j)` or `psi(p j,theta)`, representatives to their
   values at `P.rep i`, and normalized cell counts to the actual finite
   card divided by `L`. The regularity error is `C*chi`.
   Against these exact empirical target weights, take `delta_i=0` in F06.
   Against any separately supplied finite target weights `m_i`, preserve
   the explicit bounds `|count_i/L-m_i|<=delta_i`.
   The resulting error is
   `C*chi*card(J)/L + sum_i |representative_i| delta_i`.
   Existing bounds make the last term at most
   `log k * sum delta_i` for max cost and
   `4 log k * sum delta_i` for `psi`. The tail set for `cE` is
   `positions K M K`; negate the F06 comparison via F08.
   These bridges require no time measurability.

4. **Finite side comparison (F10/F11).** Use the `Crossings` witnesses to
   place two side masses among the corresponding `sideMaximum` values.
   Split prefix products at the witness index. The continuation factors
   lie in `[0,1]` by `prob_nonneg` and `prob_le_one`, so F10 gives
   `sideMass>=chi*prefixMass`. Legal positive prefix mass and positive
   `chi` imply positive maxima. Restrict `WithBot` log exponents to those
   positive arguments, then apply F11 and `cL_exact_mass_exponent`.
   This establishes a deterministic mass inequality; it does not assert
   variance or conditional anti-concentration.

5. **Entropy adapter (F13–F15).** Use cells
   `Fin R × Fin P.cellCount`, digits `Fin k`, counts `digitCount`, and
   representative coordinates `prob(P.rep i) l`.
   `digitCount_nonneg` and `positive_count_support` give the support
   premises; `powerSum_pos` gives the positive normalizer on `[3,4]`.
   Finite product-index sum identities and the cost identity identify the
   result of our `profile_entropy_le` with `profile_entropy_bound`.
   Deleting `exceptionalPositions` costs at most
   `4 log k * profileR`; the exact error still comes from F06. No integral
   has been inserted as a target by this adapter.

6. **Finite product mass (F18).** Set
   `pWord(j,l)=TimeProfile.prob(p j) l`. Then `prob_nonneg` and `sum_prob`
   discharge every probability premise in `badWordMass_le` and
   `badWordMass_le_tailWeight`. The source bad-digit set is the finite
   set of labels failing `P.IsGoodDigit chi (p j) l`.
   `exceptional_actual_le` gives per-digit mass at most `3chi`.
   The post-boundary `exceptionalPositions` set is a subset of all bad
   positions of the full word; that is the finite event inclusion needed
   for exceptional-prefix truncation. `N*wordWeight` coincides with
   `prefixMass` at depth `K` by a product-index identity. A connection to
   shuffle interval expectations remains separate.

7. **Coarse profile counting (F19/F20).** Encode raw good-digit cards and
   exceptional labels in our refined descriptors and forget the labels
   afterward. For a fixed exceptional set, partition a family of words by
   restrictions to that set and apply `coarse_word_fibre_card_le`.
   `SameCoarseProfile` is compatible with this construction and cannot
   supply a constant `Q` or `cL`. The missing source boundary-prefix
   injection, stable partition, and labelled-fibre multinomial bound are
   not provided by the five inspected files.

## Finite interval blocking: what is available and what remains

`Base.lean` defines `intervalCount` using **closed** real intervals and
defines `AlmostLike` on **closed** uniform `rho`-grid intervals. Adjacent
blocks may therefore share an endpoint column. `TimeMesh` instead has
half-open cells, except for its closed final cell, and supplies
`TimeMesh.cells_disjoint`, `.existsUnique_mem_cell`, `.cellIndex`,
`.cellIndex_mem`, and `.column_cellIndex_mem`.

The finite geometric part can be connected without any new source
assumption:

- prove `columnTime` is injective when `N>=2`, so each endpoint has at
  most one column;
- remove left endpoints from closed full grid intervals, charging at
  most `1/L` per block;
- cover the target interval by disjoint complete `rho`-grid blocks and
  two remainders of total length at most `2rho`;
- bound the empirical remainder by `2rho+2/L` using a finite lattice count;
- apply frozen F07 to the exact finite additive decompositions.

None of those lattice-count/covering lemmas is exported in the five
inspected files. `horizonDepth_error` supplies the terminal floor error,
but is not itself the arbitrary-interval lattice-count lemma.

A `TimeMesh` with a bound on cell widths is not automatically a uniform
`rho` grid to which `AlmostLike` applies. Its mesh information is useful
for time-cell classification; the actual almost-like grid must be handled
with its specified `rho*z` endpoints.

For arbitrary **finite target atom weights** satisfying the frozen additive
decomposition and remainder bound, F07 now has all the right concrete
count data. However, substituting
`m_i(a,b)=integral_{a..b} cellMass mu P i` also requires additivity of those
integrals across the chosen blocks. That is the unresolved analytic step.

## Analytic target connection and the unchanged measurability issue

`TimeProfile.TimeLaw k` is literally

`Real -> ProbabilityMeasure (Simplex k)`.

It has no measurable-kernel, measurable-map, or interval-integrability
field. The functions `profileMaxCost`, `profilePsi`,
`profileTiltedCost`, `profileTiltedEntropy`, `cellMass`,
`integratedMaxCost`, `integratedPsi`, and `integratedTiltedCost` are
defined using Lean's totalized integral. Their existence as definitions
does not prove time measurability or integrability.

`BorelPartition.measurable_classify` concerns the simplex variable. It does
not make `t -> cellMass mu P i t` measurable. Similarly, continuity of
`maxCost` and `psi` in their simplex arguments, proved inside the regular
partition construction, does not make an arbitrary time-indexed family of
their expectations measurable.

For each fixed time, the simplex observables are bounded and continuous,
and the law is a probability measure. The fixed-time integral and
representative comparison can therefore be developed from the existing
mathematics. Exported continuity/integrability lemmas may still be needed
because the relevant continuity proofs currently occur locally inside
`exists_regular_partition`. This is an implementation capability issue,
not a new assumption about the model.

In contrast, the passage in time needs a hypothesis or a theorem that is
not present in these files or explicitly in the original source setup:
for example a measurable probability kernel, or sufficient
interval-integrability of all time-dependent cell masses and costs. The
literal `AlmostLike` definition only imposes numerical inequalities for
the totalized integrals; it does not by definition supply integrability
or the additivity needed for interval blocking. It must not be used as
though it did.

Accordingly, the exact finite bridges above are available under the
already frozen source data. The analytic identifications with `A(r,s)`
and `B_theta(r,s)` remain outside that freeze. They require the pending
source-level clarification or a separate proof from genuinely existing
assumptions; none should be added silently to make those proofs easier.

This report inventories declarations with proof bodies in the named
files. It does not replace the coordinator's import, compilation, and
kernel-dependency checks for the new project interface.
