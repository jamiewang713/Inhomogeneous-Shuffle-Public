# LB-00 independent representation review

Reviewer: representation-review worker. Date: 2026-10-01.

Scope: read-only reconstruction of the revised source, canonical definitions,
old freezes and Lean 4.33.1 APIs. This report recommends interfaces; it does
not certify any as-yet unwritten target declaration. No project source,
historical contract, dependency cache or manuscript was modified. No build
was run by this reviewer. A later comparison against the exact new Lean
types is required before CONTRACT_READY.

## Findings that affect the shared contract

1. Use `TimeProfile.Cuts`, `ShuffleSample`, `sampleRow`, and
   `fixedCountPMF` directly. The sample space is a dependent product of
   exact fixed-count assignments, not the old product of row permutations.
2. `Tuple.sort` is genuinely stable in the pinned mathlib: it orders pairs
   `(value, originalIndex)`. Its output sends sorted positions to original
   indices. `Tuple.monotone_sort` alone is insufficient to state stability;
   `Tuple.eq_sort_iff` supplies the tie clause.
3. Foundations uses list-vector lexicographic words. The old lower package
   uses `Lex (Fin K → Fin k)`. These are equivalent choices, but not
   definitionally the same order. Prefer the foundations vector order for
   sorting and prefix ranks, with explicit function/vector adapters.
4. Physical chronology must be defined independently of full-word sorting.
   Even on the same dependent-product sample, the chronological inverse
   is generally not pointwise the full-word stable sort. LB-01 must prove
   equality of their distributions using reindexing of columns.
5. Enumeration of variable-length words must not use arbitrary full
   arrays plus a prefix length: a prefix of length `m` then appears
   `k^(K-m)` times. A sigma of genuine length-indexed words avoids this.
6. Retain integer-path boundary edges outside the deck. Computing boundary
   solely inside `Fin N` loses the two endpoint boundary edges, including
   for the full deck.
7. Macroscopic scalar integrability is an explicit addition to the old
   frozen hypotheses. It is neither implied by `AlmostLike` nor obtained
   by renaming `TimeLaw`. The partition in this premise must be the
   partition actually selected for transfer.

## Read-only evidence and trusted API

The following local checkout was inspected:

* `formalization/.lake/packages/mathlib/lean-toolchain` is
  `leanprover/lean4:v4.33.1`.
* `git -C formalization/.lake/packages/mathlib rev-parse HEAD` returned
  `0df444a360eaa60ab8c11dca51a86af692955474`.

This checks source provenance, not the coordinator's runtime or smoke
build; the latter are separate acceptance obligations.

Relevant exact declarations in that checkout:

* `Tuple.sort (f : Fin n → α) : Equiv.Perm (Fin n)` for `[LinearOrder α]`.
* `Tuple.monotone_sort f : Monotone (f ∘ Tuple.sort f)`.
* `Tuple.eq_sort_iff`:
  `σ = Tuple.sort f ↔ Monotone (f ∘ σ) ∧
    ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j`.
* `Tuple.comp_perm_comp_sort_eq_comp_sort` identifies sorted value tuples
  after reindexing; it does not identify sorting permutations.
* `Tuple.sort_eq_refl_iff_monotone`, `Tuple.sort_perm`.
* `Tuple.lt_card_lt_iff_apply_lt_of_monotone` and
  `Tuple.lt_card_le_iff_apply_le_of_monotone` now take `f`, `a`, and `j`
  implicitly. The positional call in old `Sorting.lean` needs a
  proof-only compatibility edit; the canonical foundations call already
  uses the current API.
* `PMF.map`, `PMF.map_apply`, `PMF.map_comp`, `PMF.bind`, `PMF.bind_apply`,
  `PMF.toMeasure_map_apply`.
* `PMF.integral_eq_sum`:
  `∫ a, f a ∂p.toMeasure = ∑ a, (p a).toReal • f a`, on finite types
  with measurable singletons. No separate integrability premise is needed.
* `PMF.apply_ne_top` and `ENNReal.toReal_sum` support the real-mass bridge.

Do not import the old vendored `RiffleTimeProfile` tree alongside the
canonical tree. The module name is identical and import-path priority
would silently select one source.

## Canonical matrix model and reuse

`TimeProfile.Cuts k N K` contains only natural column counts and their
sum equal to `N`. `cuts.profile hN j` adds the legitimate normalization
premise `hN : 0 < N`. The canonical sample type is

```lean
(j : Fin K) → TimeProfile.ColumnAssignments cuts j
```

where each coordinate is a function `Fin N → Fin k` with the required
histogram. `fixedCountPMF cuts` is the uniform PMF on this finite,
nonempty dependent product. It does not need to assert independence as a
field.

Already implemented canonical reuse candidates include:

* `FixedCountModel`: `sample_column_counts`, `sample_row_legal`,
  `fixedCount_integrable`, `fixedCount_integral_eq_average`.
* `FixedCountMoments`: `columnReindex`, `columnReindex_entry`,
  `uniform_integral_equiv`, `column_integral_reindex`,
  `column_product_factorization`, `column_marginal`,
  `sample_marginal`, `column_digit_probability`,
  `sample_digit_probability`, `expected_box_count`.
* `ExpectedMass.expected_prefix_count`: for `M ≤ K`,
  the integral of `(prefixRows x M sample).card` is exactly
  `prefixMass N (cuts.profile hN) x M`, including zero mass.

These are real reusable declarations, subject to the integration build;
there is no need to redo the first moment from scratch. In particular,
`column_product_factorization` is already a proved product-expectation
identity sufficient to derive the PMF independence statements needed by
LB-01. It is not a proof of graph representation or physical chronology.

An explicit foundations adapter needs both `hN : 0 < N` and `hk : 2 ≤ k`:

```lean
def toPileProfile (cuts : TimeProfile.Cuts k N K)
    (hN : 0 < N) (hk : 2 ≤ k) : RiffleShuffle.PileProfile N k K :=
  { count := cuts.count, deck_pos := hN, alphabet_two := hk,
    total := cuts.sum_count }
```

Its matrix rows are `List.Vector.ofFn (TimeProfile.sampleRow sample i)`;
the column-count proof reduces using `List.Vector.get_ofFn` and
`TimeProfile.sample_column_counts`. This gives access to the already
implemented foundations `sortPerm`, `sortedRows`, `rank_mem_iff`,
`rank_count`, `endpoint_bounds`, `rank_convex`, `rank_mono`,
`rank_disjoint`, `shuffleGraph`, and `reachable_iff_eq`.

Ordinary law definitions should remain available without `hN` or `hk`;
these proofs belong only on the adapter to the stronger historical
`PileProfile` structure. The K=0 and deterministic-column cases should
therefore remain definable directly.

## Prefix and lexicographic representation

Recommended finite word types:

```lean
abbrev Word (k m : ℕ) := RiffleShuffle.Word k m
abbrev Prefix (k K : ℕ) := Σ m : Fin (K + 1), Word k m.val
```

This is the existing foundations `RawPrefix` representation. Keep raw
prefix data separate from legality. A legal node is an adapter to the
existing `RiffleShuffle.Node`, not a different notion of prefix.

`List.Vector.ofFn` and `.get` provide the two directions of the
function/vector equivalence. For source formulas involving one full
array and several compatible prefixes, truncate a full word at each
required depth. For a standalone prefix, extend its digits arbitrarily
past its depth only when invoking the canonical full-array APIs. The
extension value may be `0 : Fin k` when `0 < k`, and a proof must show
that `prefixRows`, `prefixWeight`, and `LegalPrefix` do not depend on the
unused suffix. Do not require that unused suffix to be legal.

Routine shared adapters worth proving before lane release:

* vector/function inverse equalities;
* equality of prefix digits iff the vector/list prefix relation;
* equality of canonical and vector prefix-row sets;
* prefix-mass equality with the product over `Fin m`;
* invariance of counts under sorting;
* source and Lean rank interval equivalence.

For a full vector word `w`, use its inherited list lexicographic order
throughout. Using `Tuple.sort (fun i => List.Vector.ofFn (sampleRow s i))`
then agrees definitionally with the adapted foundations sorting
permutation. If a PiLex interface is still needed by a compatibility
port, prove the order-preserving equivalence once rather than silently
swapping order instances.

## Stable-sort and chronological physical laws

Recommended actual matrix law:

```lean
def matrixStableSort (sample : TimeProfile.ShuffleSample cuts) :
    Equiv.Perm (Fin N) :=
  Tuple.sort (fun i => List.Vector.ofFn (TimeProfile.sampleRow sample i))

def matrixStableSortLaw (cuts : TimeProfile.Cuts k N K) :
    PMF (Equiv.Perm (Fin N)) :=
  (TimeProfile.fixedCountPMF cuts).map matrixStableSort
```

The output value at a sorted position is its original row label.

For the physical process, fix a deck as a map from current positions to
original labels. At step `j`, sample a uniform word `a_j` with the
prescribed pile counts, interpreted as the pile labels of output
positions in a forward interleaving. Let

```lean
s_j := Tuple.sort a_j
τ_j := s_j.symm
```

Then `τ_j` sends an output position to its slot in the concatenation of
the input piles. Thus it defines the actual order-preserving
interleaving, including zero-sized piles. A deck update is
`newDeck i = oldDeck (τ_j i)`, namely `τ_j.trans oldDeck`.

Fold over the ordered list `List.ofFn (fun j : Fin K => j)` using

```lean
fun deck j => (Tuple.sort (sample j).val).symm.trans deck
```

with the identity deck as initial value. Define the physical forward
law as the `fixedCountPMF` pushforward by this fold; define the physical
inverse permutation as its `.symm` and its law as the corresponding
pushforward. This definition is unconditional and contains no desired
law identity as a field or a hypothesis.

For two steps, the fold gives
`forward = τ₀ ∘ τ₁` and `inverse = s₁ ∘ s₀`. These equations state the
orientation explicitly. Reverse chronological inverse operations act
on a deck first with `s₁`, then `s₀`. When the newly drawn digits are
pulled back to the original labels, the resulting independent columns
are sorted with column 0 taking priority. This is the substantive
LB-01 bridge; it is not definitional on the same raw column sample.

LB-01 must prove, separately:

* the one-step slot rule agrees with cutting into contiguous piles and
  uniformly interleaving while preserving internal order;
* the reindexing transformation preserves the joint uniform-column law;
* the chronological physical inverse law equals `matrixStableSortLaw`;
* inversion preserves half-L1 TV and the uniform permutation law.

The original lower package explicitly leaves the physical bridge outside
its scope; its theorem name `inverseShuffle` must not be treated as
evidence that the bridge already exists.

## Path graphs and component sorting

A useful elementary representation is a finite set of left endpoints:

```lean
abbrev PathEdges (N : ℕ) := Finset (Fin (N - 1))
```

An edge index `e` denotes the zero-based edge `(e.val,e.val+1)`. The
casts of both endpoints into `Fin N` require only the supplied `e.isLt`
and elementary arithmetic; N=0 and N=1 give no edge indices.

The generated path-edge set keeps exactly indices at which consecutive
sorted full words are equal. Its conversion to `SimpleGraph (Fin N)`
must agree with the adapted foundations `shuffleGraph`. Such an adapter
lets the counting lanes work with finite sets while reusing the
foundations reachability result. It avoids asking every lane to manage
unordered edge quotients.

A concrete component-sort permutation can be defined without bundling
its properties as proof fields. Set

`componentIndex G i = #{e : Fin (N-1) | e.val < i.val ∧ e ∉ G}`.

This index is constant exactly on consecutive components and increases
between them. For a permutation `π`, sort the pairs
`(componentIndex G i, π i)` in product lexicographic order, giving a
permutation `τ`. Define `componentSort G π := τ.trans π`, i.e.
`π ∘ τ`. This is a permutation by construction. Since the component
indices occur in increasing contiguous blocks, this operation sorts
values within their original components.

The last sentence requires a theorem, as do equality of component index
and path reachability, the empty-edge identity, and the full-path sorted
identity. They are good finite shared helpers if feasible, or explicitly
owned LB-01 obligations. They must not be assumed as data fields.

Independence of the permutation in the graph mixture should be in the
law definition:

```lean
(TimeProfile.fixedCountPMF cuts).bind fun sample =>
  (PMF.uniformOfFintype (Equiv.Perm (Fin N))).map
    (componentSort (generatedEdges sample))
```

The target equality with `matrixStableSortLaw` is genuinely pending.
It cannot be replaced by monotonicity of sorted rows or by a field in a
model structure.

## Integer ranks, clipping, boundary, and the scan

Use `rank i : ℤ := (i.val : ℤ) + 1`. For natural cuts `L,U`, prove

`L ≤ i.val ∧ i.val < U ↔ (L : ℤ) < rank i ∧ rank i ≤ U`.

Thus zero-based `[L,U)` matches manuscript one-based `(L,U]`, and the
same count `U-L` applies even to empty prefix blocks.

Keep the geometry template `H₀ : Finset ℤ` in manuscript rank
coordinates. Define a clipped translate as

```lean
Finset.univ.filter fun i : Fin N => rank i - q ∈ H₀
```

where `q : ℤ`, and use `q : Fin (N+1)` for scan locations. Its image
under `rank` is exactly `(q + H₀) ∩ Icc 1 N`. In particular, the shift
is the source zero-based lower cut `L_a`, without an extra `+1`.

For integer `H`, encode the path edges by their left endpoints:

* `internalOrigins H := H.filter (fun z => z+1 ∈ H)`;
* `boundaryOrigins H :=
  (H ∪ H.image (fun z => z-1)).filter
    (fun z => (z ∈ H) ≠ (z+1 ∈ H))`.

Left-endpoint encoding is in bijection with the source ordered edge
pairs `(z,z+1)`, so cardinalities agree. Do not truncate this boundary to
deck edges. The image of the full deck `{1,…,N}` has two boundary
origins, 0 and N, when N>0.

Define the observable as a real sum of indicators over retained
zero-based path edges:

`X H σ = ∑ e ∈ internalEdges H, if σ e.left < σ e.right then 1 else 0`.

Its scan event has exactly `N+1` choices:

`∃ q : Fin (N+1), X (clippedTranslate H₀ q) σ >
  (internalEdges (clippedTranslate H₀ q)).card / 2 + s`.

The denominator 2 is real. Cast natural cardinalities before subtracting
or taking real powers. Set `M = (H₀.card : ℝ)`, not the random or clipped
size. Clipping only proves `|H_q| ≤ M`; it does not preserve size.

## One finite real probability interface

Retain PMFs as the primary law representation and define

```lean
mass P a := (P a).toReal
prob P A := ∑ a ∈ A, mass P a
expect P f := ∑ a, mass P a * f a
variance P f := expect P (fun a => (f a - expect P f)^2)
tv P Q := (∑ a, |mass P a - mass Q a|) / 2
```

This is exactly the normalization of old `FiniteProbability.lean`.
If that file is ported into LB-01's compatibility subtree, define a
proved conversion from a PMF to its real `FiniteLaw`, rather than
assuming their operations agree. The total-mass field follows from
`PMF.tsum_coe`, finiteness, `PMF.apply_ne_top`, and
`ENNReal.toReal_sum`. The event, expectation, variance and TV bridges
then reduce to finite formulas.

At finite measurable types, `PMF.integral_eq_sum` supplies the theorem
that this `expect` equals the canonical integral; use `smul_eq_mul`.
Canonical `fixedCount_integral_eq_average` and
`expected_prefix_count` then transfer without any new temporal
integrability premise. A generic variance adapter needs no assumptions
on the observable beyond its real-valued finite domain.

Prove real-probability pushforward and mixture formulas once. Inversion
TV invariance is a finite reindexing equality, while any coupling or
graph-mixture equality is separate probabilistic mathematics.

## Empirical costs and exact finite sums

Let `L = TimeProfile.logScale N`, `K = TimeProfile.horizonDepth N T`,
`S_N = K/L`. The shared definitions can use explicit overlap lengths

`length_j(r,s) = max 0 (min s ((j+1)/L) - max r (j/L))`

and define a cost integral as the finite sum
`∑ j, length_j(r,s) * f(p_j)`. Under `N≥2` and `0≤r≤s≤S_N`, this is
the literal integral of the step cost on the source intervals
`(j/L,(j+1)/L]`. Point values at the interval boundaries do not affect
the integral. This representation avoids an arbitrary default simplex
outside the empirical horizon and never assumes macro integrability.

Instantiate `f` with the existing `maxCost`, `psi p α`,
`tiltedCost p α`, and `tiltedEntropy p α` to define `A_N`, `B_N`,
`J_N`, and `H_N`. A separate exact grid-sum definition should be

`(∑ j ∈ TimeProfile.positions K a b, f(p_j)) / L`.

The shared adapter should prove equality with the overlap formula at
`r=a/L`, `s=b/L` for `a≤b≤K`, including `a=b` and K=0. Bounded step
functions are integrable on finite intervals, but the empirical costs
need no macro-profile premise even if this equality is proved via
finite interval integrals.

Define `β_N(s)=1-A_N(0,s)` and the source `F_{α,N}` exactly. Define
`Λ_{1,N}` with real `sSup` and `sInf` over the displayed closed
parameter domains. Nonemptiness and boundedness needed to use their
order properties are proof obligations; Lean's totalized `sSup` and
`sInf` definitions do not discharge them. The source's stronger bounds
`psi≤(α-1)log k`, `I≤log k`, and `H≤I` belong to LB-05; canonical
`Analysis.psi_bounds` currently gives the weaker `4 log k` bound.

## Minimal opt-in macroscopic integrability predicate

Preserve `TimeProfile.TimeLaw`, `AlmostLike`, `cellMass`,
`profileMaxCost`, `profilePsi`, `integratedMaxCost`, and
`integratedPsi` literally. A suitable new predicate is

```lean
def ScalarTimeIntegrable (mu : TimeProfile.TimeLaw k)
    (P : TimeProfile.BorelPartition k) (T : ℝ) : Prop :=
  (∀ i : Fin P.cellCount,
    IntervalIntegrable (TimeProfile.cellMass mu P i) volume 0 T) ∧
  IntervalIntegrable (TimeProfile.profileMaxCost mu) volume 0 T ∧
  (∀ α ∈ Set.Icc (2 : ℝ) 4,
    IntervalIntegrable (fun t => TimeProfile.profilePsi mu t α) volume 0 T)
```

For `T>0`, restriction to ordered subintervals of `[0,T]` follows from
the ordinary interval-integrability restriction theorem. There is no
need to demand temporal continuity, derivatives, a measurable kernel,
or integrability of macro `J` and `H`. Generic quadrature for an
arbitrary `f` must take its own scalar-integrability premise; this
predicate only covers the actual a/psi specializations.

The quantifier order must make the selected `P` visible before this
predicate is required. For example, for fixed accuracy and k,T, choose
`P` and positive mesh threshold, then state the conclusion for every
`mu` satisfying `ScalarTimeIntegrable mu P T` and the other hypotheses.
Alternatively fix `mu` first, choose `P`, and put the integrability
implication after that choice. Do not assume integrability for an
input `P₀` and then refine or replace it with an unrelated `P`.

The old freeze explicitly leaves two-sided analytic transfer
uncertified. `reviews/analytic_alternatives.md` supplies a same-cell
nonmeasurable switching counterexample: all selected partition cell
masses are constant while a and psi costs are not time integrable.
Consequently both the cost clauses above and the explicit statement
that M has stronger hypotheses are necessary. The existing
`one_sided_quadrature` result cannot be relabelled as two-sided transfer.

## Endpoint and target type checks to perform before release

The empirical endpoint can use the precise admissibility disjunction

`κ₀ ≤ β_N(S_N) ∨
 (η_f ≤ Λ_{1,N} ∧ β_N(S_N) < κ₀ ∧ LocalGood cuts …)`

with `κ=η_f/1000`, `κ₀=min(κ/100,1/1000)`. Its fixed cold parameters
include positive rho, chi_g and gamma, and
`2*rho*log k ≤ κ₀/100`. The large-word disjunct has no local-good
premise. A pair of separate branch targets is equally faithful and
makes that separation particularly easy to check.

For each fixed parameter set and accuracy `ε>0`, the target must say
`∃ N₀, ∀ N≥N₀, ∀ cuts : Cuts k N (horizonDepth N T), … →
  1-ε ≤ tv (physicalInverseLaw cuts) uniformPermutationLaw`.
All witnesses, word families and cuts over which uniformity is promised
must be after N₀. The positive fixed margin and local parameters are
before N₀. A sequence-specific `Tendsto` does not have this content.

M additionally fixes the selected regular partition before its
integrability premise, and fixes rho/phi before N₀. N₀ may depend on
the chosen partition, rho, phi, chi_g, gamma and accuracy. M must target
the physical inverse law and use the source maximum of the two macro
margins. Naming a matrix-model target is useful as an intermediate;
it is not an alternative final law.

Each lane target should be a proposition-valued definition or a textual
unproved specification. It must never become an axiom, an instance, an
assumed target theorem, or a record field in the final theorem's
hypotheses. Geometry records may contain lengths, word families, sets,
and nominated parameters. Their witness inequalities, localization
probabilities, occupancy estimates, graph-law equality and TV conclusion
must remain separately owned propositions to prove.

## Import and ownership recommendation

For the smallest shared model layer, use the canonical
`RiffleTimeProfile.FixedCountModel` and
`RiffleShuffle.Graphs`; these transitively supply their existing
foundations. Add the PMF integrals/constructions, product lex order, and
finite tuple sorting modules explicitly only if not already imported.
The source expectations can live in a separate adapter module importing
`RiffleTimeProfile.ExpectedMass`, keeping analytic transfer imports out
of the finite model module.

Do not import a whole upper-proof tree for entropy, counting, or finite
probability helpers. Let LB-01 own compatibility ports of old finite
probability/sorting modules, and let the canonical fixed-count first
moment be reused by adapter. The new shared types and their routine
adapters are LB-00 owned. Substantive graph law/chronology proofs are
LB-01 owned; a/psi/tilt inequalities are LB-05 owned; two-sided scalar
transfer is LB-07 owned; concentration, geometry and final lower bounds
remain in their designated lanes.

Current review verdict: the above representation is compatible with
the revised source and preserves the original frozen definitions. The
integrability addition is intentional and substantive. Exact new target
types, compiled shared adapters, physical-law definitions, build
isolation and axiom closure still need the coordinator's final gate.

## First comparison with new shared source (2026-10-01)

At the coordinator's request, inspected the newly written
`Shared/Model.lean`, `Shared/Path.lean`, and `Shared/Empirical.lean`
while dependency builds were in progress. This was source inspection,
not an independent compile.

Accepted definitions:

* `Model.physicalForward` folds `List.finRange K` with
  `(oneStepForward j (ω j)).trans deck`. This has the position→label
  orientation recommended above. `physicalInverse` is the inverse of
  this deck, and `physicalInverseLaw_eq_map` states only the genuine
  definitional inversion bridge, not the pending matrix-law identity.
* The word/vector definitions, raw prefix type, row adapter and
  `toMatrix_sort` agree with foundations. Unsorted-row definitions of
  `lowerRank`, `upperRank`, and `prefixCount` have the right source
  counts; a permutation reindexing adapter will match sorted-row ranks.
* `integerBoundary`, `clipTranslate`, `manuscriptRank`, and
  `rank_interval_iff` have the intended endpoint conventions.
* The empirical `columnFraction` is the clipped primitive of each
  column interval. Taking its endpoint difference gives the signed
  step integral and correctly makes interval additivity unconditional.
  Its interpretation as a positive-time step integral and its exact
  grid-sum adapter require `N≥2` (in particular `logScale N>0`).
* `ScalarIntegrable` has exactly the three recommended clauses, with
  the selected partition appearing as an explicit argument.

Corrections sent to the coordinator:

1. `componentSort` originally passed the plain pair
   `(componentIndex G i, π i)` to `Tuple.sort`. This is the ordinary
   product type, whose mathlib order is componentwise. The intended
   lexicographic linear order needs an explicit type tag:

   ```lean
   (Tuple.sort (fun i =>
     (toLex (componentIndex G i, π i) : ℕ ×ₗ Fin N))).trans π
   ```

   `Mathlib.Data.Prod.Lex` supplies this order and is already imported
   through `Tuple.Sort`. The existing final `.trans π` is correct.
2. `probability` has a completely arbitrary proposition-valued event;
   its indicator needs classical decidability. Use `by classical; exact
   ...` in its body or an explicit module-local classical instance.
   `noncomputable section` alone is not a reason to expect a
   `Decidable (A ω)` instance.
3. The new name `prefixMass` denotes source `λ_w`, whereas canonical
   `TimeProfile.prefixMass` denotes `Nλ_w`. The precise adapters are
   new `prefixMass` ↔ canonical `prefixWeight`, and new `prefixMean`
   ↔ canonical `prefixMass`. This is a naming difference, not a
   mathematical defect; it must be explicit in every moment adapter.

The following additional shared adapters are useful and routine. Names
below are proposed signatures, not assertions that these declarations
already exist:

```lean
theorem expect_eq_integral {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : PMF Ω) (f : Ω → ℝ) :
    expect P f = ∫ ω, f ω ∂P.toMeasure

theorem prefixCount_eq_upperRank_sub_lowerRank
    {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (w : Prefix k K) (ω : Sample cuts) :
    prefixCount w ω = upperRank w ω - lowerRank w ω

theorem sorted_prefix_interval
    {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (w : Prefix k K) (ω : Sample cuts) (i : Fin N) :
    (sortedWord ω i).toList.take w.1.val = w.2.toList ↔
      lowerRank w ω ≤ i.val ∧ i.val < upperRank w ω

theorem empiricalIntegral_grid_eq
    {K N a b : ℕ} (hN : 2 ≤ N) (f : Fin K → ℝ)
    (hab : a ≤ b) (hb : b ≤ K) :
    empiricalIntegral N f (gridTime N a) (gridTime N b) =
      gridSum N f a b
```

For arbitrary raw-prefix expectations, an even cleaner alternative to
padding the suffix is to define

```lean
def prefixAllowed {k K : ℕ} (w : Prefix k K)
    (j : Fin K) : Finset (Fin k) :=
  if h : j.val < w.1.val then {w.2.get ⟨j.val, h⟩} else Finset.univ
```

Then prove `boxRows (prefixAllowed w) ω` is exactly the new prefix-row
set. `TimeProfile.expected_box_count` yields

```lean
theorem expect_prefixCount
    {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N)
    (w : Prefix k K) :
    expect (TimeProfile.fixedCountPMF cuts)
      (fun ω => (prefixCount w ω : ℝ)) = prefixMean cuts w
```

This route needs neither `2≤k` nor legal positive mass, and it handles
the empty prefix without selecting any padding digit. The first-moment
proof may remain in a small adapter module importing `ExpectedMass` or
`FixedCountMoments`; only the integral/sum adapter is needed in the
minimal shared probability module.

## Proposed exact LB-01 target statements on the current names

These are proposition-valued target definitions to freeze, never proof
constants. They expose actual laws and do not bundle the desired
identities into assumptions:

```lean
def PhysicalMatrixLawTarget : Prop :=
  ∀ (k N K : ℕ) (cuts : TimeProfile.Cuts k N K),
    physicalInverseLaw cuts = matrixLaw cuts

def MatrixGraphLawTarget : Prop :=
  ∀ (k N K : ℕ) (cuts : TimeProfile.Cuts k N K),
    matrixLaw cuts = graphMixtureLaw cuts

def PhysicalGraphEventTarget : Prop :=
  ∀ (k N K : ℕ) (cuts : TimeProfile.Cuts k N K)
    (A : Permutation N → Prop),
    probability (physicalInverseLaw cuts) A =
      expect (TimeProfile.fixedCountPMF cuts) (fun ω =>
        probability (uniformPermutation N)
          (fun π => A (componentSort (shuffleEdges ω) π)))

def PhysicalInversionTVTarget : Prop :=
  ∀ (k N K : ℕ) (cuts : TimeProfile.Cuts k N K),
    tv (physicalInverseLaw cuts) (uniformPermutation N) =
      tv (physicalForwardLaw cuts) (uniformPermutation N)
```

All four statements make sense with zero deck size, K=0, and zero piles.
The full graph-law statements need no `hN` or `hk` premises even though
the chosen foundations adapter needs them. If an implementation uses
the stronger adapter, it must discharge degenerate cases separately
rather than silently narrow these types. If the coordinator deliberately
freezes the application-only range `2≤k`, `2≤N`, that narrowing should
be visible in the comparison record; it is not needed mathematically.

A useful separate invariance target uses canonical
`TimeProfile.columnReindex` coordinatewise:

```lean
∀ (k N K : ℕ) (cuts : TimeProfile.Cuts k N K)
  (σ : Permutation N),
  (TimeProfile.fixedCountPMF cuts).map
      (fun ω j => TimeProfile.columnReindex cuts j σ (ω j)) =
    TimeProfile.fixedCountPMF cuts
```

The dependent product equivalence and existing uniform-average
invariance establish this. One must not infer that `stableSort` itself
is equivariant: stable tie ordering changes under arbitrary row
relabeling, and the correct graph-mixture argument counts the resulting
fibers instead.

## Exact target review, second pass (2026-10-01)

Reviewed all declarations then present in `Shared/{Smoke,Model,Path,
Empirical,Statistics,Adapters}.lean` and
`Contracts/v1/{ModelThinning,FactorialOccupancy,Ascent,Endpoints}.lean`.
No compilation was performed by this reviewer. The coordinator was
type-checking this source concurrently, so proof-only elaboration fixes
are outside this statement verdict.

**Verdict for the inspected mathematical types:** no false domain,
hidden target hypothesis, wrong law, or numerical formula was found.
The previously reported product-lex and classical-decidability issues
are corrected in the inspected source. The physical definitions retain
the correct composition convention. This approves the mathematical
content of these current types, subject to successful checking and the
interface-completeness points below; it is not approval of a complete
seven-lane contract inventory, which does not yet exist in this snapshot.

### Operator binding and exact finite model

`Statistics.exactFactorial` was written as

```lean
falling N (∑ i, r i) * ∏ j,
  (∏ a, falling (cuts.count j a) (requestedCount w r j a)) /
    falling N (∑ i, r i)
```

The division is inside the body of the outer `∏ j`; the leading
`falling N R` is outside it. Thus the expression has the source value

`(N)_R * ∏ j, ((∏ a, (n_j,a)_(m_j,a)) / (N)_R)`.

In particular, K=0 gives `(N)_R`, not 1. R=0 gives 1, and when
`R≤N` the denominator `(N)_R` is positive, including N=R=0 where it
equals 1. The target correctly includes `R≤N`; removing it would
make cancellation with the totalized zero denominator unsafe.
For readability and to make future diffs unambiguous, explicitly
parenthesize the quotient inside `∏ j` before freeze, or name the
per-column factor. This is a request to expose the existing intended
binding, not to change the formula.

The same binder scoping means `prefixMass` and `thinningQ` are products
of individual ratios, as intended. None divides a whole product only
once. `requestedCount` correctly counts requests with multiplicity
`r i`, and the injectivity hypothesis in `ExactJointFactorial` prevents
double allocation to one word across differently indexed categories.
`falling` uses `Nat.descFactorial` before casting; it vanishes when more
rows are requested from a pile than it contains. No positivity
assumption on all piles is needed for the exact formula.

`-t^2`, `-s^2`, and `-Δ^2` in the exponential bounds have the ordinary
Lean binding `-(t^2)`, not `(-t)^2`. The real exponents are explicitly
typed in the relative-factorial and occupancy targets. Cardinalities
are cast to reals before the real deviations, powers and divisions.

### ModelThinning target-by-target assessment

| Target | Assessment |
|---|---|
| `ColumnIndependence` | Correct unconditional product-expectation identity for the actual dependent-product uniform law. No row independence is asserted. Canonical `column_product_factorization` plus `expect_eq_integral` is the compatible input. |
| `GraphRepresentation` | Correct equality of matrix stable-sort law and independently sampled component mixture. It is pending, not assumed by the model. |
| `GraphEventIdentity` | Correct matrix-model event version; the inner uniform permutation is independently resampled by construction. The matrix qualifier is honest, and `PhysicalMatrixBridge` supplies the later physical specialization. |
| `PhysicalMatrixBridge` | Correct actual law target, with no precondition that already identifies the laws. It includes degenerate sizes and columns; this is mathematically sound. |
| `InversionTV` | Correct general finite-permutation statement for arbitrary PMF and uniform comparison. It is stronger and more reusable than just the physical specialization. |
| `SuccessiveThinning` | Correct `M>0`, all `s>0`, and `m_j≤M` domain. Subsets generated by initial segments under independent uniform permutations have exactly the required uniform subset law. Empty d gives X=M and Q=1, so the first inequality becomes equality. |
| `PrefixTails` | Correct concrete canonical-law tails, including zero-mass and empty prefixes. For mean zero, the non-strict half-mean event has probability 1 and the bound is exactly 1. No fixed-word result is being substituted for uniform concentration. |
| `AllPrefixConcentration` | Correct finite failure bound for N≥2 and ε>0. The raw-prefix type enumerates each length-m word once. Bound `2(K+1)k^K` covers the number of prefixes whenever the nondegenerate cut array exists; degenerate empty-alphabet cases are trivial or infeasible. |
| `PrefixFailureUniform` | Correct uniform quantified decay for `K≤T log N`; k,T,ε,δ are before N₀. N₀ is free to be enlarged to 2 although its existence clause does not explicitly say so. |
| `ResidualLaw` | Correct positive-probability conditioning and population N-b, with injective prescribed labels and an arbitrary bijective enumeration of unused labels. Column counts are actual subtractions. The RHS is the pushforward of the actual residual fixed-count PMF, so independence is not silently assumed as a field. |

`ResidualLaw` deliberately requires b<N, matching the assigned lane.
Its positive-probability premise is the legitimate condition for a
conditional law, not a desired conclusion. The unused-label map has
both injectivity and the exact range-complement condition; with its
domain size N-b this is sufficient. The row transpose
`fixedCountPMF residual |>.map sampleRow` has the correct target type.

### FactorialOccupancy target-by-target assessment

| Target | Assessment |
|---|---|
| `ExactJointFactorial` | Correct exact formula with distinct categories and R≤N, including R=0 and K=0. |
| `RelativeJointFactorial` | Correct error scale `(K+1)R²/N`, with fixed c,C before D,N₀ and all k,K,d,cuts,words,r afterward. Selected pile hypotheses apply to the supplied words. The restriction R≤N^(1/5) implies R≤N once N₀≥1. |
| `BonferroniSandwich` | Correct even-m upper sandwich, with m≥2 and remainder `(m-1) choose(n,m)`. |
| `BonferroniProduct` | Correct product sandwich with the three remainder terms. It follows from the individual nonnegative errors and indicators bounded by 1; no tail truncation assumption is present. |
| `CentralComparison` | Matches the source two-variable bound, moments through total degree 2m, and coefficient 3. The hypotheses allow control of the polynomial remainder expectation rather than merely a tail probability. |
| `CentralComparisonOne` | Matches the source one-variable moments-through-m version and bound. |
| `RareSandwich` | Correct coefficient 1/3 on the third descending factorial, not the historical false 1/6. No mean-positivity assumption is needed. |
| `UniformOccupancy` | Correct actual-model relative marginal and pair bounds and resulting variance estimate. It places no artificial restriction on the means and no factorial-moment assumption in the final model theorem. The constants depend only on fixed c,C. |

Allowing arbitrary k and family size after N₀ in the last two
asymptotic targets is appropriate: the fixed lower bound cN on every
selected pile controls the requested digits, and the exact error
calculation uses R and K, not ambient alphabet size. A `Finset` family
already guarantees distinct words. The variance bound may use the
same D after enlarging D to cover the pair estimates.

### Ascent target-by-target assessment

| Target | Assessment |
|---|---|
| `ComponentConcentration` | Correct one-sided bounds for the actual component ascent observable, with M>0, t>0, and only `|H|≤M`. It does not revive the false general block-difference lemma or add a boundary restriction. |
| `ComponentExpectation` | Correct coefficients `|E(H)|/2 + |G∩E(H)|/6 - |∂H|`; integer boundary includes the exterior deck boundary. |
| `UniformScan` | Correct N+1 scan locations and denominator `|H₀|`, with nonempty template and s>0. It does not incorrectly replace template size by clipped size. |
| `ComponentComparison` | Correct conditional failure inequality and positive gap `Δ=r/6-d-s`. The event uses `≤ e/2+s`, with no strict/non-strict reversal. |
| `UniformGraphScan` | Correct uniform conditional scan success from deterministic geometry and an existing excess-edge translate. N₀ depends only on a,δ,D,ε; H₀ and G follow N₀. This is a legitimate generic conditional intermediate theorem, not an actual-shuffle endpoint. |

No upper bound on `|H₀|` is necessary for `UniformGraphScan`: the
existence of a translate with at least `|H₀|^(1/2+δ)` edges already
restricts its possible size, and the uniform tail comparison only
needs the displayed lower bound. D=0 is harmless, often making the
nontrivial geometry premises impossible. Zero retained boundaries and
empty clipped sets are covered by the finite formulas; proof cases
must handle them rather than divide by their count.

### Endpoints and transfer assessment

`ProfileIntervalErrors` has the correct ordered empirical interval
domain and α∈[2,4]. `ProfileMarginErrors` uses explicit terminal
losses, with `13e/2` on the main Λ error. The terminal constant 14 is
safe using the elementary bounds `a≤log k`, `ψ_α≤4log k` and the
sharper special bound `ψ_2≤2log k` (the latter follows from
`sum p_l²≥p_max²`). For a pair s≤u≤T, clipping both endpoints to S_N
removes at most T-S_N length from the B_α interval; it does not remove
two disjoint full terminal intervals. The corresponding direct error
is at most `(7/2+4+4)log(k)(T-S_N)=23log(k)(T-S_N)/2`, plus the
`13e/2` common-cost error. Thus 14 has room. LB-07 must prove the
needed ψ₂ bound or use the sharper source bounds; the canonical
generic `4log k` bound alone is not enough to justify every naive
triangle-inequality decomposition with constant 14.

`MarginTransferTarget` legitimately accepts interval errors as the
input of a generic consequence. `ProfileTransferTarget` itself
constructs those errors, so they have not leaked into the final macro
endpoint as hypotheses. It chooses the partition and its regularity
scale first, permits an arbitrary supplied positive rho ceiling, fixes
rho then phi, and requires scalar integrability for that same P. The
profile is fixed before N₀, which is consistent with uniformity over
all cuts for a fixed profile.

`LargestOnlyTarget` is a physical-law asymptotic theorem with a fixed
positive empirical beta margin and no local-good parameters.
`ColdOnlyTarget` matches `prop:cold-lower`: positive eta fixes kappa
and kappa0; positive rho, chiGood and gamma and the exact
`2*rho*log k≤kappa0/100` restriction are fixed before N₀. The beta
cutoff is strictly `< kappa0`, as in the source.

`EmpiricalCombinedTarget` is a faithful uniform E. Its cold alternative
omits the terminal beta cutoff because assembly can split at kappa0
and use the largest-only theorem on the other branch. The largest
alternative remains usable even when the supplied cold parameters
are inadmissible. Although the fixed margins `etaLargest` and
`etaCold` can differ, the proof can take the maximum of the two
required N₀ values. There is no TimeLaw, macro integrability, witness,
localization, concentration, graph correctness or scan-success premise
in E.

`MacroscopicIntegrableTarget` is a faithful strengthened M, not the
unchanged old macro assertion. The partition is selected independently
of N and before its integrability premise; it is also selected before
the profile, a permissible stronger uniformity because the regular
partition controls all simplex points. The rho0 ceiling is explicitly
tied to eta/2, and local-good constants, frequency/mesh parameters,
accuracy and fixed profile precede N₀. All N and deterministic cuts
follow N₀. Its law is the chronological physical inverse law, and its
numerical premise is exactly the maximum of the two macro margins.

The new `ScalarIntegrable` clauses are visibly additional to the old
arbitrary `TimeLaw`/fixed-partition `AlmostLike` freeze. The old
definitions and signatures are not edited. The report and eventual
receipt must continue to say that M is stronger in assumptions and
that the original totalized-TimeLaw theorem remains uncertified.
Neither E nor M should be described as proved at LB-00.

### Remaining interface inventory before complete lane release

At this inspection only the four target modules above existed. The
following distinctions matter:

* **Contract-completeness requirement:** LB-05 witness/one-column
  exports, LB-06 type/mass-bin exports, and LB-09 geometry/localization
  exports have no typed targets or witness/geometry data declarations
  in this snapshot. These are essential interfaces for the promised
  seven independent first-stage lanes and their consumers. They need
  a separate reviewed module, not a generic text placeholder that
  assumes their desired conclusions.
* **Explicitly requested public lane results still absent as targets:**
  LB-02 one-column all-s transform; LB-04 joint relative-order
  independence, the binomial boundary probability, centered Bernoulli
  MGF, two-sided concentration, and deterministic least successful
  translate; LB-10 the finite largest-word exponential TV bound.
  These may be added as reviewed additive target definitions or
  explicitly enumerated proof-owned exports. The one- and two-sided
  tails are mathematically related, but the prompt explicitly asks for
  both export forms.
* **Useful source adapters not yet proved in Shared:** the raw-prefix
  exact first moment, sorted prefix interval, upper-minus-lower count,
  stable tie monotonicity, and clipped-size/rank-image identities.
  Where these are not completed by LB-00, give their shared signatures
  a single explicit owner. Do not leave every lane to invent an
  incompatible duplicate.
* **Internal rather than necessarily public obligations:** LB-01 row
  relabeling invariance and the interleaving slot formula; LB-08
  positive prescribed-row events, residual selected-pile bounds and
  b=2,3 conditional collision stability. Their proofs are needed in
  the owning lane but the final unconditional targets already avoid
  assuming them. Making them named typed exports is useful if another
  lane will consume them.

A suitable missing finite largest-word target, on the existing names,
is the universally quantified implication for k≥2, N≥2, any K and
cuts, and an integer m with `2≤m≤N` and
`(m:ℝ)≤maximalMean cuts hN/2`:

`1 - exp(-chernoffConstant * maximalMean cuts hN)
   - ((N-m+1 : ℕ):ℝ)/(m.factorial:ℝ)
 ≤ tv (physicalInverseLaw cuts) (uniformPermutation N)`.

This is strictly more quantitative than `LargestOnlyTarget` and is
explicitly required by LB-10; it also fixes the contiguous-run test
that is otherwise only implicit in the asymptotic endpoint.

The current proposition-valued targets themselves are honest pending
specifications. No target is introduced as an axiom, dummy instance or
proof field. `RowPrescription` has only row/word data, with injectivity
and positive conditioning stated separately. The same separation must
be preserved in the forthcoming witness and geometry structures.

## Geometry and additional finite interfaces, third pass (2026-10-01)

The coordinator subsequently added `Shared/Geometry.lean`,
`Contracts/v1/WitnessGeometry.lean`, and
`Contracts/v1/AdditionalFinite.lean`. All were inspected against the
source witness, type, geometry and relative-endpoint statements. The
exact-factorial column quotient is now explicitly parenthesized, so
the earlier readability request is resolved.

**Verdict:** the new data/proposition separation is sound, and no false
numerical assertion or hidden endpoint hypothesis was found. The
previous absence of LB-05/06/09 typed interfaces is resolved by this
addition, subject to successful compilation and final freeze review.
The new source remains specification-only for its substantive results.

### Shared geometry representation

`WordOn k I := (j : I) → Fin k` records only actual selected columns,
without unused coordinates. Sorting `I.attach` by increasing column
index before converting to a list gives the chronological lexicographic
order. This fixes the prefix/type overcounting risk identified in the
initial review. `massOn` is a product of per-column ratios. The min in
`prefixAt` only totalizes an adapter; actual witness specs impose all
depth inequalities needed to identify it with the intended prefix.

`ColdWitnessData` contains only the two depths, bridge length and tilt.
`RoundedTypeData` contains only integer counts and bin index.
`ColdGeometryData` contains only the ambient word, two type-data
objects, bridge/reserve words and two nominated good-column indices.
None contains proof fields, desired localization, concentration, law
identification, or TV bounds.

`WitnessSpec`, `TypeDataSpec`, `TypeApproximation`, `BridgeSpec`, and
`GeometrySpec` are separate proposition definitions. Conditional
intermediate results may accept these already-proved specifications;
the concrete geometry target must construct them from the empirical
premises, and the final E/M types do not accept them as assumptions.
This separation meets the contract requirement.

The derived relative set is exactly the integer points in a union of
half-open scaled relative probability intervals, using the actual
ambient prefix mean. Its clipping and random translation use the same
one-based-rank map as the previously reviewed path model. The full
family is an image of the Cartesian product of actual prefix and tail
classes. Its injective concatenation/cardinality formula is a proof
obligation expressed in `GeometrySpec`, rather than an injected
cardinality assumption inside the data structure.

### Witness/type/geometry target assessment

* `ColdWitnessTarget` matches the source's weaker witness bridge
  ceiling `2*rho*log k≤kappa eta/100`, not the stronger later geometry
  ceiling. Its output includes ordered grid endpoints, a bridge of
  ceiling length, two good columns, theta∈[3,4], the source eta/2
  lower bound for F, the 3κ/5κ J buffers, entropy and collision slack,
  and the terminal mean bound. Its thresholds are uniform in all
  cuts after N₀. The stronger kappa0 ceiling remains correctly present
  in the cold endpoint and geometry construction.
* `OneColumnTiltTarget` has the correct monotonicity and continuity
  domains, entropy identity `H=alpha*I-psi`, and comparisons
  `psi₂≤2a` and `2psi₂≤psi₄`. `EmpiricalTiltTarget` is the finite-sum
  specialization on the ordered empirical horizon. Neither requires
  any macroscopic temporal integrability.
* `RoundedTypeTarget` has the correct parameter order: Ctype depends
  on k,C; Cround and N₀ may additionally depend on T,xi,m; the actual
  partition, cuts, selected columns and alpha follow N₀. It permits
  arbitrary position sets of size at most T log N, so it is usable by
  both prefix and tail constructions. The approximation error matches
  the source with explicit constants.
* `TypeDataSpec` exposes exact rounded counts, support on retained
  digits, nonempty raw and selected classes, the multinomial count,
  maximal-bin/least-index tie rule, exact cardinality and mass-bin
  identities, and a uniform lower digit probability. The positivity
  of the retained denominator follows from `xi<1/(4k)` and the
  simplex maximum; it is an output to prove, not a free hypothesis of
  `RoundedTypeTarget`. Empty cells and empty I are included. Products
  and quotients in the multinomial expression have the intended
  per-cell scope, although explicit parentheses are again useful.
* `BridgeSpec` correctly realizes the two reserve modifications at
  separate ordered good columns, retains the lex inequalities, and
  uses the source probability lower bound `chiGood²*k^(-bridgeLength)`.
  The displayed logarithmic upper bound includes both ceiling and
  good-digit losses. It does not assume independence of reserve
  counts.
* `GeometrySpec` matches the source exponents ellp,h,z,g, uses the
  tail after bridge deletion, and has the exact selected family mass
  range `exp(-2) N^z < N lambda_y ≤ N^z`. The constants
  `exp(-2) N^h ≤ M ≤ 2N^h` and clipped boundary `≤4 sqrt M`
  are permissible sufficiently-large-N strengthenings of the source
  asymptotic statements, because fixed kappa slack absorbs rounding
  and the two clipping edges. They need actual uniform proofs, but
  do not add a new scientific assumption. The selected-pile floor is
  the source `min xi (min chiGood (1/k))` and applies to full words
  and reserves.
* `RelativeEndpointTarget` gives both exact first-difference
  identities and the source finite concentration consequence.
  `sidePrefix` truncates immediately after the differing digit, so
  later x coordinates do not contaminate the cylinder. Its formula
  correctly uses the ambient fluctuation only on the upper side.
  The bound is exactly
  `A*((2 sqrt(kK)+1) sqrt(muA)+2kK+1)`.
* `DeterministicColdGeometryTarget` may accept any already-proved
  witness; its quantifiers choose xi and P before N₀, with every
  actual witness after N₀. The two good columns in `WitnessSpec`
  suffice for this deterministic stage; no additional density
  premise is needed.
* `LocalizationTarget` is an honest conditional intermediate with
  uniformity over W,G after N₀. `ColdGeometryFromEmpiricalTarget`
  then existentially constructs the witness and geometry and proves
  the localization probability from concrete empirical/local-good
  inputs. Thus localization is not leaked into an empirical endpoint
  hypothesis.

### AdditionalFinite target assessment

All added statements are mathematically consistent with the source:

* `RowRelabeling` concerns the law of the raw row matrix. It does not
  incorrectly assert equivariance of stable sorting through ties.
* `StableTie` and `PrefixRanks` use the same sorted-position→original
  label orientation and zero-based rank cuts as the canonical model.
* `HypergeometricTransform` covers every positive s with x,m≤M and
  M>0. Its selected subset is uniform via the inverse permutation;
  this orientation does not change its law.
* `ResidualJointFactorial` subtracts the number of prescribed copies
  of each word from its occupancy inside the conditioned integrand.
  The numerator uses the residual pile counts, the denominator and
  leading factor use N-b, and R≤N-b prevents zero-denominator misuse.
  The positive-event and injective-label hypotheses justify all
  subtractions. Its direct proof can be owned by LB-03 without making
  LB-03 depend on LB-02's residual-law theorem.
* `RelativeOrderIndependence` fixes each desired relative order by a
  full permutation restricted to its finite set. Every restricted
  order can be represented this way; the joint event has the product
  inverse-factorial probability for pairwise disjoint sets. Empty
  sets give the harmless factor 1.
* `BoundaryAscentProbability` remains true when a set is empty, since
  both the event probability and the displayed inverse binomial
  coefficient are then 1. No missing nonemptiness hypothesis is
  necessary.
* `BernoulliMGF` has the correct centered indicator, real λ without a
  sign restriction, and Hoeffding constant 1/8.
* `LeastSuccessfulTranslate` constructs a least index from G and H₀
  only, with no sampled permutation argument. The least witness is
  unique; a deterministic choice function can be defined by the lane
  from this target's proof and has no dependence on independent π.
* `FiniteLargestWordTV` matches the requested exponential bound.
  Its `2≤m≤N` hypotheses imply N≥2, so `hN:0<N` is sufficient in
  the signature. It needs no k≥2 hypothesis: for K>0 and N>0 the
  cut array forces a nonempty alphabet, and K=0 is well defined.

The explicit two-sided component-concentration export is still absent
in the inspected target inventory. It is a direct union-bound
consequence of `ComponentConcentration`, so this is a small interface
completion issue rather than a mathematical flaw. The earlier
one-column, finite-largest-word and relative-order inventory gaps are
now resolved.

## Final compiled-contract approval — 2026-10-01

**APPROVED for the LB-00 shared-foundation and typed-contract release.**
This final verdict supersedes the intermediate inventory gaps above.
It does not certify the 58 pending lower-bound targets as proved, and
does not certify the original unchanged arbitrary-TimeLaw theorem.

The final review was read-only apart from appending this report. No
build or dependency-cache mutation was performed by this reviewer.
The coordinator's refreshed `audit/LB00/build-v1.log` ends with
`BUILD_OK`. Its compiled declaration records were independently
compared with the reviewed source and generated public export document.

The comparison checked all 211 public names, their exact elaborated
types, every displayed proposition-valued target body, and the recorded
source file/line locations in `Contracts/v1/EXPORTS.md` against
`audit/LB00/public-exports.json`. There were zero differences. The
compiled audit contains 364 declarations, 17 proved public routine
adapters, and 58 pending proposition-valued targets. The axiom union
is exactly `Classical.choice`, `Quot.sound`, and `propext`; no custom
axiom or unproved target constant appears as evidence.

The final additions are accepted:

* `GenericQuadrature` states both cell-mass and observable-specific
  scalar interval integrability, in addition to spatial continuity
  and bounded oscillation. Its explicit error is the source finite
  quadrature error plus the two-endpoint step-interpolation loss.
  It does not use the a/psi predicate to justify an arbitrary f.
* `ResidualRelativeFactorial` and `ResidualMeanComparison` keep a
  fixed maximum number of prescribed rows b0 before N₀ and use the
  actual residual population N-b and residual pile counts.
  `ConditionalCollisionStability` tests occupancy after removing the
  prescribed copies, which is necessary when the prescription itself
  contains the tested word. These statements are uniform in all
  later prescriptions with positive probability.
* The two-sided component tail is explicit, with the same constant
  and observable as the two one-sided tails. `MaximalMeanIdentity`
  records the actual exact beta exponent. `CollisionChebyshev` has
  the correct positive-mean and positive-relative-threshold domain.
* The final `ManyEdgesTarget` uses the exact random translation
  `q*=lowerRank (prefixAt W.ms G.ambient) ω`, as in
  `lem:many-edges`, and exponent `1/2+kappa eta/5`. The refreshed
  compiled body and export document both contain this fixed-q
  statement. The temporary existential-translate weakening is gone.

E remains the uniform concrete chronological-physical inverse-law
lower-bound target, without a macroscopic profile premise and without
any assumed witness, localization, graph identity, concentration or
TV result. Its largest-word alternative has no local-good restriction.
M remains the separately named target with the visible same-partition
scalar-integrability addition, correct partition/rho/phi/profile/N₀
order, and the same physical law. The original frozen TimeLaw,
AlmostLike and integrated cost definitions remain the basis of the
adapters; no regularity is inferred from their totalized definitions.

All inspected data structures continue to contain data only.
Substantive specifications are separate proposition definitions and
their construction remains an owning lane's pending proof obligation.
The typed exports now support the intended dependency split, including
independent LB-03 residual factorial work and separate LB-07 transfer.

This approval is bound to the following SHA-256 snapshots, with paths
relative to `formalization/lower_bound_v2`:

```text
737a259499bd3eea31843ddc6a82e498a58dc606c6a94a84b409eb35fe179253  RiffleLowerV2/Shared/Adapters.lean
84ea013c6f9c64073700be1dced470f11fa30a9b3d0b79a59dde63a099cf817e  RiffleLowerV2/Shared/Empirical.lean
cb992d0297bcf75ada15ff6154a146caadfa3d984629aafd70f74feef6bfbb09  RiffleLowerV2/Shared/Geometry.lean
cceadf1b4a5be2f412fe15a9b52b7b7f3c67bfa6d19270955f7c338f01e90930  RiffleLowerV2/Shared/Model.lean
513afea203a5ad1a3b851fdb8317b4f6473d2c54e1c0466139b349530563acbf  RiffleLowerV2/Shared/Path.lean
41544e0cc785a589dedcd14757b1bf2b69747c5512193f80fcdda277c9b1939a  RiffleLowerV2/Shared/Smoke.lean
dd57ff2f4bbac3e26176809ee15081b58510b041e6dee418f65d31d4fc26fb69  RiffleLowerV2/Shared/Statistics.lean
b94a1cb35d7204e4e6f0c8dbb277ebc471ec16307a38d2351ef290de6da20869  Contracts/v1/AdditionalFinite.lean
3816a1346b6f770837169835f93abc02a85f14c5f6c4d1d9a748f9d17602ab2b  Contracts/v1/Ascent.lean
fd005b12cc24ebab117cf08b244d28cef07c31ce02a4d429625a7e92c1e874ea  Contracts/v1/AssemblyInputs.lean
ee995fe56f4815ec78d6d2bd0d76ed4aecb357883417a57958d0dd3ae19df0c0  Contracts/v1/Endpoints.lean
80be112ec4fe3b811738bcb75a0aa29b26ef31d7bafd5d264fbee8ba21f7253d  Contracts/v1/FactorialOccupancy.lean
bdb0c4c3af301658c9798d191b3dfef1ac34d9df02fb988b1c10214d6b039288  Contracts/v1/ModelThinning.lean
fd67fc92015806b8cc78d6b1f4a558ed512a41f818c732435e7e59e664e8b933  Contracts/v1/TransferFinite.lean
bbd3f28678e95ace37f07c0d993992f20fd4dc4d565ccbc11d0b8a4f1ba822bc  Contracts/v1/WitnessGeometry.lean
ccdc854ed8b5a545de6ac3f719ac6367706dfd85f73f29f8620f0df20cbd9da1  Contracts/v1/EXPORTS.md
2c3aec14d56e7eab2d175e9e1fb12d9bab3f65ce7bbb3d7e02aa3880932f64e4  audit/LB00/public-exports.json
ba5f24f28b0e0e12de9073bc9354f29c2639edaaa870f2d77b8e1c3cb0c35fbd  audit/LB00/compiled-declarations.json
190e2608b27ebbcbe46bf3bbe2afc8a5d957f982b93c6218db197c06eca5f4f7  audit/LB00/verification.json
8d303615294b4a4cc4938ca6f093d8744f02ae62e46c89705c1905fc8ef68a61  audit/LB00/build-v1.log
```
