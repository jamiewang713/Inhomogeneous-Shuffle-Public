# Actual stable words to the time-profile numerical theorems

This is a bounded integration reconstruction, not a new freeze or implementation. It compares the existing `Riffle` model/stable-word definitions with `TimeProfile.Ambient`, `Crossing`, `SideMass`, `ExpectedMass`, and `SourceNumerical`. No assumption is changed and no expected-mass identity is taken as a premise merely because the two expressions have the same informal meaning.

## Outcome

The finite definitions are compatible. The remaining work is a small collection of genuine representation, expectation, and branch implications. There is no new numerical inequality needed to obtain `Crossings`, `StableAt`, or `ParentCrossing` from the appropriate actual stable branch.

Three limitations must remain explicit:

1. `Riffle.Retained` alone does not assert membership in the left/right boundary families. The actual `AdmissiblePair` supplies `RawPair`, and **nonterminal** `RawPair` supplies the genuine crossings.
2. The bare `Riffle.Setup` has an arbitrary real b and no time/horizon data. It does not imply a small ambient-mass error, a small ambient-time error, or `K=floor(T log N)`. Those are existing source inputs to be represented, not consequences of Stable membership.
3. The equality between `Riffle.expectedCount` and a literal fixed-count expectation is not yet provided by `TimeProfile.expected_cF_eq`. The former is a weighted finite full-word sum; the latter relates two definitions internal to the time-profile package. A bridge must first connect the row events and their expectations.

All fluctuation statements here concern deterministic maxima of expected side masses. They do not repair or assert stochastic endpoint anti-concentration.

## 1. Exact finite adapters

Fix the existing model D and setup A. Write N=D.N, K=D.K, k=D.k. From `D.one_lt_N` and `D.two_le_k` derive N>=2 and k>=2.

The natural cut adapter is

    cuts.count j l = D.n j.val l.val,
    cuts : TimeProfile.Cuts k N K.

Its `sum_count` field follows from `D.sum_counts j.val j.isLt` by `Fin.sum_univ_eq_sum_range`. On legal finite indices its profile satisfies exactly

    TimeProfile.prob (cuts.profile hN j) l
      = (D.n j.val l.val : Real)/(N : Real)
      = (Riffle.prob D j.val l.val : Real).

No property of D.n outside `i<K` and `l<k` is relevant.

For a legal list x of length n<=K choose a full finite vector X with

    (X j).val = Riffle.digit x j.val       whenever j.val<n.

A canonical adapter pads with digit 0 after n; k>=2 makes 0 a valid alphabet element. This padding is not claimed legal in its pile. Only `LegalPrefix ... X n` is needed, and that follows from x's legality and `Cuts.profile_pos_iff`. Alternatively `Riffle.full_extension` supplies a legal full completion, but a new existential choice is unnecessary.

For every list u prefixing x, the same X agrees with u before u.length by `Riffle.digit_prefix`. Therefore one vector can represent x, its parent, the boundary join, and the ambient prefix simultaneously. Values after x.length affect none of the required prefix quantities; cE does not use X at all.

`TimeProfile.positions K a b` is exactly the finite-index version of `Finset.Ico a b` whenever b<=K. The map `j -> j.val` is the needed bijection, with inverse `i -> (i, proof i<K)`. This reindexing is required for sums, products, and maxima; it is not a change from the source's zero-based interval.

## 2. Exact size-cost correspondence

For every ambient extension u prefixing x,

    Riffle.cL A u
      = TimeProfile.cL N (cuts.profile hN) X A.b A.w.length u.length.

Reindex the Ico sum to `positions`, replace the digit by the matching coordinate, and use

    1 / ((D.n i l : Real)/(N : Real)) = (N : Real)/(D.n i l : Real).

The denominators `Real.log N` and `TimeProfile.logScale N` are definitionally the same. Positivity of the actual pile comes from legality; no exact ambient-mass assumption is needed for this identity because both sides retain the same b offset.

The generic prefix version above also gives the indispensable parent identity

    Riffle.cL A (Riffle.parent x)
      = TimeProfile.cL N (cuts.profile hN) X A.b A.w.length (x.length-1),

using `Riffle.parent_prefix` and `Riffle.parent_length`. One should not compare a differently padded parent vector without proving its prefix agreement.

There is currently no `Riffle.cE` declaration in the stable-block package. The source tail exponent should be represented by the already defined

    TimeProfile.cE N (cuts.profile hN) x.length.

It is exactly the finite source sum of `-psi(2)/log N` over `[x.length,K)`. For the collision package, the additional genuine link is

    N^(TimeProfile.cE N p n) = product_{n<=j<K} sum_l p_j(l)^2,

and the exact without-replacement two-row tail factor is **at most** this product. It is generally not equal to it. The equality follows from positive squared-probability sums, finite log/product identities, and real-power conversion. The inequality follows from the existing per-column collision comparison. It must not be replaced by an asserted equality with the factorial collision factor.

## 3. A genuine expected-count bridge

The two relevant existing definitions are:

    Riffle.expectedCount D E
      = N * sum_{omega : Fin K -> Fin k}
          if Riffle.fullList omega is in E then
            product_j Riffle.prob D j.val (omega j).val
          else 0,

with values in NNReal, and a real integral over `TimeProfile.fixedCountMeasure cuts` for actual fixed-count shuffle samples.

A useful minimal bridge is the following equality for every set E of list words:

    (Riffle.expectedCount D E : Real)
      = integral_sample
          #{i : Fin N | Riffle.fullList (TimeProfile.sampleRow sample i) is in E}.

This can be proved from existing theorems, rather than assumed. Partition the finite row set by its complete vector word omega. For each omega, `TimeProfile.expected_box_count` applied to singleton allowed sets `{omega j}` gives expected multiplicity

    N * product_j TimeProfile.prob (cuts.profile hN j) (omega j).

Multiply by the E-membership indicator and sum over the finite vector-word space. `TimeProfile.fixedCount_integrable` justifies every finite integral interchange. The cut/probability adapter turns the resulting real finite sum into the coercion of `Riffle.expectedCount`. No temporal measurability of the profile is involved in this finite expectation identity.

Every actual `sampleRow` produces a `Riffle.Full` list. Its length and alphabet bounds follow from `fullList_length`/`fullList_bounded`; positive counts follow from `sample_entry_count_pos`, or from `sample_row_legal` and `Cuts.profile_pos_iff`. This legality is crucial for the event correspondences below.

For a legal u prefixing x and the matching vector X, the actual sampled-row predicate

    Riffle.fullList row in Riffle.Cylinder D u

is exactly the coordinate-prefix predicate defining `TimeProfile.prefixRows X u.length`. Therefore the general bridge and `TimeProfile.expected_prefix_count` give

    (Riffle.expectedCount D (Riffle.Cylinder D u) : Real)
      = TimeProfile.prefixMass N (cuts.profile hN) X u.length.

Do not prove this by declaring the predicates equal on **all** vector words: an alphabet-bounded vector can use a zero pile, whereas `Cylinder` requires legality. On actual sample rows legality is proved. An alternative proof directly on the product-weight sum may instead use `Riffle.weight_eq_zero_of_not_legal` to remove illegal zero-weight vectors; that is valid but must be explicit.

## 4. Side events, maxima, and cF

Suppose x extends A.w and `A.w.length<=i<x.length`. The already proved `Riffle.pieceEvent_iff` identifies membership in `PieceEvent A side x i` with:

    a full legal row extending A.w,
    agreement with x before i,
    the appropriate strict digit comparison at i.

Because i>=A.w.length and x extends A.w, agreement before i already forces the ambient prefix. For actual sample rows, this is exactly `TimeProfile.leftSideRows X j` or `rightSideRows X j`, where j.val=i. Later coordinates are unrestricted in both definitions. Thus the general expected-count bridge, this row-event equality, and `expected_left_side_count`/`expected_right_side_count` give

    (Riffle.expectedCount D (Riffle.PieceEvent A side x i) : Real)
      = TimeProfile.sideMass N (cuts.profile hN) X A.w.length sideProbability j.

This equality is valid for empty side sets as well as positive ones. It uses the original global prefix mass, exactly as both packages intend.

Let v=join y z and suppose v prefixes x. Reindexing the finite supremum over `Ico A.w.length v.length` to `positions K A.w.length v.length` yields

    (Riffle.sideMaximum A side v x : Real)
      = TimeProfile.sideMaximum N (cuts.profile hN) X A.w.length v.length sideProbability.

The NNReal versus `Real.toNNReal` presentation causes no obstruction: the expected counts and side masses are nonnegative, and `toNNReal` of the coercion of an NNReal recovers it. Equality of the suprema must nevertheless be proved by the index bijection. Both empty suprema are zero.

Taking square roots, then the extended logarithms and the minimum, gives

    Riffle.cFAt A v x
      = TimeProfile.cF N (cuts.profile hN) X A.w.length v.length.

`Riffle.cFAt_continuation` identifies the left side with `Riffle.cF A y z`, which is defined using v on both slots. The corresponding time-profile continuation theorem is `TimeProfile.cF_prefix_eq`; either can be used to organize the proof.

Both packages use bottom when the square-root side maximum is zero. The cF equality holds in `WithBot Real`, including a zero side, terminal pairs, and an empty ambient extension. Do not turn `Real.log 0=0` into a finite fluctuation exponent. For a nonterminal actual pair the existing retention theorem or the crossing lower bound then supplies a real F, and uniqueness of the coercion identifies both packages' F.

`TimeProfile.expected_cF_eq` proves that its own side-mass cF is the cF computed from literal row expectations. It becomes the needed cross-package fact only after the preceding event/expectation identifications.

## 5. Actual boundary pairs imply Crossings in the nonterminal branch

Begin with `hp : Riffle.AdmissiblePair A y z` and `hx : x in Riffle.Stable A y z`. Existing theorems give

- `admissiblePair_rawPair hp`;
- `admissiblePair_retained hp`;
- `rawPair_join_desc` and `rawPair_prefix_join`;
- `stable_desc`, so v prefixes x, x is legal, and
  `A.w.length<=v.length<=x.length<=K`.

In the branch `not Riffle.Terminal D y z`, use `boundary_nonterminal` at each boundary word. The left witness index is `i_y=y.length-1`; the right witness is `i_z=z.length-1`. Both lie in `[A.w.length,v.length)`, including when the crossing is in the first column after the ambient prefix.

At i_y the boundary crossing says

    Riffle.leftIndex A i_y < Riffle.digit y i_y.

`leftIndex_mem` says its pile proportion is at least A.chi, and `leftIndex_legal` supplies a `Fin k` digit. Prefix agreement transports the crossed digit to X. That large pile is a summand of `TimeProfile.leftProbability`, all of whose summands are nonnegative. Therefore its sum is at least A.chi. The right proof uses `rightIndex_mem`, `rightIndex_legal`, and the symmetric comparison.

These two witnesses establish exactly

    TimeProfile.Crossings (cuts.profile hN) X A.w.length v.length A.chi.

Only the case distinction is new here, not a model hypothesis. A terminal pair can arise from a no-crossing fallback, so generic terminal pairs do not imply Crossings. They must use the source singleton/terminal route, which deliberately does not require Crossings or a finite F.

Also, `Retained` by itself contains only compatibility and a terminal-or-finite-cF condition. It does not imply the boundary-index witness or the chi side-probability lower bound. The actual admissible/RawPair data cannot be discarded from the bridge interface.

## 6. Stop, StableAt, ParentCrossing, and fallback exclusion

Assume the cF equality gives `Riffle.cF A y z=(F:WithBot Real)`. The already proved

    Riffle.stop_iff_sub_lt
    Riffle.not_stop_iff_sub_ge

translate Stop and its negation into the real inequalities with the unchanged `A.delta`.

For any actual x satisfying Stop, the cL equality gives

    TimeProfile.cL ... X A.b A.w.length x.length - F < A.delta,

which implies the non-strict `TimeProfile.StableAt` used by `source_large_margin`. This is an ordinary weakening of a derived conclusion, not a change to the frozen source assumption.

An arbitrary Stable member is not yet known to satisfy Stop. Unfolding the existing Stable definition gives precisely:

- a terminal singleton, for which no Stop conclusion follows;
- a nonterminal stopped-root singleton, which does satisfy Stop;
- a Gamma member, which satisfies Stop and a parent non-Stop condition;
- a Lambda terminal fallback, which explicitly fails Stop.

For the nonterminal branch, `TimeProfile.source_no_terminal_fallback`, after the cL/cF/ambient bridges, gives Stop at length K and therefore contradicts Lambda membership. This is the correct point to exclude fallback, not a premise to insert into the stable-word adapter.

For a nonsingleton stable family, the two singleton branches are impossible. After fallback exclusion the word belongs to Gamma and the join is not stopped. `Riffle.gamma_first_crossing` then gives

    v.length < x.length,
    Riffle.parent x in Desc D A.w,
    not Stop A y z (Riffle.parent x).

The length inequality implies `0<x.length` and `v.length<=x.length-1`. The parent cL equality and `not_stop_iff_sub_ge` supply the last clause of

    TimeProfile.ParentCrossing N p X A.b A.w.length v.length x.length F A.delta.

Thus every part of ParentCrossing is derived. Gamma membership without the root-not-stopped branch does not by itself justify the strict extension length; `gamma_first_crossing` correctly takes that root fact explicitly.

`source_large_margin` does not require that the block be large as a theorem premise; it supplies the numerical inequality whenever StableAt holds. The large/small distinction is needed later when pairing it with a density estimate. Similarly `source_small_margin` takes the exact ParentCrossing proposition and does not derive it from raw Stable membership.

## 7. Actual profiles and the remaining numerical input binders

To apply SourceNumerical to a previously encoded actual profile, instantiate the deterministic data as follows:

    c = R * P.cellCount,
    cell j = finProdFinEquiv (timeClass j, P.classify (p j)),
    good j a = there exists ha:a<k such that
                 P.IsGoodDigit A.chi (p j) (a,ha).

The existential alphabet proof is immaterial by proof irrelevance and makes invalid natural digits not good. For each actual position before x.length, legality makes this predicate identical to the TimeProfile good-digit predicate on X.

Finite filter extensionality then gives equality of the actual exceptional supports. A joint-cell reindexing gives

    TimeProfile.digitCount ... (q,i,l)
      = goodDigitCount ... (finProdFinEquiv(q,i)) l / log N.

Consequently the actual real cutoff implies `profileR<=alpha` by division by positive log N. If alpha's nonnegativity is needed and an actual ProfileWord is given, it also follows from its nonnegative cardinal and the real cutoff; no extra sign hypothesis is needed. The concrete source alpha is positive in any event.

The profile S/Q formulas follow by finite-sum reindexing. The entropy equality

    TimeProfile.profileH ...
      = typeEntropy (profileKeyCounts (encodeProfile ...)) / log N

needs the count equality, the product equivalence for the joint cell, and the zero-aware entropy normalization. This is a genuine later equality, not already supplied by `profileH_source_formula` alone. It connects the exact fibre count to the H appearing in SourceNumerical.

The following SourceNumerical data are not implied by stable membership:

- the prescribed horizon relation `D.K=TimeProfile.horizonDepth D.N T`;
- AlmostLike for the supplied time law and regular partition;
- the original variational FirstMomentMargin and positive eta;
- the finite ambient approximation and the chosen error budget.

The horizon can be dealt with by constructing the actual model from horizon-indexed Cuts initially, or by explicit transport along the genuine source equality. Choosing a different T to force a floor identity would alter the source profile/margin data and is not justified.

The ambient approximation is exactly

    |A.w.length/log N-r|<=er,
    |log(expectedCount D (Cylinder D A.w))/log N-A.b|<=eb,

after the prefix-expectation equality. It is the quantitative form of the source's ambient `N^(b+o(1))` and time-offset assumptions. A.b is arbitrary in bare Setup, so a small eb cannot be derived from that structure. For the whole deck with w empty, b=1 and r=0, both errors are exactly zero. For a general ambient sequence, their required smallness must be obtained from the source's already assumed approximation and parameter choices.

SourceNumerical evaluates integrated margins at `max r (v.length/log N)` and `max r (x.length/log N)` to accommodate the ambient-time error. One must preserve those clamped times unless an actual ordering proof permits removing max. Exact prefix lengths alone do not imply `r<=v.length/log N` from a two-sided approximate ambient birth time.

There are two distinct constants named C: `A.C` is the boundary-admissibility threshold, while SourceNumerical's C is the regular-partition oscillation constant. They must not be silently identified. SourceNumerical's delta should be A.delta, whose required nonnegativity follows from `A.delta_pos`.

## 8. Minimum genuine bridges and proof order

The essential new equalities/implications can be grouped without introducing any extra scientific premise:

1. **Finite cut/vector representation:** adapter, probability equality, legal-prefix agreement, and Ico/Fin reindexing.
2. **cL compatibility for every represented prefix:** includes the join and parent instances.
3. **Expected-count compatibility:** the general finite row-event expectation identity, or equivalently independently proved cylinder and side-event specializations.
4. **Side-event and cF compatibility:** literal row-event equality, reindexed maxima, continuation, and the WithBot equality including zero cases.
5. **Boundary crossing implication:** actual nonterminal RawPair plus the common-prefix data implies the two TimeProfile crossing witnesses.
6. **Stopping branch implications:** Stop to StableAt; source terminal inequality to no Lambda; Gamma/root case to ParentCrossing.
7. **Profile compatibility:** actual good/exceptional filters and joint-cell counts, followed by profileR and entropy normalization.
8. **Tail power/collision comparison:** exact equality with the product of squared-probability sums, and the one-sided comparison with the fixed-count factorial tail factor.

Items 1--7 connect the already proved actual-profile and source-numerical packages. Item 8 is needed when attaching the collision/density package. None establishes conditional exploration laws or endpoint density. In particular the literal first-moment identities in ExpectedMass do not imply a conditional ambient law or a variance lower bound.

No incompatibility of the finite definitions was found. The genuine work is the stated expectation/event bridge and careful handling of horizon, ambient errors, terminal branches, and the extended-real zero-side convention.
