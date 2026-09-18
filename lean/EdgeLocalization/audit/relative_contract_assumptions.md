# Independent assumptions audit: recentered internal edges

This is a pre-code audit of the proposed relative-coordinate addendum. I reread the permitted TeX at 445–517 and its interval/endpoint conventions at 1202–1250, the endpoint definitions (2.13)–(2.14) in the fixed-column PDF, and the corresponding block definitions in the independent-digit PDF. I checked the existing deck, density, and sorting definitions and proved monotonicity theorem. No Lean implementation, previous definition, frozen file, or mathematical source was changed.

**Verdict: the arbitrary-shift counting inequalities are valid, and the literal source recentering can also be justified if the actual sorted-deck lower-bound and cardinality-preservation bridges are proved as proposed.** An injection alone does not establish preservation of the whole graph: arbitrary shifts may discard edges. Neither route identifies absolute and independently recentered densities.

## Source offset and exact orientation

The TeX uses lexicographically sorted full rows, defines internal prefix edges by equality of adjacent rows carrying that prefix, and at 509–511 recenters positions at the left endpoint of the ambient block. Both older papers define the one-based left boundary by

ι(w)=1+# {row positions j: row_j <lex w},

including when the cylinder is empty. Thus the proposed

ambientLeft N rows w = #((range N).filter(fun j => rows j < w))

is exactly the zero-based offset ι(w)−1. It uses the same standard lexicographic order on `List ℕ` as the existing sorted-row construction. Comparing a full row to the finite prefix is correct in that order: a word is at most each of its extensions, and rows strictly below the prefix precede all rows carrying it.

For an absolute zero-based edge index m, its relative zero-based index is m−ambientLeft. Equivalently, m=i+ambientLeft. This is precisely the proposed membership test

relativeInternalEdges N rows x s = (range(N−1)).filter(fun i => i+s∈internalEdges N rows x).

Do not use ι(w), which includes the extra one, as this offset. For example, two identical rows with ambient prefix equal to that row have absolute edge index zero and ambientLeft=0. Shifting by one would lose their only edge. A common deterministic change from zero-based to one-based relative edge labels does preserve cardinality and the corresponding sums; it is distinct from changing the sample-dependent ambient offset.

The fixed-column paper writes an inclusive right endpoint while the TeX uses a half-open interval. The count of rows strictly below the prefix, and hence the proposed left offset, agrees in both conventions. No right-endpoint formula is needed by this addendum.

## Arbitrary shifts: exact properties and limits

For every natural shift s, the map i↦i+s sends the proposed relative edge set into the absolute edge set and is injective by cancellation. Consequently

#relativeInternalEdges ≤ #internalEdges ≤ occupancyCount.

No sorting, prefix containment, legality, population positivity, or bound on s is needed for this inequality. Its reverse is false in general: all absolute edges with index below s are absent from the relative set. The chosen definition correctly discards them instead of applying truncated natural subtraction to every edge, which could merge unrelated indices below s at zero and create a false relative edge.

Let a finite sample law be W, rows depend arbitrarily on the sample, and σ:Ω→ℕ be an arbitrary sample-dependent shift. There is no requirement that σ be independent of the rows, occupancy, internal graph, or tail columns. The same pointwise injection applies separately to every outcome.

With probabilities taken under this same law and fixed support range(N−1), the generic finite sum and probability inequalities give

D_rel ≤ (E #relativeEdges)^2 ≤ (E #absoluteEdges)^2,

D_rel ≤ E #relativeEdges ≤ E occupancy.

The first comparison uses nonnegativity before squaring the expected-cardinality inequality; the second uses each probability squared being at most that probability. All nonnegativity facts follow from actual counts or existing finite-law theorems, rather than being added as premises.

For the actual matrix law, the previously proved bound on E #absoluteEdges yields

D_rel ≤ prefixMean^4 * tailCollisionFactor^2 / 4,

and the exact occupancy expectation gives D_rel≤prefixMean. These statements can retain arbitrary σ. They do not use D_abs as an upper bound for D_rel and must not be proved by an unproved comparison between those two densities.

## The two required source-preservation bridges

For the actual `sortedRows n ω`, fixed lists wList and xList, and the ordinary list-prefix relation wList<+:xList, prove:

1. Every absolute internal xList edge index m satisfies ambientLeft N (sortedRows n ω) wList≤m.
2. With that ambientLeft shift, the relative and absolute internal-edge cardinalities are equal.

These are derived facts about the constructed sorted rows, not sorting or containment assumptions supplied to make the estimate work. They need no feasibility, legality, positive population, or full-row-length premise. They also permit arbitrary list prefixes; if the target word is too long to occur, its edge set is simply empty.

For the first bridge, membership in an internal edge gives m<N and xList<+:row_m. Prefix transitivity gives wList<+:row_m, hence wList≤row_m. If a position j carries a row strictly below wList and m≤j, the existing proved sorting monotonicity gives row_m≤row_j, contradicting row_j<wList. Thus every counted j is below m. The finset of such j is contained in range m, so its cardinality is at most m. Bounds j<N and m<N needed to invoke the sorting theorem come from the existing finset memberships; no nonempty deck assumption is needed.

For the second bridge, the existing forward injection is supplemented by the inverse map m↦m−ambientLeft on the absolute edge set. The first bridge supplies exactly the condition for `(m−s)+s=m`. Since m<N−1 and m−s≤m, the inverse index lies in the relative support. Both maps preserve the requisite memberships, and cancellation proves they are inverse. This proves cardinality equality even in the empty case. A generic equality theorem with an assumed no-loss condition is unnecessary; the actual sorted-deck proof can invoke the first proved bridge locally.

For the exponent wrappers' vector inputs, the already frozen relation x(Fin.castLE hAM t)=w(t) proves `prefixWord w <+: prefixWord x` by the finite lists' lengths and their first A entries. That finite list fact can be a local proved step when applying the preservation bridges; it must not be assumed separately. The direct relative density inequalities are valid for any σ and need no containment fact, but this derived list relation is what connects their canonical ambientLeft instance to the whole source graph.

## Independent-copy relative overlap

For a given finite law W, the same random row map, the same target prefix, and the same shift function σ, the generic already proved intersection formula on common support range(N−1) gives

D_rel = E_(W.prod W) # (relativeEdges(first sample, σ(first sample))
                         ∩ relativeEdges(second sample, σ(second sample))).

Each copy uses its own shift evaluated at its own outcome. The product law supplies independence between the complete samples, including their shifts. It does not require independence of σ from its sample. It also does not represent a pair that shares the first sample's shift, a common random cut array, or a common conditioning event.

The relative intersection compares matching positions within the two separately recentered ambients. It is not the absolute intersection from the original two decks. Even when recentering preserves every edge count, it can change expected overlap: a random singleton edge at position zero or one has absolute self-overlap expectation 1/2; shifting its own edge to zero yields relative self-overlap expectation one. Thus no equality or monotonicity between D_abs and D_rel follows from cardinality preservation.

The generic overlap identity also works for arbitrary shifts that delete edges, because it applies to the resulting defined random subsets. The actual no-loss bridge explains why the canonical ambient version is a translation of the whole internal graph.

## Exponent wrappers

Instantiate the arbitrary-shift matrix bounds with

σ(ω)=ambientLeft N (sortedRows n ω) (prefixWord w).

Keep the same feasible deterministic count array, legal deterministic extension x of w, length bounds, N≥2, arbitrary real b, and exact signed ambient error as in the frozen exponent contract. The finite numerical conversion then uses the already proved μ_x=N^(L+ε_w) and tailCollisionFactor≤N^E to give the same five exponent forms for relative density:

- the unrestricted fourth-power bound N^(4(L+ε_w)+2E)/4;
- the coarse small-prefix bound N^(2E+8δ+4ε_w)/4 when L<2δ;
- the singleton-shaped bound N^(2L+2E+4δ+4ε_w)/4 with the same cutoff;
- the general mean bound N^(L+ε_w);
- its full-length terminal specialization, where the already proved E=0 identity applies.

The two small inequalities retain arbitrary real δ and all four copies of ε_w. These proofs must start from the new relative-count bounds rather than substitute relative density into an old absolute-density theorem. No source exponent, branch condition, or signed error is changed, and no new mean-power, collision-power, or spatial estimate is assumed.

This would provide a literal finite version of the source's relative small-singleton and terminal numerical estimates. It still would not prove the −c_F spatial saving, endpoint windows, stable-family classification, or a transfer from relative overlap estimates to a global absolute-coordinate first moment. Such later uses require their own proved arguments.

## Complete edge-case audit

- **N=0/1:** range(N−1) is empty, so both absolute and relative edge sets and densities vanish. Counting/injection, actual preservation, and overlap results need no N≥2 restriction. Only the inherited logarithmic exponent wrappers retain that restriction.
- **Empty ambient word:** every list is at least [], so no row is strictly below it and ambientLeft=0, even for arbitrary rows. Relative internal edges then equal absolute internal edges. The source root choice b=1 retains its already proved zero error.
- **Empty target prefix:** it selects all equal-row edges. The arbitrary-shift bounds remain true for every s. In the source-preserving ambient setting, wList<+:[] forces wList=[], so the canonical shift is zero.
- **Empty ambient cylinder:** its insertion point is still the count of rows below its prefix and can range from zero to N. If x extends w, no x row or x internal edge exists. Both edge sets are empty regardless of whether the insertion point is realized as a row position. No positive-occupancy event or conditioning is needed.
- **Full-word target or ambient:** repeated full words form a contiguous run under the existing sorting construction. If w is itself the full-length ambient and x extends it within K, the two words agree. The shift moves that run's first row to relative position zero; the no-loss proof covers zero, one, or many repetitions.
- **Overlong list prefixes in deterministic statements:** they may select no rows; all counting and no-loss conclusions still hold. Vector exponent statements keep their existing length bounds and do not allow an overlong legal prefix.
- **K=0:** all rows are empty words. With the source empty ambient, ambientLeft=0 and every deterministic path edge is retained. With arbitrary list ambient/target in the generic actual-deck bridge, an incompatible nonempty target has no internal edges.
- **Empty alphabet:** the finite matrix data and empty-row conventions stay unchanged. The generic deterministic facts do not choose a digit. Actual-law feasibility controls when a nonempty column with an empty alphabet is possible, exactly as before.
- **Large shifts:** no extra upper bound on s is needed. If s≥N−1, no relative edge survives; the injection estimate is still valid. For an actual ambient with surviving target edges, the proved lower-bound bridge supplies the necessary smaller shift automatically.
- **Shift depends on the whole outcome:** allowed in the generic density and overlap statements. No tail independence or distribution of ambientLeft is used.
- **Sample-dependent target prefix or count array:** not part of the proposed source wrappers; x, w, and n remain fixed deterministic data. Arbitrary rows and shifts do not silently authorize adaptive prefixes or a mixed matrix law.
- **Zero piles or illegal prefixes:** generic finite bounds allow empty target sets. Source exponent wrappers retain the earlier legal-prefix premise exactly; a selected positive pile of size one remains allowed and can give zero edges.
- **Sorting ties:** equal rows need no prescribed tie order for the lower-bound proof. The existing sorting permutation has a proved nondecreasing row map, which is the only order fact used.
- **Actual versus reduced population:** the shift changes positions, not the probability law, row count N, or tail denominator N(N−1). No residual-population resampling or conditional ambient law is inferred.

## Pre-freeze conclusion

The definitions and arbitrary-shift inequalities are sound as finite set and probability statements. To justify the whole source coordinate interpretation, the selected inventory should also prove the actual ambient lower-bound and cardinality-equality bridges just described. The root and statement designer have indicated that both will be included with the general actual-sorted List-prefix domain, which needs no new sorting, containment, or legality assumption.

Subject to comparison of the complete exact inventory, this route genuinely resolves the previously missing relative-coordinate representation and permits the count-based finite bounds in that representation. It does not identify two different density functions, assume spatial spread, or change any earlier frozen theorem. All additional facts used in the route must be proved within the new frozen inventory or local proof bodies before its mathematical interpretation is claimed.

## Final exact-inventory comparison and acceptance

I have compared the complete `relative_contract_statements.md`, including every definition, parameter list, and conclusion, against this independent audit and the complete `relative_contract_reconstruction.md`. **I accept exactly R.D01–R.D03 and R.01–R.18, with the selected four-module allocation, and found no remaining pre-freeze correction.** No Lean code was written for this review.

- **R.D01–R.D03:** the relative edge set uses the forward additive membership test on the unchanged finite path-edge support. The density uses the same shift function evaluated separately at each sample. The ambient cut is the strict lexicographic count within range N, with no extra one; it matches the source insertion offset and remains meaningful for empty cylinders. No probability or count alias, extra hypothesis, or alternative row order is introduced.
- **R.01–R.05:** the support, zero-shift edge equality, arbitrary-shift cardinality inequality, deck-size bound on the ambient cut, and empty-word cut all have the exact unrestricted row-map domains. The arbitrary-shift theorem correctly concludes only a cardinality inequality, and shift zero is the only general equality case selected here. No hidden sorting, positive population, bounded shift, or prefix-containment premise is needed.
- **R.06–R.07:** the actual `sortedRows` and ordinary list-prefix relation are exactly the data needed for the source-preservation proofs. R.06 proves the ambient cut is before each internal child edge using the upstream proved sort monotonicity. R.07 then proves count equality with inverse subtraction under that derived bound. These signatures add no hn, legality, common-length, assumed sorting, or assumed no-loss premise. Their general list domain includes absent and overlong target words through empty edge sets. The finite vector extension used later yields the corresponding list-prefix relation by the trusted prefix/get-element characterization; no independent vector-prefix assumption or named adapter is necessary.
- **R.08–R.11:** the generic probability statements allow arbitrary dependence of the shift on its own outcome. The expected-count and square-of-expected-count bounds follow from R.03, not from a comparison of densities. R.10 asserts density equality precisely at zero shift. R.11 has the identical law, row map, target prefix, and shift function on both product coordinates, but evaluates that function at each coordinate's own sample. Its expected intersection therefore compares matching relative positions and does not identify them with matching absolute positions.
- **R.12–R.13:** both actual-matrix inequalities retain the existing all-N feasible count model, original population, arbitrary shift function, and all zero-pile/empty-prefix cases. They correctly use the proved expected absolute-edge bound and occupancy identity, preserving the coefficient 1/4. There is no source-legality or positive-tail restriction in these finite inequalities.
- **R.14–R.18:** the actual shift is exactly the sample's `ambientLeft` for `prefixWord w`, with no public shift parameter. R.14–R.17 retain the complete X.09–X.12 vector domains, and R.18 the exact X.14 terminal domain. The four-power, two small-case, mean, and terminal conclusions have the correct signs, coefficients, and signed ambient errors. In particular both small cases retain L<2δ with arbitrary real δ and 4ε; the mean/terminal case retains ε once. Their scalar proofs start from the relative bounds, use the existing proved mean/tail identities, and never substitute a relative density into an old absolute theorem. X.13 supplies the terminal tail exponent zero without another new declaration.

The independent reconstruction's optional expected-relative-overlap bound wrappers and its optional density≤expected-absolute-count wrapper are not selected as extra public declarations; the exact R.11 identity and the selected bounds supply those compositions directly. Conversely the selected zero-shift and ambient-cut checks make the convention explicit. This is a consistent pre-freeze decomposition with exactly eighteen theorems, not a change to any earlier frozen statement.

I accept `Relative/Model.lean` for the three definitions, `Relative/Deck.lean` for R.01–R.07, `Relative/Density.lean` for R.08–R.13, and `Relative/Estimates.lean` for R.14–R.18. All other steps in the stated proof plan can remain local proved arguments. The definitions and no-loss branch justify the entire source recentered edge graph once implemented, while the independent generic counting branch proves the new bounds. Their combination still does not equate absolute and relative densities, supply an exploration-conditioned law, or establish the remaining spatial savings and global first-moment aggregation.
