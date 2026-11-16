# LB09 independent finite geometry and concentration review v1

Date: 2026-10-01. Reviewer: the LB09 mathematical reviewer and Geometry implementation worker, independent of the five modules reviewed here. Scope: Intervals, ProbabilityIntervals, ColdSet, Edges, and Concentration. All five were read in full against the frozen shared definitions and manuscript. No reviewed source was modified.

## Verdict

Approved mathematically and for statement fidelity. No substantive finding, missing premise, unaccounted combinatorial factor, rank shift, or constant error was found. These modules provide sound finite helpers; this review does not by itself certify the final localization event or assembled LB09 target, which remain separate obligations.

## Exact findings by module

### Intervals.lean

- Lines 9–35 characterize the literal integer half-open set by `Ico (ceil l) (ceil r)`. The count error at most one is valid for real l≤r, including equal endpoints and empty lattice intervals; it improves the manuscript's safe error of two.
- Lines 37–108 prove interval disjointness and boundary subadditivity. The boundary estimate uses at most two edges per selected interval. It does not equate selected intervals with connected components, so adjacent selected intervals merging causes no issue.
- Lines 110–169 handle integer translation and clipping. `rankSet_clipTranslate` uses `[1,N+1)` in integer manuscript ranks, exactly matching `manuscriptRank i=i.val+1`. Clipping adds at most two infinite-path boundary edges, including N=0 and truncation at either end.
- Lines 171 onward sum cardinality bounds only after a genuine pairwise-disjointness premise. The summed error is exactly the family cardinality, with no hidden independence or spacing requirement.

### ProbabilityIntervals.lean

- Lines 10–44 separate nonnegative masses from normalized masses. Normalization and population upper bounds require `0<N`; no division by a zero population is used.
- Lines 50–97 prove both the right-endpoint upper bound and ordered interval separation from explicit nonnegative sums. Injectivity of `wordOnList` justifies strict comparability for distinct words. Zero-mass intervals are allowed and harmless.
- Lines 98–113 place the actual integer union in `[0,N)`, supplying `M≤N` exactly. This is the relative-set convention; clipping to one-based ranks is treated separately in Intervals.
- Lines 115 onward combine mean-scaled mass bounds with disjoint cardinality sums. The input lower mass estimate can be weak because the requested integer bound is also weak. Empty families and arbitrary nonnegative scale mu remain valid.

### ColdSet.lean

- Lines 10–28 state exactly the frozen finite cardinality and boundary block, using only the actual selected class, ambient mean identity, three exponent buffers, and the explicit threshold `12/kap≤logScale N`.
- The proof derives `b≥4kap` from the selected nonnegative bin exponent, and hence `ell≥4kap`. The log threshold gives `N^ell≥exp 2`, more than the required minimum interval length.
- With `C=|P|`, `Q=N^ell`, `M=|Hrel|`, the proof correctly uses `C(exp(-1)Q-1)≤M≤C(Q+1)`. The bound `2exp(-2)≤exp(-1)` follows from `exp 1≥2`; combined with `exp(-2)Q≥1`, this establishes `exp(-2)N^h≤M`. The upper constant 2 is also valid.
- `h≥kap/2` and the same threshold imply `N^(kap/3)≤exp(-2)N^h`. The upper bound M≤N uses the actual probability union rather than exponent heuristics.
- The entropy buffer `hp≤ell-kap` proves `C²≤exp(-2)N^h≤M`. Thus C≤sqrt M. Since M≥1, the actual boundary estimate `2C+2` is at most `4sqrt M`, exactly the frozen constant for every q.
- No assumption of separate connected components, a lower bound on every clipped translate's size, or positive mass outside the selected class enters the proof.

### Edges.lean

- Lines 7–28 derive exact zero-based full-word rank intervals using the explicitly authorized checked `Model.prefixRanks` theorem. The right endpoint is exclusive in zero-based position indices, as required.
- Lines 31–65 construct the edge whose zero-based left index is `lowerRank(fullPrefix w)`. A count of at least two and the population bound prove this index belongs to `Fin(N-1)`, including the degenerate N<2 cases by impossibility.
- The chosen edge's two endpoint words both equal w. Equality of chosen edges therefore forces equality of words, yielding actual injectivity.
- Lines 67 onward prove the finite cardinality comparison for the shared `shuffleEdges ∩ internalEdges H` representation. The supplied localization premise is used at both endpoints. This helper is suitable for final assembly only after that premise has been established for the actual cold family; the implementation does not claim otherwise.
- No physical shuffle-law or graph-mixture theorem is imported. The import is the optional deterministic Model.Sorting module authorized by LB00.

### Concentration.lean

- `endpointError` (line 9) is precisely the finite relative-endpoint error with A=N^(kap/4), muA=N^b.
- The threshold helper (line 12) uses log N/N^a→0 and 1/N^a→0. All fixed constants precede N0, and no cut/witness dependence enters.
- `endpointError_le` (line 29) derives the concrete endpoint bound from `K≤T log N`, `b≥4kap`, and `4kT log N+4≤N^(kap/4)`. Its elementary sqrt d≤d+1 estimate is conservative and sufficient; all multipliers are checked nonnegative.
- `reserve_deviation_le_half` (line 62) uses the actual mean lower bound and `16≤N^(5kap/2)` to obtain `16A²≤mu`. It correctly proves A(sqrt mu+1)≤mu/2, including the +1 term, using mu≥1. This numerical condition is equivalent to the earlier review's `4≤N^(5kap/4)`.
- `half_reserve_mean_dominates` (line 91) combines `4≤N^(kap/2)` with the endpoint estimate and the same mean bound to yield the explicit two-unit slack e+2≤mu/2. The extra growth threshold ensures the endpoint scale is at least two.
- `reserve_count_dominates` (line 110) applies the same `allPrefixEvent(kap/4)` to the reserve prefix, obtaining e+2≤count. There is no auxiliary stochastic event, reserve independence premise, or tail-dependent choice.
- `exists_localization_thresholds` (line 122) combines three uniform thresholds correctly. The probability union bound itself belongs to the checked LB02 input and must still be applied in final Event/assembly; no probability conclusion is falsely asserted by this scalar module.

## Remaining assembly checks

The final event proof must identify its endpoint errors with `endpointError`, obtain `b≥4kap` and the reserve means from the actual GeometrySpec, and prove rank membership simultaneously for every tail. The finite endpoint identities must retain the ambient fluctuation on the right. The actual prefix probability bound and its uniform decay must then be used to remove the event premise. These are boundaries of the reviewed helper modules, not defects in them.

## Reviewed source hashes

All paths below are relative to `RiffleLowerV2/Localization/`.

| Source | SHA-256 |
|---|---|
| Intervals.lean | e87d8757d4d1c53c7c58614aff0e105e366c6c8797de141e8ae39d56f99a1367 |
| ProbabilityIntervals.lean | 9ad1f16e3cc2634264e1cbb4234f0814cca85e5fda860ea35fbc9c34f8177249 |
| ColdSet.lean | 930abe1e6d85a10e7d8ed34a9bc6121e88339d9a00accd1f47c73421a04a9922 |
| Edges.lean | a09fd0311c6dd3562ebbfcbfd2174d44ad50ca4872ba63845560a1029c91420a |
| Concentration.lean | 4dcb81b3c4e36f9381840e1a28678c4c064e051c4451862e036b9549cb772685 |

The parent reported successful lane builds for all five modules. This independent review checked mathematical and statement fidelity from their source, not a separate fresh axiom-inventory run; the lane's final compiled audit should cover all elaborated declarations and standard axiom closure.
