# Revalidation of the current first-moment Lean input

Read-only audit. Mathematical sources remain the three authorized files. Inspected current project `.lean` interfaces, including `formalization/first_moment/FirstMoment/{Assembly,Numerical,Counting,Entropy}.lean`, the first-moment audit/import files, and relevant foundations, time-profile, finite-law/conditioning, and edge-density interfaces. No other mathematical notes were read. No Lean edits or build claims are made here; root is checking builds separately.

## Finding

The current `expectedCommonEdges_power_bound` is a useful generic aggregation theorem. It is NOT the checked formal counterpart of manuscript `prop:ub-first-moment`. Treating it as that input would add substantial unproved localization, density, and class-control hypotheses to the upper theorem. Its own module header states that the results do not assert localization or density estimates for shuffle graphs.

A clean axioms audit or successful build would establish the soundness of these conditional aggregation results; it would not discharge their mathematical premises.

## Exact exported claim

`Assembly.lean:177`, `InhomogeneousShuffle.FirstMoment.expectedCommonEdges_power_bound`, accepts:

- an arbitrary finite graph law `law`, with nonnegative weights summing to one;
- arbitrary finite index and class types `I,C`, a class map, and active index sets;
- nonnegative error values and local probability candidates;
- `hactive`: an upper bound on the number of active terms per edge;
- `hloc`: every actual edge marginal is bounded by the error plus the active local terms;
- `hD`: a squared-error sum bound;
- `hU`: every class has a bounded sum of squared local terms;
- power estimates on D, L, the number of classes, and U.

It concludes

    expectedCommonEdges <= 2*N^(-d)+2*N^(ell+c-a).

`two_power_terms_eventually` then turns the numerical right side into N^(-delta) under delta<d and delta<a-ell-c. This final asymptotic step is proved independently of any shuffle model.

Neither theorem mentions prescribed column counts, uniform valid shuffle matrices, prefix blocks, the time profile, almost-likeness, good columns, `FM`, recursive accessibility, or conditional exploration.

## Premise-to-manuscript map

The following obligations must be PROVED for the actual shuffle law, not carried into the final upper theorem as new hypotheses:

| Lean premise/data | Required actual-model construction or proof |
| --- | --- |
| `law` | Uniform finite law on valid fixed-column matrices, and its actual sorted equality-edge set; correspondence with the other project graph definitions |
| `classOf`, `I`, `active` | Retained boundary/profile classes and per-location admissible stable blocks, with an explicit finite encoding |
| `hloc` | Manuscript bad-profile reduction and per-edge stable localization |
| `hactive`, `hLpow` | Uniform bound on active stable blocks/classes at every edge location |
| `hD`, `hDpow` | Uniform probability/error estimate for discarded profiles, with correct N factor in the squared error sum |
| `hU`, `hUpow` | Actual edge-density estimates in every large/small/singleton regime, multiplied by actual class cardinality and controlled by the time-inhomogeneous numerical margins |
| `hCpow` | Injection of actual retained classes into the finite profile codes and the resulting N-small counting exponent |
| positive exponent budget | One parameter choice making all preceding errors uniformly smaller than the available source margin |

The generic `profileClass_sum_bound` has the correct arithmetic shape but itself assumes both the class-count estimate and a power bound on each summand. Thus it does not discharge `hU` without the missing model estimates.

A useful diagnostic: choose one local index for each edge and let its local value equal the actual edge marginal at that edge, zero elsewhere; set error zero and one class. Localization then becomes tautological and `hU` becomes essentially the desired first-moment estimate itself. This shows why the abstract theorem cannot create first-moment decay from finite probability alone.

## Comparison with the manuscript's actual input

`prop:ub-first-moment` (TEX line 1817) assumes only the specified model/ambient setup, chosen regular partition and hierarchy, deterministic tail almost-likeness, local good-shuffle condition, and `FM(r,b,T,eta)`. It concludes a uniform negative power of N for two independent restricted shuffle graphs, with positive exponent depending on eta,gamma,k,T.

The assembly theorem proves the concluding Cauchy–Schwarz, class summation, and power absorption steps ONCE analytical premises are supplied. It does not prove the statement with the manuscript's assumptions alone. Calling those analytical premises a 'certificate', a typeclass, a structure, or a 'completed first-moment input' would not remove them as assumptions.

## What the other inspected interfaces establish

- `formalization/foundations/.../Matrices.lean` and `Graphs.lean` provide valid fixed-count matrix structures, sorted rows, prefix rank intervals, and equality-adjacency graph/component identities. These are substantial model foundations, but not a first-moment probability bound.
- `formalization/first_moment/.../Numerical.lean` and `formalization/time_profile/.../Numerical.lean` prove scalar inequalities from explicit scalar premises. They do not derive those premises from actual time integrals or shuffle density estimates.
- The counting and entropy modules bound abstract sparse codes and genuine finite type classes, but actual retained stable/profile classes still need to be connected to those codes.
- `lean/EdgeLocalization/.../Density.lean` proves density <= expected edges/occupancy/collision pairs. Its header explicitly says it does not assert a tail-collision formula or asymptotic exponent estimate.
- `lean/Shuffle/Conditioning.lean` provides valid finite conditional-probability/tower tools, including careful treatment of null atoms. It does not identify the conditioned shuffle-matrix law or prove the required conditioned first moment.
- The inspected time-profile code defines `AlmostLike` on a fixed absolute grid, including its terminal partial cell, and `LocalGood` with an exact threshold. There is no exported full first-moment theorem connecting these predicates to the graph expectation.
- `EndpointObstruction.lean` proves that deterministic first-column endpoints remain atoms even after intersecting with a good event. Therefore a blanket endpoint small-atom estimate cannot be inserted to bridge the gap; the needed localization/density proof must respect the actual endpoint geometry.

## Upper-bound needs beyond the original first moment

Even an exact formal `prop:ub-first-moment` would still require proved transfer lemmas for use during exploration:

1. identify the conditional block law as an appropriate deterministic-cut subshuffle after conditioning on all required count information;
2. prove coordinate/count concentration on adapted good histories;
3. prove the chosen fine-partition to coarse-partition robustness lemma, good-column threshold transfer, and any time/base-population rescaling;
4. show uniform first-moment constants and exponent losses across every large accessible block;
5. separately bound tiny blocks, near-unit expected-size blocks, and repeated copies of the current exposed string;
6. obtain the uniform conditional future-edge bound needed by the killed-exploration exponential-moment proof.

None of these can be replaced by accepting an extra robustness or conditional-first-moment hypothesis. The guard-band construction previously audited is a possible route to proving robustness from the original chosen-partition assumptions, but no such model transfer is currently supplied by the aggregation theorem.

## Safe freeze decision

There is no checked-input route to a completed global freeze using these modules alone that both preserves the manuscript assumptions and treats the requested full first-moment result as previously proved.

The safe alternatives are:

- obtain the actual completed theorem declaration, with its checked proof and exact model/ambient/partition quantifiers, then map it into the upper-bound representations by proved equivalences; or
- prove the missing model-to-aggregation bridge from the unchanged source assumptions, thereby creating the genuine first-moment theorem before relying on it.

It is safe to record the desired full first-moment statement as an unresolved proof obligation in a planning document. It is not safe to give it an unproved Lean declaration, add it as an assumption of the final upper theorem, assume `hloc`/`hU`, or claim the requested input has been imported.

Independent finite reductions can have precise planned statements, but they do not resolve this global handoff. The current audit supports continued pre-freeze work and an explicit missing-input status, not completion of the exponential-moment or TV upper-bound formalization.
