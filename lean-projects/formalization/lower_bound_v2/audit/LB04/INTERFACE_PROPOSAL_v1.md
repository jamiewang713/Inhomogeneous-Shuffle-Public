# LB04 interface proposal v1

Status: proposal only; no dependent proof started. Preserve the immutable v1 statements.

## Exact exports and assumptions

The ten exports in OWNERSHIP.json are adopted without strengthening hypotheses or weakening conclusions: `componentConcentration : Targets.ComponentConcentration`, `componentExpectation : Targets.ComponentExpectation`, `uniformScan : Targets.UniformScan`, `componentComparison : Targets.ComponentComparison`, `uniformGraphScan : Targets.UniformGraphScan`, `relativeOrderIndependence : Targets.RelativeOrderIndependence`, `boundaryAscentProbability : Targets.BoundaryAscentProbability`, `bernoulliMGF : Targets.BernoulliMGF`, `leastSuccessfulTranslate : Targets.LeastSuccessfulTranslate`, and `componentConcentrationTwoSided : Targets.ComponentConcentrationTwoSided`, all under `RiffleLowerV2.Ascent`.

No new shared definition or target is requested. Finite bounds retain exponent constant 1, clipped expectation retains exactly `e/2+r/6-d`, and the comparison is the non-strict FAILURE event with positive Delta. Relative orders include empty position sets; the boundary comparison includes empty A or B. Integer H0 remains arbitrary, and no M≤N hypothesis enters the scan. Eventual N0 is uniform over N,H0,G and chosen at least 1. Least-choice construction will be a deterministic function of G and fixed parameters, with a default on unsuccessful graphs, and has no permutation argument.

The finite parity proof will establish independence of relative orders by exact counting; it will not assert independence of component value sets. No generic block bounded-difference lemma is used. The independent-keys reconstruction is a mathematical check only. A generic mixture test, if exported, explicitly assumes its graph-law mixture identity; the actual shuffle-law discharge belongs to LB10 with LB01.

## Readiness and ownership

`python3 scripts/lane.py LB04 --check-ready` passed with `LB04 CONTRACT_INPUTS_OK`. Foundation receipt: `audit/LB00/CONTRACT_READY.md`; frozen manifest SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`. Manuscript SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`. All work stays in Ascent/ and audit/LB04/, with private lane build outputs.

Three independent pre-proof reviews are underway and will be compared in a new resolution record before dependent proofs start. Initial findings require no statement amendment.

## Additive dependency request

Please register compatible `Mathlib.Probability.Moments.SubGaussian` in the coordinator overlay, preserving pinned source/caches and all old freezes. Its proved `hasSubgaussianMGF_of_mem_Icc` has exactly the Bernoulli constant required, including every real t. Existing finite expectation/integral adapters will connect it to the shared PMF definitions. Request also `Mathlib.Probability.ProbabilityMassFunction.Integrals` if not already registered.

LB01 has just issued `audit/LB01/COMPLETED_INPUT_v1.json`. Generic deterministic helpers in `RiffleLowerV2.Model.GraphSorting` (`componentIndex_monotone`, `componentIndex_lt_of_missing`, `sort_pair_preserves_first`, `componentSort_preserves_component`, `componentSort_increasing`) and elementary finite PMF helpers in `RiffleLowerV2.Model.FiniteLaws` can prevent duplicate proofs. Since v1 disallows an unplanned first-stage dependency, please explicitly review and authorize this additive dependency on these now-completed checked helpers, or direct LB04 to source-port the needed helpers privately with provenance. No graph-law theorem will be assumed to prove the deterministic LB04 targets. No shared contract change is requested.

Please return a new LB04 interface acknowledgement and separate dependency receipt. Do not edit frozen v1 sources or start LB04 proofs.
