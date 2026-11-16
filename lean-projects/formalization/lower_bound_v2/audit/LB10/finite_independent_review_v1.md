# Independent final review: LB10 finite largest word

Reviewer role: LB10 hypotheses/counterexample reviewer, not the author of LargestFinite.lean. Reviewed final source `RiffleLowerV2/EmpiricalLower/LargestFinite.lean`, SHA-256 `08c491435949bc39be23bebfcc8136a53574785b28ac03e83250d33e10a1cc7d`. The full file was read against the original source label `prop:largest-prefix`, the canonical shared definitions, and the historical U01–U06 proof. Source was not edited by this reviewer.

Verdict: the exact frozen `finiteLargestWordTV : Targets.FiniteLargestWordTV` is proved with no added hypothesis and no unresolved mathematical finding. Its dependency module compiles as part of the independent successful build `audit/LB10/largest-asymptotic-dev06.log`.

The natural counting argument establishes one and only one ordering permutation for each injection of m observed values. Extend-domain reordering gives equally sized fibers; the double sum gives count(event)*m!=N!. Conversion to the actual uniform PMF is explicit and uses positive factorial denominators. It handles m=0 and m=N as intermediate cases without dividing by m or m-1. The finite endpoint still requires 2≤m≤N exactly as frozen.

The null event is the canonical `HasIncreasingRun`. Its window equivalence covers exactly `Fin (N-m+1)` contiguous starts. The proof never replaces a run by a subsequence. The endpoint's natural subtraction is safe because m≤N. Overlap among windows is allowed by the union bound.

The shuffle-side event is proved from the actual canonical stableSort. Full-prefix rank characterization identifies an interval of length wordCount; the positive run length ensures the natural rank difference can be used. Every pair of positions in the first m locations has the same full word, and the proved stable-tie theorem makes their row labels increasing. The permutation orientation is sorted position → original label, matching the shared matrix law.

`Thinning.maximalWordTail` supplies a deterministic canonical word chosen before sampling, handles all feasible alphabets and empty column arrays, and gives the exact exponential failure. Its `<m` event is complemented to `m≤count`; no strict/weak endpoint is lost. The proof pushes this actual event through matrixLaw and discharges the physical endpoint with the proved `Model.physicalMatrixBridge`. No false same-raw-sample identity is asserted.

The final event comparison uses the checked half-L1 TV inequality. Its constants are precisely exp(-chernoffConstant*maximalMean) and (N-m+1)/m!, with no replacement of the Chernoff constant or omitted factor. The exported theorem has no moment, run-success, graph-law, local-good, witness, or TV premise beyond the frozen numerical hypotheses.

Independent small-event check from the initial review: N=4,m=3 gives contiguous-run probability 7/24≤1/3, while the increasing-subsequence event has probability 10/24>1/3. This confirms why the predicate correspondence matters; the reviewed implementation uses the correct predicate throughout.
