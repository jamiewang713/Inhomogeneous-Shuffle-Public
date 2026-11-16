# LB10 finite largest-word component delivery v1

The finite source `prop:largest-prefix` estimate is proved in `RiffleLowerV2/EmpiricalLower/LargestFinite.lean`.

The required export is exactly:

```lean
RiffleLowerV2.EmpiricalLower.finiteLargestWordTV :
  RiffleLowerV2.Targets.FiniteLargestWordTV
```

It retains arbitrary natural k,N,K and positive N, with only `2≤m`, `m≤N`, and `m≤maximalMean/2` as additional hypotheses. The conclusion uses the physical chronological inverse law, the frozen Chernoff constant, and the exact `(N-m+1)/m!` null error. There is no witness, law identity, count-tail, scan-success, or profile-law premise.

Additional public exports are:

```lean
probability_increasingRun_le {N m : ℕ} (hm : m ≤ N) :
  probability (uniformPermutation N) (fun π => HasIncreasingRun π m) ≤
    ((N-m+1 : ℕ) : ℝ)/(m.factorial : ℝ)

fullWord_forces_increasingRun {k N K : ℕ} {cuts : Cuts k N K}
  (ω : Sample cuts) (w : Word k K) (m : ℕ) (hm : 1 ≤ m)
  (hc : m ≤ wordCount w ω) : HasIncreasingRun (stableSort ω) m
```

Both use the existing canonical `RiffleLowerV2.HasIncreasingRun` predicate. The run consists of contiguous sorted positions. The count adapter uses checked LB01 prefix-rank and stable-tie results directly. The exact null count adapts historical natural U01–U06 permutation counting; its probability wrappers use the shared PMF. The actual shuffle success follows from LB02's exponential `maximalWordTail`, and the final law is identified by the proved LB01 physical bridge. The half-L1 event inequality is the checked LB04 `Ascent.probability_sub_le_tv`.

Successful final component build:

```text
python3 audit/LB10/compile_lane.py largest-finite-dev03.log RiffleLowerV2.EmpiricalLower.LargestFinite
LB10 BUILD_OK
```

`finite_check_v1.lean` then passed with warnings as errors against the LB10 private overlay. It assigns the exported theorem to the literal frozen target and prints the three public signatures and axiom closures; see `finite_check_v1.log`. Every closure is exactly `propext`, `Classical.choice`, `Quot.sound`.

Historical and final source SHA-256 values, exact toolchain, pinned mathlib, port boundaries, and log paths are recorded in `finite_provenance_v1.json`. No historical package, shared source, frozen contract, or coordinator cache was modified. The local duplicate run definition noticed by the coordinator in a development draft was removed before the final checked source.

This report certifies the finite component only. Full uniform largest, many-edge, cold, and combined endpoints are separate components. Independent final review of this finite implementation is performed by the largest-asymptotic worker, not by its author.
