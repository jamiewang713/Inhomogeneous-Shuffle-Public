# LB10 largest-word asymptotic component

The exact frozen `RiffleLowerV2.EmpiricalLower.largestOnly : RiffleLowerV2.Targets.LargestOnlyTarget` is proved. Import `RiffleLowerV2.EmpiricalLower.LargestAsymptotic`.

The stronger finite-mean export is:

```lean
largestMean_uniform (b epsilon : ℝ) (hb : 0 < b) (hepsilon : 0 < epsilon) :
  ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ k K : ℕ,
    ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
    (N : ℝ)^b ≤ maximalMean cuts hN →
    1-epsilon ≤ tv (physicalInverseLaw cuts) (uniformPermutation N)
```

It fixes N0 before all alphabet sizes, column depths, cut arrays and word means. No macroscopic law, analytic regularity or local-good premise occurs. For the frozen horizon endpoint, LB02's exact beta/mean identity turns the empirical beta margin into the finite mean hypothesis.

`largestRunLength N b` is exactly `floor(N^(b/2))`. The module proves its eventual lower bound 2, upper bound N and mean admissibility. For b>1, the mean premise is impossible once N≥2, using the separately proved maximalMean≤N; the theorem does not add b≤1 as a premise.

The exact uniform null error is `largestRunError N b = (N-m+1)/m!`. The checked estimate `2^m≤2*m!` and `floor(x)≥x/2` for x≥2 bound it by `2*N*exp(-(log 2/2)*N^(b/2))`. This tends to zero by a proved stretched-exponential composition. The actual Chernoff failure is bounded uniformly by `exp(-chernoffConstant*N^b)`, which also tends to zero. `largestMean_uniform_scales` combines admissibility and the sum of these errors before the cut array is introduced.

Source correspondence: the finite source `prop:largest-prefix` supplies the already proved LargestFinite module; its uniform convergence paragraph is realized by LargestAsymptotic/Numerical and LargestAsymptotic. All dependency proofs are actual checked declarations, and every intermediate numerical premise is discharged at the endpoint.

Successful component build:

```text
python3 audit/LB10/compile_lane.py largest-asymptotic-dev06.log RiffleLowerV2.EmpiricalLower.LargestAsymptotic
LB10 BUILD_OK
```

The separate exact-target/closure audit `largest_asymptotic_check_v1.lean` passed with warnings as errors. `largest_asymptotic_axioms_v1.log` reports only `propext`, `Classical.choice`, `Quot.sound` for the endpoint and core numeric exports. The source and evidence hashes are bound in `largest_asymptotic_receipt_v1.json`. No manuscript, frozen contract, shared definition or historical package was changed. The representation reviewer is independently reviewing this final component; this author separately reviewed LargestFinite in `finite_independent_review_v1.md`.
