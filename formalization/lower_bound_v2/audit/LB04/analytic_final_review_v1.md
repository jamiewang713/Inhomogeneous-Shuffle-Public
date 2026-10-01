# Independent final analytic implementation review v1

Reviewer: root lane owner, who did not author MGF.lean or Asymptotic.lean. Both files were read in full against the source and frozen targets. Status: PASS, no substantive finding. The helper authors' individual checks are not substituted for this source review or the lane's final complete axiom audit.

| Source | SHA-256 |
|---|---|
| RiffleLowerV2/Ascent/MGF.lean | 3fa1bbd161af04b5b6bcda57f8f1e528f5e341e002a5a7bb8c27ac1b9a52d9e1 |
| RiffleLowerV2/Ascent/Asymptotic.lean | 3eec5f1f3635bbe18e2e1074a29790f05e95ee2a6ea2938f10058ab4ecfba13a |

The Bernoulli proof installs the full measurable space locally on the finite type and discharges measurability and [0,1] bounds. It applies the approved pinned mathlib Hoeffding theorem to P.toMeasure and converts both the expectation and MGF by the checked shared expect_eq_integral. The parameter is exactly 1/4 in the sub-Gaussian convention, giving t²/8 for every real t. No positivity, nontrivial-event or extra integrability hypothesis remains in bernoulliMGF.

The one-class product MGF uses a displayed finite-factorization premise rather than silently asserting independence. Weighted Cauchy–Schwarz is a proved finite sum inequality; the parity combination evaluates the two inputs at 2u and obtains exponent u²(B0+B1)/4. Markov optimizes at 2t/B, requires B>0 explicitly and derives the lower tail from the same MGF at negative u. The zero total-cardinality branch makes both classes empty and X constant before any division. The larger denominator M weakens the bound in the correct direction. Root's concrete Concentration module discharges both factorization inputs through relative-order counting on disjoint pair supports; no analytic premise is left in that endpoint.

The asymptotic proof uses the actual named chosenTranslate, with success proved from the graph-only witness, and the exact complement of a weak failure event to enter the strict scan. Its finite threshold is M>0, M^delta≥576 and M^delta≥24D, and its error is exactly exp(-M^(2delta)/144). The eventual threshold combines real-power divergence, that exponential limit, and N≥1 before quantifying over H0 and G. Positivity of M follows from N^a≤M. No M≤N or constraint on the integer support appears.

The null estimate proves the exponent identity s²/M=M^delta at s=M^(1/2+delta/2), and uses monotonicity in M≥N^a. The factor N+1 is dominated by exp(-N^(a delta)) through an explicit checked power/exponential limit. The eventual epsilon bound supplies N0≥1 before N and H0. This is quantitative uniformity over all permitted sets, not merely a sequence-dependent convergence result.

The helper conditional arguments are visibly typed with Targets.ComponentComparison or Targets.UniformScan. Concrete Test.lean supplies the proved componentComparison and Concentration.lean supplies uniformScan, so these helpers are not counted alone as completed targets. Neither reviewed file introduces or assumes an actual physical shuffle representation.

Individual build and axiom evidence: mgf_delivery_v1.md / mgf_axioms_v1.log and asymptotic_delivery_v1.md / asymptotic_axioms_v1.log. Those are consistent with the inspected exact definitions and source constants. No change requested.
