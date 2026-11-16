# LB07 independent mathematical implementation review v1: margins and extrema

Verdict: approved. The completed Margin and Extrema implementations preserve the frozen v1 target and implement valid two-sided transfer with no missing mathematical hypothesis. This review is independent of their author. No proof file was edited.

Reviewed source snapshot:

- `RiffleLowerV2/ProfileTransfer/Margin.lean`: SHA-256 `0cd1f3b94947da08fcd316a1b7b1df3e5e3356f6c05843ee4d6aa6bd6db4c964`
- `RiffleLowerV2/ProfileTransfer/Extrema.lean`: SHA-256 `9834ecf915048be8d83af99c01e47fdd109eea1f5441b3fc5e5aa9c1cbeebb79`

## Extrema

`alphaDomain_nonempty` provides the actual frozen domain [3,4]. `alphaInf_bounds` constructs a lower bound for the image, uses nonemptiness for `le_csInf`, and supplies boundedness for `csInf_le`. Its upper bound uses the concrete alpha=3 witness, so no attainment theorem is smuggled in.

`alphaInf_le_add` correctly needs an a priori lower bound only for f's image: from the pointwise inequality it constructs the claimed lower bound for every element of g's image before applying `le_csInf` on the nonempty domain. Lack of an explicit boundedness premise for g in this helper is therefore not a gap.

`variational_le_of_lift` constructs the required BddAbove bound for the target supremum from `alphaInf_bounds`. It applies `csSup_le` only to the nonempty source image. The target set E has no separate nonempty premise, but each source point is lifted to an actual target point, and the source is nonempty. At every `le_csSup` call the target membership witness is explicitly supplied. There is no appeal to totalized empty infima/suprema, compactness, extremizer selection, or time continuity.

## Scalar and finite bounds

`scalar_restrict` restricts interval integrability from [0,T] only to ordered subintervals in [0,T]. `scalar_bounds` applies integral monotonicity with that restriction and an integrable constant. `scalar_mono` has the correct nested interval orientation c<=a<=b<=d and uses the full containing interval's integrability. Nonnegative scalar costs suffice throughout.

`macroF_bound` and `empiricalF_bound` provide a single finite real bound 4+20*log(k)*T, uniform in the triangle point and alpha in [3,4]. It is deliberately coarse and exceeds the algebraic sum of the max-cost and coarse psi bounds. All empirical intervals lie within the finite horizon; all macro intervals lie inside [0,T]. The case S=0 is retained, and triangle nonemptiness follows from the explicit (0,0) witness.

## Common-domain constant

`common_F_error` uses the actual A/B error input on (0,s), (s,u), and (u,S). On alpha in [3,4], the beta coefficient is nonnegative and at most7/2. Multiplying the A error requires e>=0, which is present. Summing the three losses yields exactly (7/2+1+2)e=13e/2. `common_lambda_error` applies the lifting helper twice, with the identity map on triangle S, to preserve both signs. No extra temporal regularity or alpha differentiability is assumed.

## Horizon clipping

`scalar_clip_le` handles both necessary cases explicitly. If a<=S, clipping the upper endpoint removes a terminal subinterval; if a>S, both clipped endpoints equal S and the clipped integral is zero. Therefore the implementation never makes the incorrect literal claim that the singleton [S,S] is contained in [a,b] when a>S.

`macroF_clip_le` applies this fact separately to A(0,s), B_alpha(s,u), and B_2(u,T), simplifying min(0,S)=0 and min(T,S)=S. Since all terms enter F as nonpositive costs and the A coefficient is nonnegative, the inequality points from macroF at T to macroF at S. The clipped pair lies in triangle S, uniformly in alpha.

`macroF_horizon_eq` uses interval-integral additivity with both integrability proofs to show that on triangle S, shortening only the terminal horizon adds the constant 2*integratedPsi(μ,2,S,T). The clipping lift and inclusion lift thus establish

    0 <= macroLambda1(μ,S)-macroLambda1(μ,T)
      <= 8*log(k)*(T-S).

The coarse historical psi_2<=4*log(k) is sufficient. This is a proved stronger terminal estimate than the frozen allowance; it does not modify the target.

## Final frozen target

`marginTransfer` has exactly type `Targets.MarginTransferTarget`. It takes ScalarIntegrable for the supplied P, the exact frozen interval-error predicate, and e>=0. The floor-horizon estimate supplies 0<=S<=T and T-S<=1/log N, with log N>0 from N>=2. Max-cost integration gives the beta loss e+log(k)/log N. The common-domain error and terminal estimate give lambda loss 13e/2+8*log(k)/log N, then monotonicity enlarges 8 to the frozen14 using log(k)>=0.

No measurable kernel, time continuity, derivative, macro J/H integrability, alternative partition, or assumption equivalent to the conclusion is introduced. The proof is specific to the explicitly scalar-integrable margin-transfer target and does not certify the old unregularized TimeLaw statement.

The author's clean `margin-build-v3.log` and `margin-axioms-v1.log` were inspected. The reported axiom closure is the standard trio `propext`, `Classical.choice`, `Quot.sound`. This review checks mathematical implementation and target preservation; the coordinator retains responsibility for the final combined lane receipt.
