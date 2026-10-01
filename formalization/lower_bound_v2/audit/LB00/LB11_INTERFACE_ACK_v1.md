# LB00 acknowledgement of LB11 unchanged interface v1

INTERFACE_ACKNOWLEDGED. All three independent pre-proof reviews have been read and compared; both completed upstream lanes are registered. Recorded 2026-10-01T18:30:44.098629+00:00.

Released exact existing export:

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
  RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

The target remains the definition in `Contracts/v1/Endpoints.lean`. LB00 compared the proposal and review resolution with the compiled expanded target, the actual LB07 and LB10 exports, and manuscript `thm:buffered-reduced-lower-bound`, `lem:lower-profile-transfer` and `prop:cold-lower`. No mathematical assumption, shared definition or conclusion is amended.

The adopted proof uses etaCold=eta/2, d=kappa0(eta/2), and e=min(d/10,eta/100)/2. For k>=2 the ceiling d/(200 log k) is positive and supplies exactly the required bridge budget. The checked helper transferThreshold(log k,e) bounds the logarithmic remainder by e/4. Thus the two margin errors are at most 5e/4 and 10e. The three reviews use alternative valid remainder budgets; the comparison selects this one consistently.

Choose the transfer partition P before requiring ScalarIntegrable for that same P; retain it in AlmostLike throughout. Fix rho, phi, chiGood, gamma, epsilon and the profile before selecting N0. Take a maximum of the transfer, logarithmic-remainder, largest and cold thresholds before N and cuts. At each cut array, beta>=d invokes largestOnly. Otherwise beta<d and the two-sided transfer imply macroBeta<eta; the maximum hypothesis forces macroLambda1>=eta, and the lambda error gives the empirical margin eta/2. Invoke coldOnly with its actually constructed ColdParameters. Both branches share the same threshold, including arbitrary alternation. These are proof obligations to discharge, not new premises.

The scalar predicate is exactly interval integrability on [0,T] of the selected-P cell masses, profileMaxCost and profilePsi for alpha in [2,4]. It adds no time continuity, measurable-kernel condition or macro J/H integrability. This remains an explicit strengthening of the historical unrestricted TimeLaw setting. The nonmeasurable-switching examples explain failure of the weakened transfer route; they alone are not asserted to disprove every possible historical lower endpoint. The historical arbitrary-TimeLaw endpoint remains uncertified.

Dependency readiness is `audit/LB00/LB11_DEPENDENCIES_READY_v1.md`, SHA-256 `8a3375c90768c020809885c6a7f39468e1e4c191c4fb8a729c9943a449518969`. Its combined check verifies nine actual upstream theorems and the helper type in the shared overlay. The historical review observations about missing registration are superseded by this additive receipt.

Dependent LB11 proof work may now begin in `RiffleLowerV2/MacroscopicLower/`, with its audit in `audit/LB11/` and the assigned lane build command. Final source review, exact compiled theorem/expanded-target check and full axiom audit remain required before M certification. An optional convergence corollary must follow from the uniform theorem and cannot replace it.

Frozen v1 manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`. Manuscript SHA-256: `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.

| Reviewed input | SHA-256 |
|---|---|
| `audit/LB11/INTERFACE_ADOPTION_v1.md` | `a02246b6f6a6e9ba7e5218b233d52b05d28eee5ad0010ea11be0ff5ae01b0b43` |
| `audit/LB11/REVIEW_RESOLUTION_v1.md` | `af246b60ad6ba203e35ed9ac0372c8fc69e69fd19507db6a963a202de342f442` |
| `audit/LB11/math_review_v1.md` | `96ee14c553afb593760f78ddf48e5f1920ffc47571a120d736d8815fed485463` |
| `audit/LB11/representation_review_v1.md` | `27c58b0332e0f3d2380a9d399495db5475040cf5f1846b556c90bebd4b7a66f4` |
| `audit/LB11/hypotheses_review_v1.md` | `24f75965f36489763d288c0a24e5f1de5b6d0192ec5e6a8752a6a86e7cd8020c` |
| `audit/LB11/input_validation_v1.json` | `c153de06864e1c759bd287e35a3873749d4077c5029fcf1fe5b7f7c5ab20dfa4` |
