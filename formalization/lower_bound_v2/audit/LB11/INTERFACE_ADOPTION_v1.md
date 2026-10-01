# LB11 exact frozen interface adoption proposal v1

Adopt without modification `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable : RiffleLowerV2.Targets.MacroscopicIntegrableTarget`, from `Contracts/v1/Endpoints.lean`. No additive mathematical contract is requested. LB00 alone may register dependencies; this proposal neither changes nor refreezes any shared file.

Inputs: `ProfileTransfer.profileTransfer : Targets.ProfileTransferTarget`, `EmpiricalLower.largestOnly : Targets.LargestOnlyTarget`, and `EmpiricalLower.coldOnly : Targets.ColdOnlyTarget`. The complete LB07 and LB10 receipts and compiled theorem types must be revalidated in the coordinator overlay before proof implementation. Three independent pre-proof reviews are running.

Choose eta_f=eta/2, kappa=eta_f/1000, kappa0=min(kappa/100,1/1000), and e=min(kappa0/10,eta/100)/2. Apply LB07 with the positive rho ceiling (kappa0/100)/(2 log k). Its selected regular partition P remains unchanged throughout; only after selecting it require ScalarIntegrable mu P T. Select rho, phi, positive chiGood/gamma, epsilon and mu before the final N0.

Use the existing explicit transferThreshold (log k) e to bound log k/log N by e/4. The two margin errors are then at most 5e/4 and 10e. If empirical beta is at least kappa0, use largestOnly; otherwise the two-sided beta bound implies macroBeta<eta, so the maximum assumption implies macroLambda1>=eta and the lambda error gives empirical lambda1>=eta/2. Apply coldOnly. Take the maximum of all four fixed thresholds before N and cuts.

Additional final assumption, visible in the frozen type: interval integrability on [0,T] of each selected-P cell mass, profileMaxCost, and profilePsi at every alpha in [2,4]. This is neither a measurable-kernel assumption nor time continuity, and includes no macro J/H integrability. It is an explicit strengthening of arbitrary totalized TimeLaw. The empirical endpoint has no temporal regularity assumption. The manuscript and historical definitions remain unchanged.

A convenience Tendsto corollary may be derived from the proved uniform theorem and TV<=1; it will not replace the frozen uniform endpoint or introduce a premise asserting convergence. All additional helpers stay in the owned MacroscopicLower namespace.
