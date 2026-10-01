# LB-03 review comparison and interface adoption v1

All three independent pre-proof reports have been read and compared: math_review_v1.md, representation_review_v1.md, and hypotheses_review_v1.md. Each finds the ten frozen targets valid and requests no shared amendment. LB00 has acknowledged the exact unchanged interface in audit/LB00/LB03_INTERFACE_ACK_v1.md. Dependent proof implementation is now authorized under that receipt.

Agreed obligations: count globally disjoint labelled requests using distinct full words; retain the canonical fixedCountPMF; prove residual admissibility and deleted-row identities on the conditioning event; allow zero unrequested piles without taking their logarithms; control the residual order R relative to ambient N; treat R=0, K=0, N=0 (exact formula) and b=0 explicitly; control the product remainder with the (m,m) factorial moment; preserve the rare coefficient 1/3.

The numerical reviews offer compatible, nonoptimal choices of constants. No sharp constant is required by the relative target. Implementation may use the more generous exp-error coefficient 3 and constants 6/min(c,1) or 12/min(c,1), or any actually proved larger explicit constants. Thresholds remain uniform and are chosen before all variable arrays/requests; no reviewed numerical estimate is assumed without proof.

The representation review confirms that all residual targets already occur in TransferFinite.lean. We will not import first-stage LB01/LB02 implementations. Elementary finite-PMF helper arguments may be implemented locally with source provenance. The historical Lean 4.19 caches will not be used. The scalar Poisson benchmark is an analytic lemma or a justified infinite-series identity; the finite central target will never be instantiated on an infinite type.

Implementation responsibilities: exact/residual combinatorial moments; numerical factorial ratios and residual means; pointwise/analytic Bonferroni lemmas; and finite expectation assembly. These are separate proof interfaces inside the owned Factorial directory. Independent implementation review will follow. No target is claimed proved by this review resolution.
