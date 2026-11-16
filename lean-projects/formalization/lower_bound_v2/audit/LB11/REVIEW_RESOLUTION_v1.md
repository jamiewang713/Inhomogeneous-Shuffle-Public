# LB11 pre-proof review comparison v1

Independent mathematical, Lean representation, and missing-hypothesis reviews agree on adopting the exact v1 MacroscopicIntegrableTarget with no added assumptions. The separate review reports retain their own numerical presentations and snapshot-specific readiness findings.

Adopted implementation: e=min(kappa0(eta/2)/10,eta/100)/2. The log-tail threshold transferThreshold(log k,e) yields d=log k/log N<=e/4, hence beta error<=5e/4 and lambda1 error<=10e. Since kappa0(eta/2)<=eta/200000 and e<eta/100, small empirical beta forces macroBeta<eta and empirical lambda1>=eta/2. This has the same mathematical content as the alternative reviewed tail budget 14d<=e, but uses one simpler arithmetic bound already exported by LB07.

Both direct branch application and construction of EmpiricalAlternative are valid. Use direct largestOnly/coldOnly to mirror the manuscript, with a maximum of transfer, log-tail, largest, and cold thresholds. The supplied cold parameters are constructed from the final hypothesis, and no witness/test/TV assumption is introduced. Both branch thresholds are uniform over cuts, so alternating branches require no subsequence or compactness argument.

Partition and all mesh/frequency choices precede ScalarIntegrable for that exact P and the eventual N threshold. Keep both margins unchanged. Use only the cell-mass, a and psi integrability clauses. The manuscript global scalar-integral convention is broader (also covers other displayed integrands); this theorem needs only the reviewed subset. Historical arbitrary TimeLaw and old packages remain unchanged and uncertified by this endpoint.

The only initial obstacle is coordinator registration of completed LB07/LB10 inputs. Request sent to LB00; no sibling cache copying, shared build, contract mutation or freeze regeneration is authorized for LB11. Dependent implementation waits for the coordinator acknowledgement. Final source/compiled-type/axiom review will be separate and cannot be inferred from these pre-proof approvals.
