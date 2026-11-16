# LB09-v1 additive dependency authorization

Status: AUTHORIZED by LB00 after comparison of the three completed independent pre-proof reviews, exact v1 targets and manuscript. Only the permitted implementation dependency graph changes.

| Item | Frozen v1 baseline | Additive LB09-v1 authorization |
|---|---|---|
| LB09 prerequisites | LB00, LB02, LB05, LB06 | Same completed inputs, plus optional completed LB01 `RiffleLowerV2.Model.Sorting` |
| Purpose of optional dependency | Prove or adapt deterministic prefix-rank helpers locally | Reuse `RiffleLowerV2.Model.prefixRanks : RiffleLowerV2.Targets.PrefixRanks` and deterministic helpers in that module |
| Five Localization target types | Exact frozen v1 definitions | Unchanged; no new theorem premise |
| Mathematical model and assumptions | Actual fixed-count matrix, empirical data and frozen witness/geometry specifications | Unchanged |
| Ownership | LB09 owns Localization sources and audit/LB09 | Unchanged; no edits to Model, Shared, Contracts or shared cache |

Model.Sorting imports only the frozen Contracts.v1.AdditionalFinite root and its shared/foundation dependencies. It has no Localization import and no law-identification assumption. The additional edge is acyclic and consumes a completed input already independently rebuilt and audited by LB00 under LB01-v1. This addendum does not authorize other Model proof modules or an unfinished-lane dependency.

LB02 Thinning.Main and LB05 Witness.Main have now been independently rebuilt and audited in the coordinator overlay; LB06 Types.Main remains valid under LB06-completed-v1. A combined read-only import check verified their twelve exact frozen proof exports plus Model.prefixRanks and printed standard-only axiom closures. Its source and log are audit/LB00/LB09DependencyCheck_v1.lean and LB09_dependency_check_v1.log. No LB09 proof was compiled in that check.

The original ownership table, contract, source freezes, tooling and umbrellas remain unchanged. Direct use of the approved imports avoids any copy of historical cache files. All concrete geometric, endpoint, event, rank and edge-injection obligations remain LB09 work.
