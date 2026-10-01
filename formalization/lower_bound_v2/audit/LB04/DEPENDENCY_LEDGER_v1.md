# LB04 final proved/pending dependency ledger v1

All ten frozen LB04 targets are proved on the shared definitions. No LB04 mathematical obligation is pending. This ledger does not claim completion of either full lower-bound endpoint.

| Source obligation | Checked export(s), namespace RiffleLowerV2.Ascent | Status |
|---|---|---|
| `lem:relative-order-independence`: exact joint uniform orders | `relativeOrder_fiber_card_mul`, `relativeOrder_expect`, `relativeOrderIndependence`, `expect_prod_of_relativeOrder` | PROVED by explicit finite block-action bijections and double counting |
| Same lemma: separation probability | `boundaryAscentProbability` | PROVED, including empty sides; exact inverse binomial |
| `lem:permutation-bd`: actual statistic and independent parity classes | `component_ascent_decomposition`, `boundarySupport_disjoint_sameParity`, `boundaryAscent_congr_relativeOrder`, `boundary_class_factorization` | PROVED on shared componentSort; no value-set independence premise |
| Same lemma: exact analytic constant | `bernoulliMGF`, `parity_mgf`, `subgaussian_tails`, `two_class_indicator_concentration`, `componentConcentration` | PROVED, zero boundaries handled separately; both weak tails exp(-t²/M) |
| Same lemma: two-sided consequence | `componentConcentrationTwoSided` | PROVED with coefficient 2; no boundary-size premise |
| `lem:component-ascent-expectation`: clipping and double charging | `partialComponents_card_le_boundary`, `badBoundaries_card_le`, `good_boundary_double_charge`, `componentExpectation` | PROVED; e/2+r/6-d, all internal clipped edges retained |
| `lem:uniform-ascent`: uniform baseline and scan | `probability_uniform_ascent`, `expect_ascentCount_uniform`, `componentSort_empty`, `uniformScan` | PROVED; arbitrary integer H0 and exactly N+1 shifts |
| Same lemma: asymptotic null test | `null_scan_envelope_tendsto_zero`, `uniform_null_scan_eventually uniformScan` | PROVED; N0 before N,H0; M≥N^a, no M≤N restriction |
| `lem:lalley-comparison`: weak failure event | `componentComparison` | PROVED; positive Delta=r/6-d-s and exact exp(-Delta²/M) |
| Same lemma: quantitative uniform alternative | `lalley_gap`, `quantitative_component_failure componentComparison`, `uniformGraphScan` | PROVED; error exp(-M^(2delta)/144); threshold independent of N,G,H |
| `lem:lalley`: deterministic measurable graph-only selection | `chosenTranslate`, `chosenTranslate_spec`, `leastSuccessfulTranslate`, `chosenTranslate_measurable` | PROVED; default zero; no permutation input |
| Same lemma: graph-mixture observable/TV test | `pathGraphMixture`, `conditionalLalleyTest`, `conditionalLalleyTendsto` | PROVED conditional on the explicitly stated physical-law/mixture identity |
| Actual shuffle representation at final specialization | LB01 representation; LB10 assembly | Not an LB04 premise or proof claim; must be discharged downstream |
| Full empirical/macroscopic lower-bound endpoints | LB10/LB11 | Outside LB04; not claimed |

## Discharged intermediate premises

The product-expectation inputs to the analytic parity wrapper are supplied by the proved joint relative-order law for the actual disjoint component-pair supports. The decomposition is the concrete shared statistic, not a model field. The boundary-probability input to the expectation assembly is supplied by boundaryAscentProbability and proved component disjointness. componentComparison supplies its concrete concentration and expectation; uniformGraphScan supplies that comparison. conditionalLalleyTest supplies the actual uniformScan and uniformGraphScan when taking both error bounds. Only its displayed law identity remains conditional, as authorized by the assignment.

## Inputs and imports

Base input: audit/LB00/CONTRACT_READY.md and unchanged mathematical interface acknowledgement audit/LB00/LB04_INTERFACE_ACK_v1.md. Additional checked imports are explicitly authorized by audit/LB00/LB04_DEPENDENCIES_READY_v1.md and Contracts/dependencies/LB04-v1/REUSE.md, supported by the completed LB01 integration. Direct sibling imports are limited to Model.GraphSorting and Model.FiniteLaws. No unfinished lane, unapproved Model module, old compiled cache or generic block bounded-difference lemma is imported.

Downstream import: `RiffleLowerV2.Ascent.Main`. Exact compiled public types are in EXPORTS_v1.md and public-exports-v1.json. The complete elaborated dependencies and axiom sets are in compiled-declarations-v1.json. The final Main build and all 269 compiled-declaration audits passed, with standard axiom union exactly Classical.choice, Quot.sound, propext.
