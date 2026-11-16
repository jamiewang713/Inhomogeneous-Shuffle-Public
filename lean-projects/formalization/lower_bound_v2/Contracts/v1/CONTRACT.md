# LB-00 contract v1

Status: shared definitions and statement inventory; downstream mathematics pending. The immutable `SHA256.json` binds this contract, exact Lean statements, shared source definitions, build tooling, ownership and provenance. `EXPORTS.md` prints the elaborated public types and target bodies. The authoritative source is the revised manuscript with SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.

## Endpoints and historical comparison

* **E**: `RiffleLowerV2.Targets.EmpiricalCombinedTarget`. Every accuracy epsilon > 0 has an N0, uniform over all N and all horizon cut arrays after N0. Fixed k,T, both positive margins, cold parameters and accuracy precede N0. E's cold disjunct includes positive chi/gamma/rho, the kappa0 mesh budget, actual LocalGood, and empirical Lambda1 margin. E's largest disjunct includes only the empirical beta margin. LargestOnlyTarget, ColdOnlyTarget and FiniteLargestWordTV are separate required exports.
* **M**: `RiffleLowerV2.Targets.MacroscopicIntegrableTarget`. The order is k,T,eta → partition scale and regular P → rho0 → fixed rho → phi0 → fixed phi, good-column constants, accuracy and fixed mu with ScalarIntegrable for that same P → N0 → N and all cuts. The macro margin is max(macroBeta mu T, macroLambda1 mu T). N0 may depend on fixed rho/phi/chiGood/gamma/mu/accuracy. No sequence-specific Tendsto statement replaces these quantifiers.
* Both conclusions concern `physicalInverseLaw`, independently defined from chronological forward operations. Matrix/graph equalities are pending LB-01 targets, never fields or final assumptions. InversionTV is a pending theorem needed to recover the equivalent forward-law endpoint.
* **Visible regularity addition:** M strengthens the historical arbitrary totalized-TimeLaw formulation by ScalarIntegrable. Current manuscript lines 147–152 intend ordinary scalar Lebesgue integrals, but this is not present in old Lean TimeLaw. Fixed-partition AlmostLike cannot derive it: same-cell nonmeasurable switching is documented in both historical analytic alternatives and the new independent review. Integrability is required for the selected P; no refinement is substituted later. E is free of this addition. The unchanged historical statement remains uncertified.
* The old lower package proves a finite Chebyshev/run bound; it did not prove the asymptotic cold theorem. Its old cold combinatorial lemma assumes localization. No such localization assumption enters E or M.

## Definition and representation contract

The source-of-truth definitions live in Shared/Model, Empirical, Path, Statistics and Geometry. PMF normalization is inherited from checked mathlib constructions. Prefix and restricted-column word cardinalities enumerate only actual coordinates. Physical chronology, stable full-word sorting and component sorting have separate names and semantics. No law-identification field is allowed.

A/B/J/H use the fraction of each column elapsed at an endpoint, with their difference divided by log N. This is the signed finite step integral, including partial endpoint columns. `empiricalIntegral_grid` proves its exact normalized finite sum. Supremum/infimum domains are the real triangle and [3,4]; LB-05/LB-07 must prove all boundedness/nonemptiness properties needed in their arguments, rather than exploit totalization. Definitions exist also outside theorem domains; no such totalization is evidence.

`ColdWitnessData`, `RoundedTypeData`, `ColdGeometryData`, and `RowPrescription` contain data only. Separate WitnessSpec/TypeDataSpec/GeometrySpec predicates state their owners' obligations. LB09's concrete target existentially constructs all the data/specifications and the localization probability from the empirical premises. Intermediate conditional targets may consume previously proved specifications; E/M do not assume them.

The definitions of integer boundary and clipping preserve the paper's one-based integer geometry. `rank_interval_iff`, `mem_clipTranslate`, `clipTranslate_card_le`, `matrix_graph_adapter`, and the finite expectation adapters are proved shared exports. `ManyEdgesTarget` uses the exact ambient translate q*=lowerRank(prefixAt W.ms G.ambient), matching the source.

## Independence and pending obligations

All target definitions are propositions to be proved, with no proof constants, instances or axiom placeholders. A theorem of a target type must be added in the assigned lane directory under its recorded future export name. LB-01–07 depend only on this shared foundation; when elementary spatial/probability helpers overlap, each may prove private helpers or request a separately reviewed additive shared export. They may not introduce an unplanned dependency on another first-stage lane. In particular LB-07 cannot assume LB-05's pending one-column toolkit, and LB-03 proves residual factorial identities independently of LB-02's law theorem.

Source correspondence, exclusive paths, imports, future theorem names and dependency prerequisites are in OWNERSHIP.json and LEDGER.md. No original library has been ported by LB-00: canonical 4.33.1 project modules are compiled from their original source into the new output directory. Old 4.19/4.24 sources are reuse candidates only. Compatibility ports have named lane owners and must come with original/ported hashes, signature comparison and checked concrete adapters.

LB-12 must re-audit complete theorem hypotheses and the proof dependency closure after E/M exist; this foundation receipt is not final theorem certification.
