# Assigned-scope completion audit

This checklist follows the user's assigned list. It does not identify the assignment with the entire shuffle mixing theorem. The complete source architecture, including upper, lower and random-pile branches, is mapped in `PROOF_MAP.md`; compiled declaration edges are recorded separately in `DEPENDENCIES.md`.

| Assigned interface | Formalized content | Main location |
|---|---|---|
| Simplex-valued pile profiles | Closed simplex, zero coordinates, normalized natural cuts, positivity/support, maximum and bounded one-column costs | Base, Analysis |
| Time cells | Strict finite mesh, exact cell conventions, disjoint/unique membership and column classifier; exact floor and lattice endpoint errors | Base, LatticeCounts |
| Regular partitions | Finite measurable classifier and representatives; all four regularity conditions; existence with fixed C=1 for every admissible chi | Base, Analysis |
| Almost-time-profile-like cuts | Literal closed-grid definition, local good condition, explicit randomized convergence predicate; proved one-sided interval quadrature with partition/grid factors visible | Base, Source, IntegralEnvelope, GridQuadrature |
| Ambient blocks | Legal exact prefix, time/mass discrepancy, exact cylinder products, actual uniform-matrix expected-count identity and sorted-count invariance | Ambient, FixedCountModel, FixedCountMoments, ExpectedMass, RowReindex |
| Good and exceptional digits | Exact classification, counts, conservation, positive support and actual/representative cost bounds | Base, Digits, DigitEstimates |
| cL, cE, cF | Exact prefix/tail costs and splits; cF continuation/zero cases in WithBot; crossing comparison; expected-size interpretation from the concrete shuffle law | Ambient, SideMass, IntegratedBounds, ExpectedMass |
| S, Q, R, H | Frozen wordwise definitions, positivity, entropy/Gibbs estimates, exceptional error and the valid coarse-profile invariances | Digits, DigitEstimates, Crossing |
| Numerical first-moment margin | Actual profile estimates plus the infimum algebra; large, small, singleton and terminal branches; nested parameter choices yielding a uniform −eta/2 margin | Numerical, AnalyticParameters, SourceNumerical |

Three independent agents reviewed every inventory group before its separate freeze. All later stages retain the earlier frozen statements. No scientific assumption was added during implementation; no extra hypothesis stands in for the finite-uniform sample law, a quadrature estimate, an integrability fact or a numerical budget. The expected-count model internally constructs feasibility and derives its probability and factorization properties. When the box indicator proof encountered a representation mismatch, both other reviewers were asked for alternative finite abstractions before it was resolved.

All asymptotic statements used here have explicit quantifier order or finite error bounds. In particular, the final deck threshold precedes the cuts, time law, ambient data and words. Ambient convergence, when supplied as a family, is the already frozen uniformly quantified predicate; it is never inferred from the names of error parameters.

## Limits preserved in the final deliverable

The numerical interface consumes Crossings, StableAt, ParentCrossing and the exceptional allowance. Constructing boundary/stable families and proving the probabilistic graph first moment are separate layers. Hypergeometric estimates, conditional exploration, graph localization, mixing, lower-bound witness/type arguments and random-pile mixing transfer are mapped but not asserted as proved.

The unchanged arbitrary time profile need not have ordinary time integrals. The proved one-sided totalized-integral bounds suffice for the numerical margin; the false general two-sided quadrature does not follow. The omitted exceptional digit labels still prevent Q and cL from being determined by the coarse profile. The deterministic-first-column counterexample still prevents the source cF from implying its stated anti-concentration theorem. These are explicit source limitations, not missing hypotheses smuggled into Lean.

`verification.json` is the authoritative compilation/foundation record, including exact module fingerprints and unchanged contract/source checksums. This audit should be read together with that record, rather than as a replacement for it.

Final integration result: all 19 modules and the entry point rebuilt successfully; 158 public theorems passed the foundation audit with only propext, Classical.choice and Quot.sound. All three frozen contracts and all three original sources matched their manifests. Every current module matched its verified fingerprint. The generated dependency ledger covers all 258 public declarations, including all 158 audited theorems. No assigned interface remains pending.
