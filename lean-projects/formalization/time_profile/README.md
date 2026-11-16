# Time-profile and digit-profile formalization

The assigned time-profile and digit-profile layer is implemented: **158 public Lean theorems compile and pass the foundation audit**, including the one-sided time-profile estimates, quantified numerical first-moment margins and exact fixed-count expected-mass identities. The full shuffle mixing theorem remains outside this assigned layer.

The package uses Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Verified proofs use only the standard foundations `propext`, `Classical.choice` and `Quot.sound`. No new axioms or admitted proofs are permitted. The three original mathematical sources and all frozen contracts retain their recorded checksums.

## Entry points and proof dependencies

- [RiffleTimeProfile.lean](RiffleTimeProfile.lean) imports the implemented layer.
- [PROOF_MAP.md](PROOF_MAP.md) maps the complete claimed upper bound, lower bound and random-pile extension, with dependencies and finite/probabilistic/analytic/measure-theoretic classification.
- [DEPENDENCIES.md](DEPENDENCIES.md) records all 258 public declarations and their dependencies extracted from compiled Lean types and proof bodies. [dependencies.json](dependencies.json) also records direct trusted-library references. Private project helpers are expanded when presenting dependencies between public declarations.
- [verification.json](verification.json), [build.log](build.log) and [axiom-audit.log](axiom-audit.log) record compilation, module fingerprints and each public theorem's foundations.
- [COMPLETION_AUDIT.md](COMPLETION_AUDIT.md) checks every assigned interface and records the precise remaining boundaries.

## Implemented layers

| Modules | Frozen items | Mathematical content |
|---|---|---|
| [Base](RiffleTimeProfile/Base.lean), [Analysis](RiffleTimeProfile/Analysis.lean) | F01–F09, E01 | Closed simplex; normalized natural counts; exact floor error; unique time-cell membership; Borel regular partitions with C=1; bounded costs and finite Gibbs inequality, including zero coordinates. |
| [Ambient](RiffleTimeProfile/Ambient.lean), [SideMass](RiffleTimeProfile/SideMass.lean) | D01–D05, B01–B04 | Legal cylinders; exact cL splitting, monotonicity and logarithmic mass identity; cE; side masses; extended cF with empty maxima; crossing lower bound. |
| [Digits](RiffleTimeProfile/Digits.lean), [DigitEstimates](RiffleTimeProfile/DigitEstimates.lean), [Crossing](RiffleTimeProfile/Crossing.lean) | D06–D13 | Good/exceptional digits; S,Q,R,H; conservation, support and nonnegativity; representative-cost error; entropy and exceptional-cost bounds; appended-digit and parent-crossing estimates. |
| [Numerical](RiffleTimeProfile/Numerical.lean), [Source](RiffleTimeProfile/Source.lean) | N01–N10 and source definitions | Large/small/singleton real inequalities; justified infimum; explicit margin absorption; terminal exclusion; FM/RFM and quantified asymptotic predicates. |
| [IntegralEnvelope](RiffleTimeProfile/IntegralEnvelope.lean), [LatticeCounts](RiffleTimeProfile/LatticeCounts.lean), [GridQuadrature](RiffleTimeProfile/GridQuadrature.lean) | C01–C04 | Spatial fibers; totalized-integral envelope; exact lattice and endpoint counts; one-sided representative and actual-cost quadrature. |
| [IntegratedBounds](RiffleTimeProfile/IntegratedBounds.lean), [AnalyticParameters](RiffleTimeProfile/AnalyticParameters.lean), [SourceNumerical](RiffleTimeProfile/SourceNumerical.lean) | C05–C07 | Actual cE, entropy, maximal-prefix and terminal bounds; explicit parameter choices; uniform source numerical margins with all budgets discharged. |

The expected-count modules [FixedCountModel](RiffleTimeProfile/FixedCountModel.lean), [FixedCountMoments](RiffleTimeProfile/FixedCountMoments.lean), [ExpectedMass](RiffleTimeProfile/ExpectedMass.lean) and [RowReindex](RiffleTimeProfile/RowReindex.lean) implement the separately frozen P01–P08 interface. The final integrated audit includes their 33 public theorems: sample-law construction, marginal and event probabilities, column factorization, expected prefix/side counts, the cL/cF interpretations, and count invariance under sample-dependent row permutations.

## Quantified numerical theorem

`exists_uniform_source_margins` chooses parameters in the source order:

`k,T,eta,epsilon → chi0 → chi → a regular partition P → rho0 → rho → phi0 → phi → N0`.

Only after N0 does it quantify the deck size, cut array, arbitrary time profile, ambient parameters, words, lengths and time classifiers. With `epsilon ≤ eta/28`, literal AlmostLike, FM and the frozen ambient/exceptional/crossing predicates imply the large, small and singleton bounds with margin `−eta/2`. The terminal branch excludes fallback for every positive threshold. No numerical-error budget remains as an additional hypothesis in this composed theorem.

For `L=log N`, `m=P.cellCount` and `J=floor(T/rho)+1`, the exact quadrature error is

`E = 2 omega T + M m phi T + 2 M rho + (omega + M + 2 M m) J/L`.

The source application uses `M=4 log k` and `omega=C chi`. Partition size and grid count remain explicit. The parameter theorem uses C=1 and exceptional allowance `1/sqrt(log(1/chi))`. It derives all six error bounds. The numerical kernel's large and small losses are at most `25 epsilon/2` and `27 epsilon/2`, so `epsilon ≤ eta/28` suffices.

Physical times remain the exact prefix length divided by log N and the floor-defined terminal length divided by log N. Birth-time and last-column errors are retained.

## Independent review and immutable contracts

Three agents independently reconstructed the mathematics, designed Lean representations and searched for hidden assumptions/counterexamples before each tranche. Their reports were compared before freezing:

| Contract | Pre-implementation reports |
|---|---|
| [FROZEN_CONTRACT.md](FROZEN_CONTRACT.md) | [Mathematics](reviews/math_reconstruction.md), [design](reviews/lean_design.md), [adversarial](reviews/adversarial_review.md) |
| [ANALYTIC_CONTRACT.md](ANALYTIC_CONTRACT.md) | [Mathematics](reviews/continuation_math.md), [design](reviews/continuation_design.md), [adversarial](reviews/continuation_adversarial.md) |
| [EXPECTATION_CONTRACT.md](EXPECTATION_CONTRACT.md) | [Mathematics](reviews/expectation_math.md), [design](reviews/expectation_design.md), [adversarial](reviews/expectation_adversarial.md), [comparison](reviews/expectation_comparison.md) |

Separate checksum manifests enforce each freeze. Later contracts add proved interfaces while leaving every earlier frozen definition, assumption and statement unchanged. Final implementation audits are in [continuation_implementation_audit.md](reviews/continuation_implementation_audit.md) and [expectation_implementation_audit.md](reviews/expectation_implementation_audit.md).

## Exact scope and source limitations

The numerical theorem is a uniform wordwise implication using `Crossings`, `StableAt` and `ParentCrossing`. It does not construct boundary families, prove profile-class truncation, or prove the probabilistic first-moment/mixing theorem. Those dependencies are located in the whole-proof map.

The arbitrary source TimeLaw has no stated time measurability. The one-sided estimates are proved for the unchanged totalized mathlib integrals, in precisely the directions needed by the numerical margin. They do not establish ordinary time-integral existence or the manuscript's false two-sided quadrature at that generality. No measurable-kernel hypothesis was added; the earlier unanswered clarification was not treated as authorization.

Two further source defects remain explicit:

- The unified coarse profile omits exceptional digit labels. It determines S,H,R but generally not Q or cL. Only the valid invariances are proved.
- The source cF includes a deterministic first-column contribution. Three equal fixed piles give a positive side-mass exponent for a continuation with deterministic left endpoint. Its downstream anti-concentration claim is false as written; no such theorem is imported.

The expected-count interface uses the uniform law on the full product of fixed-count column-assignment types. It proves column factorization and uses linearity across rows. Prefix and side expectations are unconditional global counts with the ambient restriction included. Later side digits remain free. cF is a deterministic function of expected counts, not an expectation of a random maximum. Cardinality invariance under sample-dependent row permutations supplies the sorted interpretation without a sorted-row marginal assertion.

No full upper, lower or random-pile mixing theorem is claimed. The active TeX's random upper extension and the common-test issue for a random lower extension are mapped explicitly.

## Reproduce the checks

From this directory:

```sh
python3 verify.py
python3 dependencies.py
```

The build uses the pinned compiler and existing mathlib cache read-only. Missing trusted probability modules are compiled from unchanged pinned sources into `.build`; a local symlink view supplies the remaining library files. Project proofs are rebuilt, all three contracts and original sources are checked, prohibited proof constructs are rejected, and every public theorem's foundations are audited.

Set `RIFFLE_LEAN` and `RIFFLE_PACKAGES` for another installation of the same pinned versions. The Lake configuration and `lean-toolchain` record those versions. Source-preserving hypotheses remain in statements even where Lean reports them unused.

`source_text/` contains only derived text from the two permitted PDFs. Original TeX and PDF files were not edited.
