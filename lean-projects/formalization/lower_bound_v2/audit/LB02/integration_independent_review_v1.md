# LB-02 independent concrete integration review v1

Reviewed 2026-10-01. Scope: concrete `Process`, `Prefixes`, `Main`, updated `PrefixCoordinates`, and their inspected `Sampling`, `ColumnSampling`, and residual-prefix adapters. No source edits were made.

**Mathematical/representation verdict:** the candidate integration supplies the required concrete substitutions and retains all seven frozen target domains and constants. Deterministic selection and conditional residual parameters are represented correctly. **Compilation verdict:** this is not a checked-complete certificate. The current `Prefixes.lean` has the local elaboration issue below; a final successful `Main` lane build and axiom audit remain mandatory.

## Current verification and actionable finding

Independent read-only Lean checks of the inspected `Process.lean` and updated `PrefixCoordinates.lean` both exited 0. `Sampling` and `ColumnSampling` had current compiled artifacts at inspection, and earlier receipts certify the fixed residual-law module and the two analytic/asymptotic targets. The current candidate `Prefixes.lean` failed at its final `simpa` in `prefixTransform`: the raw dependent-function sample space and the shared `ShuffleSample` abbreviation prevent rewriting the `intersectionWithin` count to `prefixCount` under the expectation.

The displayed goals have the same mathematical law and event, but Lean has not accepted this transport. Explicitly change the local expectation's sample type to `Sample cuts` before applying `prefixCount_intersectionWithin`, or supply the integrand equality after that definitional change. This is an API/elaboration obstacle, not a counterexample or missing hypothesis. The finding was sent to the root before this report. No full build or axiom closure for the final `Main` is claimed here.

## Seven frozen exports

All declarations below retain an exact `Targets.*` type annotation, so successful compilation checks the complete frozen quantifier order and statement. `Main` imports all of their modules transitively.

| Export in `RiffleLowerV2.Thinning` | Exact target | Module |
| --- | --- | --- |
| `hypergeometricTransform` | `Targets.HypergeometricTransform` | `Sampling` |
| `successiveThinning` | `Targets.SuccessiveThinning` | `Process` |
| `prefixTails` | `Targets.PrefixTails` | `Prefixes` |
| `allPrefixConcentration` | `Targets.AllPrefixConcentration` | `Prefixes` |
| `prefixFailureUniform` | `Targets.PrefixFailureUniform` | `UniformError` |
| `residualLaw` | `Targets.ResidualLaw` | `Residual` |
| `maximalMeanIdentity` | `Targets.MaximalMeanIdentity` | `MaximalWord` |

## Concrete law substitutions

`Sampling` proves uniform subset expectation by an equal-fibre bijection between permutations, then applies the checked all-positive subset transform for every deterministic marked set. Its public hypergeometric target uses the exact initial-segment marked/selected sets and the frozen inverse-permutation membership convention. No old finite-law distribution is silently substituted: the real finite expectation identity is explicitly proved.

`Process` instantiates the checked backward recursion on independent uniform permutations, with `q_j=m_j/M`. Initial-segment cardinalities use `m_j≤M`, and the count is identified with the frozen `thinningCount`. The two transform inequalities and `thinningTails` keep `M>0`, every `s>0`, all three exact constants, and `t>0`. Empty sequences give the initial whole population; fractions zero and one are retained.

`ColumnSampling` proves that relabeling preserves the full column assignment space and maps the selected digit set accordingly. Equal fibres then identify the actual `columnPMF` digit set with the uniform fixed-size subset law. This is the substantive concrete-column bridge, not an assumed row-independence assertion.

`Prefixes` sets inactive suffix columns to the whole label set and fraction one. It proves the actual list-prefix count equals the intersection count, applies the concrete active-column transform, and uses the deterministic neutral-column equality elsewhere. The product is exactly the shared dimensionless `prefixMass`, and multiplication by N gives `prefixMean`. Its concrete `prefixTails` supplies the previously generic premise in `allPrefixConcentration_of_prefixTails`; the proposed frozen export retains no external tail assumption. The explicit cardinality/union bound and uniform error limit remain the separately checked modules.

## Required edge cases and ordering

* The quantified prefix type is the sigma over every length, including zero. Empty-prefix count N and mass one agree with neutral suffix factors, including K=0. No full-word extension is chosen to encode a shorter prefix.
* Zero-mass prefixes are explicitly proved to have zero count in **every** valid sample. An assumed occurrence would force every active digit count, hence the product mass, to be positive. No probability-one exception or positive-pile hypothesis is introduced.
* Concrete prefix statements require N>0 and allow k=0. Feasible positive-population cuts with k=0 can only have K=0; the definitions and universal coordinate proofs accommodate that case. The simultaneous-prefix helper separately proves this feasibility split, and k=1 is included.
* `maximalWordTail` has quantifier order `∀ cuts hN, ∃ w, canonical ∧ mean_identity ∧ ∀ m, ...`. The same smallest-maximizer word is chosen before m and before any random sample. It requires only N>0. From `wordCount<m` and `m≤μ*/2`, event monotonicity gives the exact `exp(-chernoffConstant*μ*)` bound. No run, physical permutation-law, or TV conclusion is claimed.

## Conditional specialization

The inspected residual adapters split counts on the prescription event into the prescribed and complementary labelled rows. Consequently `residualPrefixCount` is the original count minus the number of prescribed prefix matches; natural subtraction is justified on that event. Off-event values do not affect conditional expectations. `residualPrefixMass` subtracts every `usedCount` and divides each active factor by the natural residual population N-b; `residualPrefixMean` multiplies by N-b.

`Main.residualPrefixTransform` passes the actual proved `prefixTransform` into the residual transport adapter. `Main.residualPrefixTails` similarly passes the actual `prefixTails`. Neither wrapper leaves a generic transform/tail theorem as a user hypothesis. Both retain `b<N`, injective prescribed row indices, positive prescription probability, deterministic prefix choice, and all exact constants. The adapters prove a deterministic complement enumeration exists and use `Nat.sub_pos_of_lt hb` to satisfy the positive residual population premise. The fixed residual-law theorem still quantifies over every permitted complement enumeration.

## Completion conditions

Resolve the noted expectation rewrite, build the actual `RiffleLowerV2.Thinning.Main` entry point through the locked lane tool, and inspect exact exported types plus full axiom closure for all seven frozen outputs and the added abstract/prefix/residual/maximal-tail outputs. Confirm the resulting checked source hashes, rather than treating this candidate review as build evidence. No mathematical objection or silent target weakening was found in this source snapshot.

## Inspected source identities

| Module under `RiffleLowerV2/Thinning` | SHA-256 |
| --- | --- |
| `Process` | `19ed3d26b23d8cafb7807fcceef48ccc3e70c5cd43579543ec8aeea4aebb111b` |
| `Prefixes` | `3186a217fc234148f3ec2993c396f0492aad18670b75120e6ce5068fbfdb4ff2` |
| `Main` | `c096cae87af4a31cb846da49971660b893ed9adf48e5899fb9d7a8ded41f6248` |
| `PrefixCoordinates` | `6eb1e70f618acb49faf4992abc2a4518a94aeb0ffadd096a974b451628b57ee4` |
| `Sampling` | `c4b28390e2322893d008f17997e94c0067d40daf72c8fb0b966aae625ae7824e` |
| `ColumnSampling` | `4a3d09f0bfecce0875db521d9bd565d0c86796b64cbe18c213bce77343e393d5` |
| `Residual/Prefix` | `e858e223a9a2d19fafadff543c57bcd009b67cb3ebe4fb81b3ebad12369f9510` |

## Resolution of the local elaboration finding

After the initial inspection, the root made the sample-type identification explicit before rewriting the integrand. An independent read-only Lean check of the corrected `Prefixes.lean` exited 0 with no diagnostics. Its SHA-256 is `3186a217fc234148f3ec2993c396f0492aad18670b75120e6ce5068fbfdb4ff2`; this hash remained unchanged throughout the check. The original inspected candidate that failed had SHA-256 `ad99f894f24141f68cbfa1d69cc57a9fb2ed8de94c1f2a63019ccae8287a6862`.

The actionable source finding is therefore resolved. This strengthens the review to independently checked source elaboration of `Process`, corrected `Prefixes`, and updated `PrefixCoordinates`; it still does not replace the required final compiled `Main` build and full declaration audit.
