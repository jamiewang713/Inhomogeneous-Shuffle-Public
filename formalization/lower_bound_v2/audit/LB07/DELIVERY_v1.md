# LB07 delivery v1 — explicitly integrable profile transfer

**Complete for the unchanged frozen LB07 contract.** All four required exports are proved, compile together, and pass the aggregate axiom audit. No LB07 proof obligation remains pending. This is the explicitly scalar-integrable transfer theorem; it does not certify the historical unregularized TimeLaw theorem or the downstream lower-bound assembly.

## Exact exports and source correspondence

All names below have prefix `RiffleLowerV2.ProfileTransfer.`. Their types are exactly the frozen predicates, with no additional parameters or assumptions.

| Declaration | Exact type | Source correspondence |
| --- | --- | --- |
| `genericQuadrature` | `RiffleLowerV2.Targets.GenericQuadrature` | Generic finite two-sided estimate in the proof of `lem:lower-profile-transfer` |
| `jointPsiContinuity` | `RiffleLowerV2.Targets.JointPsiContinuity` | Joint continuity used to select the regular partition in that proof |
| `marginTransfer` | `RiffleLowerV2.Targets.MarginTransferTarget` | `eq:lower-margin-transfer`, including 13e/2 and explicit terminal errors |
| `profileTransfer` | `RiffleLowerV2.Targets.ProfileTransferTarget` | `eq:lower-profile-transfer` and its margin conclusion, with ordered parameters |

`EXPORTS_v1.md` records exact compiled types of the required exports and public helpers. `compiled_declarations_v1.json` records every owned elaborated declaration, its type, direct dependencies, and transitive axiom closure. The target bodies are printed in `check_v1.log` and remain frozen in `Contracts/v1/EXPORTS.md`.

## Mathematical result and assumptions

The generic theorem proves the absolute step-integral error

```text
2*T*omega + M*m*phi*T + 4*M*rho
  + (4*M*m*(T/rho+2)+6*M)/log N.
```

The owned compatibility proofs include complete grid blocks, at most two incomplete blocks, and the closed-to-half-open discrepancy. Applying the one-sided theorem to both f and M-f supplies both signs. Spatial integrability and the observable's own time-integrability justify the complementary integral identities. The sampled-column error costs an additional M/log N and endpoint interpolation costs 2M/log N. Effective oscillation min(omega,M) and the proved m≥1 bound yield the frozen budget.

The specializations discharge spatial continuity/integrability and use exactly `ScalarIntegrable μ P T`: the selected P's cell masses, maximal-pile cost, and each psi cost for alpha in [2,4] are interval-integrable on [0,T]. The selected P is chosen before this predicate and is never replaced or refined. No measurable kernel, time continuity, derivative, or macro J/H integrability is added. The generic theorem retains the frozen cell-mass premise, although the complementary route proves a stronger result that does not need that clause.

For margins, boundedness and nonemptiness are proved before every real infimum/supremum comparison. On the common horizon S the error is 13e/2. Monotone clipping proves

```text
0 ≤ macroLambda1 μ S - macroLambda1 μ T ≤ 8*log(k)*(T-S).
```

Since 0≤T-S<1/log N, this lies within the frozen terminal allowance 14*log(k)/log N. The beta terminal error is e+log(k)/log N. The zero empirical horizon is included.

## Explicit order and thresholds

`Parameters.lean` proves the following formulas and their bounds. Write M=4log k and m=P.cellCount:

```text
chi  = min(1/(2k), e/(8(T+1)))
P    = a regular partition at chi, with regularity constant 1
rho0 = min(rhoCeiling, e/(16(M+1)))
phi0 = e/(4(M*m*T+1))
C    = 4*M*m*(T/rho+2)+6*M
N0   = max(2, ceil(exp(4*C/e))).
```

The order is k,T,e,rhoCeiling → chi,P → rho0 → fixed positive rho≤rho0 → phi0 → fixed positive phi≤phi0 → μ with the same-P scalar predicate → N0 → N and all cuts. Each of the four error terms is at most e/4. The actual N0 is independent of phi and μ, stronger than the permitted dependence, and is uniform in cuts, endpoints, and alpha. The supplied positive bridge ceiling is respected.

## Proved-versus-pending dependency ledger

| Obligation or input | Status and evidence |
| --- | --- |
| LB00 shared foundation and frozen target types | Verified by unchanged `CONTRACT_READY.md` and lane readiness; 43 frozen file identities preserved |
| Canonical `RiffleTimeProfile.Analysis` | Checked additive receipt `LB06-v1`; used for bounds and regular-partition existence, without a dependency on LB06's proof lane |
| Historical lattice/envelope/one-sided quadrature | Fresh owned source ports, compiled with pinned Lean 4.33.1; provenance in `quadrature_implementation_receipt_v1.md` |
| Finite empirical primitives | Fresh independent namespace port; `empirical_provenance_v1.md`; no Witness-lane import |
| Endpoint interpolation, spatial continuity, parameter budgets | Proved and included in aggregate Main build |
| Four required LB07 exports | All proved at their exact frozen types; no pending input theorem or placeholder |
| Independent review conditions | Resolved by pre-proof comparison, final mathematical review, and final assumptions review/addendum |
| LB11 macro lower-bound assembly | Outside LB07; this receipt provides its transfer input but does not prove the assembly |
| Original arbitrary-TimeLaw transfer claim | Uncertified; fixed-partition nonmeasurable switching remains a counterexample to the removed-integrability inference |

No temporal predicate was introduced into empirical witness, type, model, or probability modules. Those modules, the manuscript, old packages, shared definitions, Lake configuration, umbrellas, and old freezes were not edited.

## Verification and reviews

From `formalization/lower_bound_v2`:

```text
python3 scripts/check_dependency_receipt.py LB06-v1
python3 scripts/lane.py LB07 --check-ready
python3 scripts/lane.py LB07 RiffleLowerV2.ProfileTransfer.Main
```

The aggregate build succeeded cleanly; see `main_build_v2.log`. `Check_v1.lean` was then run with the pinned compiler, `LEAN_PATH` set to `.build/lanes/LB07/lib/lean`, and warnings treated as errors; see `check_v1.log`. It checks all four typed theorem assignments and the transitive axiom closure of **140** owned declarations, including private helpers and generated declarations. The union is exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no proof placeholders, custom axioms, or native proof oracles. Earlier failed development or lock-contention logs are preserved and are not certification receipts.

The pre-proof mathematical, representation, and missing-hypothesis reviews are recorded separately and compared in `REVIEW_RESOLUTION_v1.md`. Post-implementation reviews are `margin_math_implementation_review_v1.md`, `final_hypotheses_implementation_review_v1.md`, and `final_hypotheses_verification_addendum_v1.md`. All substantive findings are resolved. The root additionally inspected the Spatial implementation: positive exponents cover zero simplex coordinates, positive power sums justify logarithmic continuity, bounded continuity supplies spatial integrability, and no temporal regularity enters those proofs.

## Downstream import and receipt

Import `RiffleLowerV2.ProfileTransfer.Main` for all four exports. Its direct imports are the owned Quadrature, Margin, and Parameters modules. The transitive external imports are the frozen shared/contracts modules, canonical registered Analysis/Base, and pinned mathlib. No other first-stage proof lane is imported.

Proof output remains in the assigned private lane cache `.build/lanes/LB07/lib/lean`. The coordinator may register/rebuild the entry point in its serialized integration build; no shared cache or umbrella was changed here. `FINAL_RECEIPT_v1.json` binds the delivered sources and certification artifacts; `implementation_hashes_v1.json` records all 12 proof-module hashes. The pre-review `checked_build_receipt_v1.json` is retained as an earlier snapshot; this final delivery and receipt close its review-pending status.
