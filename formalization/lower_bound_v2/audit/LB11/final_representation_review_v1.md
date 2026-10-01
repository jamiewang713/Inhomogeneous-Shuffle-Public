# LB11 independent final representation and closure review v1

Date: 2026-10-01. Verdict: **PASS; no unresolved representation, dependency, quantifier, or axiom finding.**

This review read the two final proof sources, independently re-elaborated a separate dependency-closure check against the LB11 lane overlay with warnings treated as errors, and validated the completed `VERIFICATION_v2.json` evidence. It did not modify proofs, shared files, previous reports, or compiled caches. New evidence is confined to `audit/LB11/`.

## Exact endpoint and sequence wrapper

The compiled declaration is a theorem with the literal constant type:

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
  RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

The independent check tests both theorem kind and `info.type.isConstOf` against the frozen target. It also prints the expanded target and `ScalarIntegrable`; there is no extra hidden argument or conditional endpoint premise. Every file listed by the immutable `Contracts/v1/SHA256.json` was rehashed, with zero mismatches.

The second compiled theorem is `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto`. Its complete type is printed in both the final audit and the independent closure-check log. It repeats the same positive k/T/eta regime, regular partition selection, rho budget, phi selection, positive local-good constants, and `ScalarIntegrable μ P T` for the identical selected partition. It then quantifies over actual sequences

```lean
cuts : (N : ℕ) → Targets.HorizonCuts k N T
```

with eventual `AlmostLike` and `LocalGood` hypotheses, the same macro maximum-margin premise, and conclusion

```lean
Tendsto
  (fun N => tv (physicalInverseLaw (cuts N)) (uniformPermutation N))
  atTop (𝓝 1)
```

The eventual hypotheses quantify over proofs `hN : 2 ≤ N`; the proof obtains such a witness only once N exceeds the uniform threshold. Thus arbitrary initial arrays are permitted, and there is no illicit division or positivity assumption at N=0 or N=1. Proof irrelevance makes the resulting profile hypotheses independent of the chosen proof witness.

The wrapper is derived directly from `macroscopicIntegrable`, `tendsto_order`, and the checked `Ascent.tv_le_one`. Its actual compiled value dependencies include the uniform theorem. It does not assume TV convergence or reconstruct a weaker per-sequence endpoint as a substitute for the frozen uniform result.

## Hypotheses and uniformity

The added regularity remains exactly interval integrability on [0,T] of the chosen-P cell masses, `profileMaxCost`, and `profilePsi` for every alpha in [2,4]. P is selected before this premise and retained in `AlmostLike`. No time continuity, measurable probability kernel, globally positive pile bound, tilted-cost/entropy regularity, witness, graph law, concentration estimate, or desired TV conclusion is added as an endpoint hypothesis.

The implementation fixes `etaCold = eta/2`, `kappa0 (eta/2)`, and the positive transfer accuracy before obtaining P from LB07. The selected rho0 satisfies the frozen bridge inequality, and each allowed rho inherits it. Phi is selected before the profile and integrability assumption. The local-good constants, epsilon and profile all precede N0.

The endpoint takes the maximum of four thresholds—transfer, logarithmic error, largest-word and cold—before introducing N and cuts. It selects the finite branch only after these inputs. The large case applies the actual `EmpiricalLower.largestOnly`; the small case uses the actual two-sided transfer and applies `EmpiricalLower.coldOnly`. The same N0 handles every cut array in both branches, including sequences alternating without an eventual fixed branch. This is the exact promised uniform quantifier order.

The numerical helper uses the correct absolute-value directions: a lower bound on `betaFinite - lambda0` yields an upper bound on lambda0, and a lower bound on `lambdaFinite - lambda1` yields the necessary empirical lambda lower bound. With `log k / log N ≤ e/4`, errors are at most `5e/4` and `10e`; `kappa0 (eta/2) ≤ eta/200000` and `e < eta/100` suffice. The exact margins and the chronological physical inverse law remain unchanged.

## Actual dependency closure

The independent checker `representation_closure_check_v1.lean` starts at each final theorem and recursively visits the constants appearing in both its type and its value, opening opaque values with `allowOpaque := true`. It rejects any reachable axiom other than `propext`, `Classical.choice`, or `Quot.sound`, and independently compares this traversal with `Lean.collectAxioms`.

| Root | Recursively reachable declarations | Project declarations recorded | Axiom closure |
|---|---:|---:|---|
| `macroscopicIntegrable` | 50,441 | 2,013 | `propext`, `Classical.choice`, `Quot.sound` |
| `macroscopicIntegrable_tendsto` | 50,443 | 2,015 | `propext`, `Classical.choice`, `Quot.sound` |

The full reachable-name lists and project type/value dependency graphs are retained in `representation_closure_v1.json`; these counts include trusted Lean/mathlib definitions as well as project proofs and are not theorem-count completion claims. The recursive traversal and `collectAxioms` agree exactly for both roots.

The actual compiled endpoint directly depends on `ProfileTransfer.profileTransfer`, `EmpiricalLower.largestOnly`, `EmpiricalLower.coldOnly`, and `ProfileTransfer.transferThreshold_spec`. Its transitive closure contains `ProfileTransfer.marginTransfer` and the checked concrete proof chain of the empirical endpoints. These are proved theorem dependencies, not arbitrary premises bearing target predicate names. The sequence wrapper adds the uniform theorem and `Ascent.tv_le_one`.

The separate independent Lean check completed with exit code 0 and the marker `LB11_INDEPENDENT_REPRESENTATION_CLOSURE_PASSED`. The final v2 lane audit records 17 owned declarations, verifies the required theorem kind and exact target, and has only the same three trusted axioms throughout. Its JSON records were parsed independently and found exactly equal to `compiled-declarations-v2.json`.

## Readiness, builds and evidence identity

The prior pre-proof report's registration blocker is resolved by the additive coordinator receipts `LB11_DEPENDENCIES_READY_v1.md` and `LB11_INTERFACE_ACK_v1.md`. Both LB07 and LB10 completed imports are now registered in the shared overlay. Independent read-only executions of

```text
python3 scripts/check_dependency_receipt.py LB07-v1
python3 scripts/check_dependency_receipt.py LB10-v1
python3 scripts/lane.py LB11 --check-ready
```

all returned exit code 0. The final owned build recorded in `final-build-v2.log` is `python3 scripts/lane.py LB11 RiffleLowerV2.MacroscopicLower.Main`, invoked by the lane's serializing wrapper; it succeeded without warnings. The independent re-elaboration used the assigned LB11 import overlay and did not rebuild or copy sibling caches.

All two source hashes, eight input-manifest/receipt hashes, and seven verification-artifact hashes recorded in `VERIFICATION_v2.json` match the current files. The eight inputs include both newly issued coordinator receipts. The checked source identities are:

| File | SHA-256 |
|---|---|
| `RiffleLowerV2/MacroscopicLower/Main.lean` | `9983f9b9b097ef9cfc67374521a1639693cb3b1e745890ab6bd2323acf5e33c7` |
| `RiffleLowerV2/MacroscopicLower/Parameters.lean` | `ac7da881e475df4b5820a240b36739c0a50b8a496f7830636d17de7419c14def` |
| `audit/LB11/final-audit-v2.log` | `f2d1d40a9f2d214bac9491ada373647a1f4908f07201d3e1a271de543dfae426` |
| `audit/LB11/compiled-declarations-v2.json` | `1c8970f358acba74127565eb71a31d299787ad87a4ea32735a83cdc42a8953e6` |
| `audit/LB11/VERIFICATION_v2.json` | `bae16f545e2ca92f947706b368eb05d66f438a7f81551cd170864adce40adf13` |

`final_representation_evidence_v1.json` binds these files, the independent Lean checker and log, the complete closure inventory, and both coordinator receipts. It also records the fresh read-only dependency-check results and exact audit/inventory match.

## Scope of the pass

The complete proof implements the separately named scalar-integrable macroscopic endpoint and derives the sequence convergence corollary from it. It is appropriate to report those results as proved, subject to the coordinator's separate completed-lane registration. This review is not that registration and does not modify an integration ledger.

The empirical endpoint has no temporal regularity assumption; this macroscopic endpoint explicitly has same-partition scalar integrability. The original arbitrary totalized-TimeLaw statement and historical definitions remain untouched and are not certified by this proof. The manuscript's global assertion about all scalar integrals is broader than the minimal predicate actually used here. No finding remains open within this review's scope.
