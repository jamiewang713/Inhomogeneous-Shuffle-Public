# LB11 final independent hypotheses and counterexample review, v1

Date: 2026-10-01. Reviewer: `lb11_hypotheses_review`.

## Verdict and scope

**Accept.** The implemented `macroscopicIntegrable` proves exactly the frozen `MacroscopicIntegrableTarget`, with no added assumptions, weakened conclusion, hidden upstream endpoint premise, or unresolved mathematical condition. The Tendsto corollary is correctly derived from this uniform theorem. The completed code preserves the required same-partition scalar integrability, all-cut uniformity, and arbitrary alternation between the two empirical branches.

I independently read all of `RiffleLowerV2/MacroscopicLower/Main.lean` and `Parameters.lean`, compared the theorem and helpers against the frozen contract, revisited the manuscript statements/proof and historical scalar-integrability counterexample, and inspected the elaborated declarations, expanded target/predicate printout, proof dependency lists, and full axiom audit. I also inspected the verification scripts. This review used the existing completed Lean build and audit logs; it did not run a redundant new LB11 compilation.

The pre-implementation dependency-registration finding is resolved. Independent read-only runs of

```text
python3 -B scripts/check_dependency_receipt.py LB07-v1
python3 -B scripts/check_dependency_receipt.py LB10-v1
```

both returned `DEPENDENCIES_OK`. The same checks with `--sources-only` also passed. These validate the registered source identities, frozen inputs, compiler/dependency revisions, and registered output fingerprints. All 15 hashes in the completed `audit/LB11/VERIFICATION_v1.json` matched their current files when independently recomputed.

## Exact implemented theorem and assumptions

The compiled inventory classifies

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
  RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

as a theorem. `Check_v1.lean` checks that its type is literally the named frozen target constant, not an implication to it or an alternate proposition. The successful audit prints `LB11_REQUIRED_THEOREMS_VERIFIED` and the following target body, reproduced here with the source's namespace abbreviations and fully named proof adapters:

```lean
∀ (k : ℕ), 2 ≤ k → ∀ (T eta : ℝ), 0 < T → 0 < eta →
∃ (chiPartition : ℝ), 0 < chiPartition ∧ chiPartition < 1 / (k : ℝ) ∧
∃ (P : BorelPartition k), P.IsRegular chiPartition 1 ∧
∃ (rho0 : ℝ), 0 < rho0 ∧
    2 * rho0 * Real.log (k : ℝ) ≤ kappa0 (eta / 2) / 100 ∧
  ∀ (rho : ℝ), 0 < rho → rho ≤ rho0 →
  ∃ (phi0 : ℝ), 0 < phi0 ∧
    ∀ (phi : ℝ), 0 < phi → phi ≤ phi0 →
    ∀ (chiGood gamma : ℝ), 0 < chiGood → 0 < gamma →
    ∀ (epsilon : ℝ), 0 < epsilon →
    ∀ (μ : TimeLaw k), ScalarIntegrable μ P T →
    ∃ (N0 : ℕ), 2 ≤ N0 ∧
      ∀ (N : ℕ) (hN : 2 ≤ N), N0 ≤ N →
      ∀ (cuts : HorizonCuts k N T),
        AlmostLike cuts (deckPos hN) μ P T rho phi →
        LocalGood cuts (deckPos hN) chiGood gamma rho 0 T →
        eta ≤ max (macroBeta μ T) (macroLambda1 μ T) →
        1 - epsilon ≤ tv (physicalInverseLaw cuts) (uniformPermutation N)
```

Here `HorizonCuts k N T` is exactly `Cuts k N (horizonDepth N T)`, with `horizonDepth N T = floor₊ (T * log N)`. `deckPos hN` supplies `0 < N` from `2 ≤ N`; it is not a mathematical hypothesis about the cuts.

The only new temporal-regularity predicate relative to arbitrary historical `TimeLaw` unfolds as:

```lean
(∀ i, IntervalIntegrable (cellMass μ P i) volume 0 T) ∧
IntervalIntegrable (profileMaxCost μ) volume 0 T ∧
∀ α ∈ Set.Icc (2 : ℝ) 4,
  IntervalIntegrable (fun t => profilePsi μ t α) volume 0 T
```

Every assumption has therefore been exposed: `k ≥ 2`, positive `T,eta`, the selected regular partition and mesh/frequency bounds, fixed positive `chiGood,gamma`, positive requested accuracy, same-partition scalar integrability, the finite `AlmostLike` and `LocalGood` properties, and the original positive maximum-margin inequality. There is no test-event, graph-representation, witness, probability, total-variation, transfer-target, or empirical-endpoint hypothesis in this theorem type. The auxiliary `ProfileIntervalErrors`, `ProfileMarginErrors`, and `ColdParameters` appearing in proof dependencies are locally proved data or conclusions of checked theorems, not additional caller premises.

## Concrete discharge of dependencies

At `Main.lean:17`, the proof directly invokes `ProfileTransfer.profileTransfer`. It obtains `P` and its regularity together with the transfer hierarchy. At line 25 it first introduces `μ` and `hμ : ScalarIntegrable μ P T`; line 26 passes that exact `hμ` to the transfer hierarchy for the previously selected `P`. The later `AlmostLike` hypothesis has this same `P`. No second partition, refinement, or hidden regularity transport appears.

At lines 29–33 the proof directly invokes the checked `EmpiricalLower.largestOnly` and `EmpiricalLower.coldOnly`. `ColdParameters` is constructed at lines 27–28 from the theorem's fixed positive parameters and the checked bridge inequality. The small empirical margin and required cold margin are proved before `coldOnly` is applied. No concrete shuffle-model input remains abstract in LB11's exported type: both branch results already concern `physicalInverseLaw cuts` versus `uniformPermutation N`.

The compiled main theorem's value dependencies include the three actual theorem names `ProfileTransfer.profileTransfer`, `EmpiricalLower.largestOnly`, and `EmpiricalLower.coldOnly`. Its type dependency is exactly `Targets.MacroscopicIntegrableTarget`. Thus the code supplies the dependencies rather than assuming a predicate that merely names the desired result.

## Constants, max-margin branch, and endpoint uniformity

`Parameters.lean` uses the original `kappa` and `kappa0` definitions from `Shared.Empirical`; it does not redefine the margins or change their normalization. It chooses

`e = min (kappa0 (eta/2)/10) (eta/100) / 2`

and proves its positivity and both strict upper bounds. The bridge ceiling is `(kappa0 (eta/2)/100)/(2 log k)`. Its positivity is justified using `k ≥ 2`, and the selected `rho0` and every `rho ≤ rho0` satisfy the exact frozen `2 rho log k ≤ kappa0 (eta/2)/100` budget.

The proof's `Nd = transferThreshold (log k) e` gives the stronger terminal bound `d_N = log k/log N ≤ e/4`, improving on the sufficient `d_N ≤ e` reviewed initially. The frozen beta and lambda errors consequently become at most `5e/4` and `10e`. Under `β_N < κ₀`, the arithmetic helper uses the correct side of each absolute-value bound to obtain

`Λ₀ ≤ β_N + 5e/4 < κ₀ + 5e/4 < eta`.

It then uses the maximum hypothesis to infer `eta ≤ Λ₁`, and obtains `λ₁,N ≥ eta - 10e > eta/2`. The implementation returns the required weak cold-margin bound. The supporting inequality `κ₀ ≤ eta/200000` is proved from the literal frozen minimum. No branch is chosen using a substituted homogeneous cutoff or a presumed cold margin.

The split at `Main.lean:41` includes equality `β_N = κ₀` in the largest branch and puts its strict complement into the cold branch. Its location and constant are correct. The source's positive margin and zero-margin exclusion are preserved.

All four thresholds `Nt`, `Nd`, `Nl`, and `Nc` are selected before `N` and `cuts`; line 35 takes their maximum. The final threshold can depend on the profile and every fixed parameter preceding it, exactly as permitted by the frozen statement. It cannot depend on a particular cut array or on which branch holds at a later `N`. The same `epsilon` is passed separately to each empirical endpoint because only one endpoint is used for any given cut array; no error sum requiring an `epsilon/2` split is missing. Hence the theorem proves the full all-cut bound and includes arbitrarily alternating branches without an eventual-branch assumption.

## Tendsto wrapper

The wrapper retains the same parameter-selection hierarchy and same `ScalarIntegrable μ P T`. Its sequence argument is a dependent family `cuts : ∀ N, HorizonCuts k N T`. It assumes that eventually, for each proof of `2 ≤ N`, this array is both `AlmostLike` and `LocalGood` for the fixed selected parameters. This permits arbitrary initial arrays; `N = 0,1` do not cause a problem because the proof intersects admissibility with the eventual set `N ≥ N0 ≥ 2`.

The wrapper obtains its partition, mesh, and uniform lower bound directly from `macroscopicIntegrable` at lines 73–86. For each `a < 1`, it chooses `epsilon = (1-a)/2`, then uses that uniform bound and eventual admissibility to prove eventually `a < tv`. For each `b > 1`, the checked general bound `Ascent.tv_le_one` gives `tv < b` for every `N`. `tendsto_order` therefore yields the displayed convergence to one.

The compiled wrapper's value dependencies explicitly include `MacroscopicLower.macroscopicIntegrable` and `Ascent.tv_le_one`; it contains no separately assumed convergence result. Its full elaborated type is in `compiled-declarations-v1.json` and the final audit log. The wrapper does not replace the uniform endpoint or add a fixed-branch premise.

## Scalar scope and historical contract

The source's current global integral convention implies measurability and integrability of the selected cell masses, `a` expectations, and `ψ_α` expectations used here; it also covers additional displayed integrands the macro lower proof does not need. The implementation assumes only the frozen reviewed scalar subset and uses no temporal kernel, time smoothness, or macro `J/H` regularity.

The historical `TimeLaw` remains merely a function from time to simplex probability measures. The fixed-cell nonmeasurable switching example in the pre-review still shows that deleting scalar regularity invalidates the needed two-sided transfer. Nothing in the finished code claims to eliminate that counterexample or upgrade the historical contract. The certified empirical endpoint has no temporal regularity; the newly certified macro endpoint visibly does. A claim of an unchanged-assumption arbitrary-totalized-TimeLaw theorem would therefore be incorrect, and is not made by these theorem types.

No global positive lower bound on pile coordinates, random-pile extension, upper first-moment theorem, altered margin, or zero-margin conclusion was found in either LB11 theorem or its inspected concrete assembly.

## Audit evidence and reviewed identities

The final build log reports `LB11 BUILD_OK`. The final audit checks 17 declarations and prints the exact target and scalar predicate. Both endpoints' complete transitive axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom, `sorryAx`, native proof oracle, or hidden endpoint premise is present in the inspected audit. The verification script rejects custom axioms and forbidden proof tokens, checks that source hashes do not change during verification, and invokes the checker with warnings treated as errors.

| Reviewed artifact | SHA-256 |
|---|---|
| `RiffleLowerV2/MacroscopicLower/Main.lean` | `9983f9b9b097ef9cfc67374521a1639693cb3b1e745890ab6bd2323acf5e33c7` |
| `RiffleLowerV2/MacroscopicLower/Parameters.lean` | `ac7da881e475df4b5820a240b36739c0a50b8a496f7830636d17de7419c14def` |
| `audit/LB11/Check_v1.lean` | `8729612d35b79e1b4e9cb9fac6a177fb94d9cc2b80d8a0eb67803179e3439004` |
| `audit/LB11/final-build-v1.log` | `e4c898c2b3d3e78ea6daf10044451b178b17310ad1559cc544c3783d7fd7ff9a` |
| `audit/LB11/final-audit-v1.log` | `f2d1d40a9f2d214bac9491ada373647a1f4908f07201d3e1a271de543dfae426` |
| `audit/LB11/compiled-declarations-v1.json` | `1c8970f358acba74127565eb71a31d299787ad87a4ea32735a83cdc42a8953e6` |
| `Contracts/dependencies/LB07-v1/SHA256.json` | `4280cdd4109f8bf6b817c237b63ad9825e34767b4652c1da5600b9ba661b1398` |
| `Contracts/dependencies/LB10-v1/SHA256.json` | `9fe2f82ad8be2c67eaa6b7f9f9e51e833b234952cbc339b238eefa70bfd399da` |

The source manuscript remains at SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, and the frozen v1 manifest remains at `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.

No mathematical revision or additional assumption is requested. Coordinator registration of LB11's completed lane remains a separate integration action; it does not detract from this acceptance of the checked lane implementation and exact theorem statements.
