# LB08 independent statement and representation review v1

Date: 2026-10-01. Scope: pre-proof review only. This report does not certify an LB08 proof or alter any contract. The only file written by this reviewer is this report.

## Verdict

The three frozen LB08 targets express the intended actual-model statements and need no changed hypotheses or shared definitions. They require genuine uniform estimates, including arbitrary positive word means and arbitrary deterministic finite word families. The conditional target is deliberately stronger than conditioning only on two or three copies of a different word: it permits every fixed bounded number of prescribed rows, arbitrary prescribed words, and prescribed copies of the tested word, while subtracting those copies from the count.

There are two separate readiness issues before dependent proofs: (1) LB02 has a checked completed lane, but its imports are not yet integrated in the coordinator overlay; (2) the requested pre-proof LB08 unchanged-interface acknowledgement is not present. LB03 is both completed and integrated. These are workflow/import obstacles, not a counterexample or an absent upstream mathematical proof.

## Exact required exported types

The immutable `OWNERSHIP.json` specifies:

```lean
RiffleLowerV2.Occupancy.uniformOccupancy :
  RiffleLowerV2.Targets.UniformOccupancy
RiffleLowerV2.Occupancy.conditionalCollisionStability :
  RiffleLowerV2.Targets.ConditionalCollisionStability
RiffleLowerV2.Occupancy.collisionChebyshev :
  RiffleLowerV2.Targets.CollisionChebyshev
```

`UniformOccupancy`, defined in `Contracts/v1/FactorialOccupancy.lean`, has quantifier order

```text
c,C : real; 0<c; 0<C;
exists D>0; exists N0;
for all N>=N0; k,K : natural; K <= C logScale(N);
cuts : Cuts k N K; W : Finset (Word k K); selectedPiles cuts W c;
  marginal estimate AND pair estimate AND variance estimate.
```

Writing `P = fixedCountPMF cuts`, `mu(w) = N * wordMass cuts w`, `p(w) = probability P (collisionEvent w)`, `tau = (N : ℝ)^(-1/100 : ℝ)`, and `EZ = expect P (collisionCount W)`, its exact three conclusions are:

```text
forall w in W,
  |p(w) - poissonCollision(mu(w))| <= D*tau*poissonCollision(mu(w));
forall w in W, v in W, w != v,
  |probability P (fun omega => collisionEvent w omega AND collisionEvent v omega)
     - p(w)*p(v)| <= D*tau*p(w)*p(v);
variance P (collisionCount W) <= EZ + D*tau*EZ^2.
```

The multiplication form is essential until positivity is proved. One common `D,N0` must work for all three conclusions, with neither permitted to depend on `k,K,cuts,W,w,v`.

`ConditionalCollisionStability`, in `Contracts/v1/TransferFinite.lean`, has quantifier order

```text
c,C : real; 0<c; 0<C; b0 : natural;
exists D>0; exists N0; b0<N0 AND 2<=N0;
for all N>=N0; k,K,b : natural; b<=b0; K<=C logScale(N);
cuts : Cuts k N K; p : RowPrescription N k K b; w : Word k K;
Injective p.row;
0 < probability (fixedCountPMF cuts) (prescriptionEvent p);
(forall j, c*N <= cuts.count j (w.get j));
```

and concludes

```text
|conditionalProbability (fixedCountPMF cuts)
    (fun omega => 2 <= wordCount w omega
      - (Finset.univ.filter (fun q => p.word q = w)).card)
    (prescriptionEvent p)
  - poissonCollision(N*wordMass cuts w)|
<= D*(N : real)^(-1/100 : real)*poissonCollision(N*wordMass cuts w).
```

The subtraction is in `ℕ`. Its match to deletion is proved only on the conditioning event. The centering Poisson mean is the original mean, not the residual mean; `residualMeanComparison` and a uniform comparison for `poissonCollision` must be used. There is no positivity assumption for every prescribed word's selected piles. Only the tested word's piles are lower bounded; positive prescription probability supplies compatibility for the other prescribed words.

`CollisionChebyshev`, in `Contracts/v1/AssemblyInputs.lean`, has the same outer data and uniform `D,N0` order as `UniformOccupancy`, then universally quantifies `t>0` and assumes `0<EZ`. Its conclusion is exactly

```text
probability P (fun omega => t*EZ <= |collisionCount W omega - EZ|)
  <= 1/(t^2*EZ) + D*(N : real)^(-1/100 : real)/t^2.
```

The threshold and constant precede `t`; empty families remain admitted by the occupancy theorem and make the positive-mean Chebyshev hypothesis false. A concrete success consequence is `P(Z>0) >= 1 - 1/EZ - D*tau`, using `t=1`. A lower-tail success bound for `Z >= (1-t)*EZ` is likewise a consequence. Neither should replace the frozen two-sided concentration conclusion.

## Actual sample representation

The law is the canonical `TimeProfile.fixedCountPMF cuts`, defined as the uniform PMF on the finite product `ShuffleSample cuts = ∀ j, ColumnAssignments cuts j`. `Sample cuts` abbreviates this type. Every column assignment carries its exact counts as a subtype proof. Independence of the columns follows from this product law; independence of two word occupancies is not present and cannot be assumed.

`Word k K` abbreviates `RiffleShuffle.Word k K`, a length-`K` vector of `Fin k` digits. `wordCount w` is `prefixCount (fullPrefix w)`, and `wordMass cuts w` is `prefixMass cuts (fullPrefix w)`. The full prefix has all `K` actual coordinates. `expect`, `probability`, and `variance` are the shared real finite-PMF sums, not the old `FiniteLaw` definitions and not measure-integral notation.

`W : Finset (Word k K)` already represents a deterministic distinct family. No additional injectivity premise is needed for `W`. Specializing LB03 to a `Fin 2` tuple requires an injectivity proof derived from `w != v`. Its `Fin 1` specialization handles marginal moments. The full targets permit `K=0`, arbitrary `k`, and empty `W`; do not silently add `K>0`, `k>=2`, nonempty `W`, a lower mean cutoff, or an upper mean bound.

## Upstream evidence checked

LB02 receipt: `audit/LB02/LB02_READY_v1.json`, status COMPLETE. All 29 bound owned source hashes match. The final build, readiness, and compatibility-provenance log hashes match. I re-ran the existing `RiffleLowerV2/Thinning/Check.lean` using Lean 4.33.1 and `LEAN_PATH=.build/lanes/LB02/lib/lean`, without an output argument or cache write. Exit code was zero; its whole-namespace axiom audit accepts only `propext`, `Classical.choice`, and `Quot.sound`.

Relevant exact proved LB02 exports are:

```lean
Thinning.prefixTails : Targets.PrefixTails
Thinning.residualLaw : Targets.ResidualLaw
Thinning.residualPrefixTails
Thinning.residualConditionalExpect
Thinning.residualConditionalProbability
Thinning.residualPrefixCount_eq_restriction
Thinning.residualPrefixMass_eq
Thinning.residualPrefixMean_eq
```

`Thinning.residualPrefixTails cuts p hb hr hp u` applies to any prefix `u`, any injective prescribed rows, and a positive prescription event, with `hb : b<N`. Its last conjunction component bounds the conditional probability of `residualPrefixCount p u < 2` by `2*exp(-residualPrefixMean cuts p u/2)`. Taking `u=fullPrefix w` is the required full-word tail. Its mean has population `N-b` and each selected numerator subtracts `usedCount p j (w.get j)`.

LB03 receipt: `audit/LB03/verification_v1.json`, status complete. All 15 bound source hashes and all 3 bound evidence hashes match. I re-ran `audit/LB03/Check_v1.lean` with the existing LB03 overlay and Lean 4.33.1; exit code was zero. Its ten exact target assignments and eleven published axiom closures pass. The coordinator acknowledgement `audit/LB00/LB03_INTEGRATION_ACK_v1.md` is present. Read-only `PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_dependency_receipt.py LB03-v1` returned `LB03-v1 DEPENDENCIES_OK`.

Relevant checked exports, all in `RiffleLowerV2.Factorial`, are:

| Name | Exact frozen type |
|---|---|
| `exactJointFactorial` | `Targets.ExactJointFactorial` |
| `relativeJointFactorial` | `Targets.RelativeJointFactorial` |
| `residualJointFactorial` | `Targets.ResidualJointFactorial` |
| `residualRelativeFactorial` | `Targets.ResidualRelativeFactorial` |
| `residualMeanComparison` | `Targets.ResidualMeanComparison` |
| `bonferroniSandwich` | `Targets.BonferroniSandwich` |
| `bonferroniProduct` | `Targets.BonferroniProduct` |
| `centralComparison` | `Targets.CentralComparison` |
| `centralComparisonOne` | `Targets.CentralComparisonOne` |
| `rareSandwich` | `Targets.RareSandwich` |

`conditional_wordCount_eq_residualWordMean` also identifies the actual conditional deleted count expectation with `Targets.residualWordMean`. Its premises are `b<N`, injective prescribed rows, and positive conditioning probability; it does not assume the desired conditional collision estimate.

`relativeJointFactorial` has relative error `D*(K+1)*(sum r)^2/N` and order bound `(sum r : ℝ) <= N^(1/5 : ℝ)`. The residual version preserves the ambient `N` in both this bound and the logarithmic horizon while using population `N-b` inside the actual moment and residual mean. LB08 must preserve that distinction.

`centralComparison` is appropriately generic, not an actual-model completion: it needs all mixed moments with `r+s<=2*m`, positivity of both means, `0<=epsilon<=1`, `m>=2`, and even `m`. Its error is `epsilon*(1+mu)*(1+nu)*exp(mu+nu)` plus three times the sum and product of Poisson remainders. The one-variable version needs moments up to `m` and has error `epsilon*(1+mu)*exp(mu) + 3*poissonRemainder m mu`. `rareSandwich` has exactly the source's lower correction `E[(X)_3]/3`.

## Compatible imports and readiness obstacle

Intended LB08 entry point: `RiffleLowerV2.Occupancy.Main`. Intended proof imports:

```lean
import RiffleLowerV2.Factorial.Main
import RiffleLowerV2.Thinning.Main
```

The frozen contracts are already transitively available through these modules. `Factorial.Main` exists in both `.build/lanes/LB03/lib/lean` and the coordinator `.build/lib/lean`. `Thinning.Main` exists only in its private LB02 overlay at the time of this review; `.build/lib/lean/RiffleLowerV2/Thinning/Main.olean` is absent. No `Contracts/dependencies/LB02-*` registry or LB00 LB02 integration acknowledgement is present.

`scripts/lane.py` does not consume sibling private lane overlays: it constructs read-only links from the coordinator `.build/lib/lean`, recursively compiles only owned namespace modules, and rejects missing non-owned imports with `Upstream module not registered by coordinator`. Therefore LB08 cannot use the normal permitted build with `Thinning.Main` yet. The correct request is LB00 integration of the completed LB02 sources with a new additive receipt. Do not copy sibling oleans, alter LEAN_PATH to hide the missing integration, build upstream modules as LB08, or rewrite the frozen lane tool.

After integration and the pre-proof LB08 unchanged-interface acknowledgement, the normal owned build is:

```text
python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Main
```

Its output belongs in `.build/lanes/LB08/lib/lean`, and new logs belong in `audit/LB08/`. The base `--check-ready` check verifies only frozen/shared inputs; by itself it is not evidence of LB02 availability.

## Necessary local bridges and recommended proof interface

No shared interface amendment is necessary. The following local proved helpers fit inside `RiffleLowerV2/Occupancy/` and do not change the frozen result:

1. Full-prefix adapters equating `Thinning.residualPrefixCount p (fullPrefix w)` with the deleted full-word count and `Thinning.residualPrefixMean cuts p (fullPrefix w)` with `Targets.residualWordMean cuts p w`. The former uses full-length vector equality; the latter is a coordinate-index simplification.
2. Positivity of each selected mean for `N>0`; eventual positivity of the selected collision probability from a strict relative error below one. Positivity must be proved before ratio versions are stated.
3. A conditional central/rare argument using a genuine conditional PMF or the concrete residual law. An expression `conditionalExpect` is a quotient of sums and cannot be passed as though it were an unconditionally normalized PMF.
4. Positive probability of the forced two/three-row same-word events. `Factorial.column_request_probability` and `Factorial.request_probability` give exact labelled-event probabilities, and `factorialProduct_eq_requests` expands factorial counts into sums over embeddings. These checked existing helpers avoid assuming row exchangeability or importing LB01. The selected-pile bound ensures each required falling factorial is positive eventually.
5. Multiplication inequalities for `poissonCollision` under relative mean perturbation, uniformly down to arbitrarily small positive means. The logarithmic derivative bound is a method of proving this helper, not a new hypothesis.
6. A generic variance-sum identity and finite-PMF Chebyshev bound, instantiated with the shared `collisionCount`. The older `lean-lower-bound/RiffleLower/FiniteProbability.lean` contains suitable elementary proof patterns, but uses a different `FiniteLaw` representation and Lean 4.19.0. It cannot be imported as a compatible checked dependency. Any small local port requires named source provenance. Existing `Factorial.Basic` already provides normalized shared-PMF expectation algebra; `Thinning.PMFTools` provides Markov and probability monotonicity. No LB04 dependency is needed merely to obtain finite-probability helpers.

The central proof must explicitly establish `m=2*(floor(floor(N^(1/25))/4))>=2`, evenness, `2*m<=R`, `R<=N^(1/5)`, and all residual budgets before invoking LB03. Bounds of order `(log N)^3*N^(-18/25)` and the complete polynomial remainders must be reduced to the claimed `N^(-7/10)` scale with actual constants and thresholds. An assumed eventual error budget or assumed relative marginal/pair estimate would merely rename LB08's work.

For conditional stability, a useful acyclic proof order is: original/residual one-category estimates; residual-mean perturbation; conditional stability for arbitrary bounded prescriptions; rare-pair estimates; moderate/large pair cases; variance; Chebyshev. The rare-pair case only needs the proved conditional theorem with `b0=3`, but the exported conditional theorem must retain arbitrary `b0`.

## Review resolution requested

Approve the frozen three-export interface unchanged, integrate the completed LB02 input, and retain all above positivity, conditioning, rate, and finite-sum obligations as explicit LB08 proof work. No target is false on the evidence of this representation review; no dependent LB08 proof has been started here.

I also inspected the coordinator's `audit/LB08/INTERFACE_PROPOSAL_v1.md`. Its three export names/types, quantifier order, retained deleted-row statistic, no-extra-assumptions statement, import plan, and staged proof decomposition agree with this review. I approve that proposal unchanged, subject to the explicitly recorded input integration and acknowledgement gates.
