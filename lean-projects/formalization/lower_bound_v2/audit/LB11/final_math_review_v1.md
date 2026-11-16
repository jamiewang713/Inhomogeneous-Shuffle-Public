# LB11 final independent mathematical implementation review v1

Verdict: PASS for the uniform scalar-integrable macroscopic endpoint and its sequence corollary at the source hashes below. No mathematical revision is requested. The implementation discharges its actual LB07 and LB10 inputs; it neither assumes the requested endpoint nor proves only a generic conditional substitute. The earlier coordinator-registration obstacle is resolved by the validated LB07-v1 and LB10-v1 dependency receipts.

## Source identity and independent verification

| Source | SHA-256 |
|---|---|
| `RiffleLowerV2/MacroscopicLower/Parameters.lean` | `ac7da881e475df4b5820a240b36739c0a50b8a496f7830636d17de7419c14def` |
| `RiffleLowerV2/MacroscopicLower/Main.lean` | `9983f9b9b097ef9cfc67374521a1639693cb3b1e745890ab6bd2323acf5e33c7` |

The parameters hash agrees with the prior independent parameters review. Both source files were read in full for this final review. The target was compared with frozen `Contracts/v1/Endpoints.lean`; scalar assumptions and margins were compared with shared `Empirical.lean`; the upper TV bound was checked in `Ascent/Mixture.lean` against shared `Model.lean`'s half-L1 TV definition.

Independent checks performed during this review:

- `python3 scripts/check_dependency_receipt.py LB07-v1`: exit 0, `LB07-v1 DEPENDENCIES_OK`.
- `python3 scripts/check_dependency_receipt.py LB10-v1`: exit 0, `LB10-v1 DEPENDENCIES_OK`.
- Re-elaboration of `RiffleLowerV2/MacroscopicLower/Main.lean` with the pinned Lean 4.33.1 compiler, `LEAN_PATH=<package>/.build/lanes/LB11/lib/lean`, and `-DwarningAsError=true`: exit 0, no diagnostics. This read-only check wrote no compiled outputs.
- Independent execution of `audit/LB11/Check_v1.lean` with the same compiler/options: exit 0, `LB11_REQUIRED_THEOREMS_VERIFIED`. The declaration inventory identifies both exports as theorems. Their transitive axiom closure is exactly `propext`, `Classical.choice`, `Quot.sound`.

The source proof was re-elaborated; the axiom/type check then inspected the owner-built module. The owner's `main-dev02.log` also records `LB11 BUILD_OK`. This is a lane mathematical implementation review, not a claim to have independently rebuilt every upstream source or replaced the separate LB12 project-wide audit.

## Uniform endpoint: proof dependency and arithmetic audit

The export is exactly

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
  RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

`Main.lean` actually invokes `ProfileTransfer.profileTransfer`, `EmpiricalLower.largestOnly`, and `EmpiricalLower.coldOnly`; their target predicates are not additional theorem premises. The compiled direct constant inventory confirms those concrete dependencies.

Fix k >= 2, T > 0, eta > 0. The proof chooses `e = transferAccuracy eta = min (kappa0 (eta/2)/10) (eta/100) / 2` before invoking LB07. The previously reviewed helpers prove its positivity and strict required budgets, `0 < kappa0 (eta/2) <= eta/200000`, and the positive bridge ceiling `(kappa0 (eta/2)/100)/(2 log k)`.

LB07 chooses chi, the regular partition P, and rho0 from these already-fixed inputs. Its rho bound is converted into the exact source bridge restriction. The proof returns these very same witnesses to the final endpoint. After a fixed rho is selected, it obtains and returns LB07's phi0. After fixed phi, positive chiGood/gamma, epsilon, μ, and `ScalarIntegrable μ P T` are supplied, it obtains the actual transfer threshold Nt. There is no partition refinement or second integrability premise for a different partition.

`ColdParameters k (eta/2) chiGood gamma rho` is constructed from the actual supplied positive constants and the proved mesh budget. Thus the calls to both empirical endpoints have all fixed-parameter hypotheses discharged before N and the cut array are introduced.

Four thresholds are fixed:

1. Nt from actual profile transfer for this μ and P;
2. Nd from `transferThreshold (log k) e`;
3. Nl from largestOnly at margin `kappa0 (eta/2)` and requested epsilon;
4. Nc from coldOnly at margin eta/2 and the same requested epsilon.

The common threshold is `max Nt (max Nd (max Nl Nc))`, and its lower bound by 2 is obtained from the actual largest endpoint threshold. The four threshold comparisons hold before any numerical branch is selected, so uniformity is retained over every admissible cut array.

At an arbitrary N past this threshold, the split is exactly

```lean
kappa0 (eta / 2) ≤ beta cuts (deckPos hN)
  (horizon N (horizonDepth N T))
```

The nonnegative branch calls the checked largest-word theorem directly with its fixed positive margin. It does not require transfer or add an artificial local-good premise to that empirical theorem.

In the complementary strict branch, `htransferN ... hLike` supplies the actual two-sided margin errors for this same cut array. The logarithmic helper gives `d = log k / logScale N <= e/4`. The lambda error is converted by the algebraic identity `14 log k / logScale N = 14 d`; the `mul_div_assoc` normalization changes no constant. The parameter lemma then uses the correct lower sides of both absolute-value bounds to get

\[
\Lambda_0(T)<k_0+5e/4<\eta,\qquad
\Lambda_{1,N}\ge\Lambda_1(T)-10e.
\]

The assumed maximum and first strict bound imply `Lambda1(T) >= eta`, hence `Lambda1,N >= eta/2`. The final coldOnly call receives actual hGood, that derived cold margin, and the actual strict small-beta branch. No witness, localization, convergence, branch certificate, or hidden target proposition is left as a final assumption.

Both branches supply exactly `1 - epsilon <= tv` with the same common threshold. There is no addition of branch errors, sequence-dependent threshold, or assumption that the selected branch eventually stabilizes. Arrays that alternate arbitrarily between branches are included.

## Sequence wrapper and TV upper bound

The second export is `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto`. It begins by invoking the proved uniform theorem and returns its same partition/parameter witnesses. It assumes only eventual AlmostLike and LocalGood for a sequence of actual horizon cut arrays, the same scalar predicate, and the macro maximum condition.

The order-topology argument is correct. For any a < 1, it chooses epsilon = (1-a)/2 > 0; the uniform endpoint gives eventual TV >= 1-epsilon = (1+a)/2 > a. Eventual admissibility is combined with the common numerical threshold, from which `N >= 2` is derived before instantiating the proof-indexed conditions. Arbitrary initial arrays are therefore harmless. For b > 1, the generic proved inequality `Ascent.tv_le_one` gives TV <= 1 < b for every N. This proves convergence to 1 without needing an additional lower TV bound or any unstated rate.

The inspected `tv_le_one` theorem concerns exactly the shared finite half-L1 TV of two PMFs and proves its upper bound from normalization and `|p-q| <= p+q`. It has no graph, local-good, regularity, or deck-size premise. Its use at small N and in this wrapper is therefore valid. The compiled dependency inventory confirms that the wrapper depends on `macroscopicIntegrable` and `Ascent.tv_le_one`, so the Tendsto result genuinely follows from the uniform theorem.

## Assumption and source correspondence

- `thm:buffered-reduced-lower-bound`: the uniform export is the complete branch assembly, with the frozen explicit scalar addition.
- `lem:lower-profile-transfer`: supplied by LB07 on the selected P, with exact constants e and 13e/2 plus the frozen logarithmic tails.
- `prop:cold-lower`: supplied by the proved LB10 cold endpoint with eta_f = eta/2, the exact kappa/kappa0 scales, actual LocalGood, and all derived branch margins.

The full uniform type fixes P before `ScalarIntegrable μ P T`, and fixes rho, phi, chiGood, gamma, epsilon and μ before N0. Only N and all cut arrays occur after N0. The predicate requires interval integrability of the selected-P cell masses, profileMaxCost, and profilePsi for every alpha in [2,4]. No measurable-kernel hypothesis, time continuity, global positive pile lower bound, homogeneous cutoff substitution, upper first-moment result, random-pile extension, or zero-margin conclusion occurs.

This certifies the separately named scalar-integrable macroscopic endpoint. The empirical LB10 endpoint has no temporal regularity assumption. The historical arbitrary totalized-TimeLaw formulation remains a different, uncertified statement; neither this implementation nor this review silently upgrades it. The manuscript's broader ordinary-integral convention is compatible with the restricted explicit premise but is not encoded into TimeLaw itself.

Final mathematical finding: no unresolved obligation in LB11's implementation at the recorded hashes. Preserve the distinct scope of the later project-wide integration and LB12 audit.
