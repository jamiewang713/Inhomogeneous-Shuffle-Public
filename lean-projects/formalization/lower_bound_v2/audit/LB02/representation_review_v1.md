# LB-02 independent Lean representation review, v1

Date: 2026-10-01. Scope: exact frozen interface and compatible proof routes, before dependent proofs. This review changes no proof, contract, shared definition, manuscript, build configuration, or old audit. It is a statement/interface review, not proof certification.

## Verdict

The frozen seven LB-02 targets represent the principal intended quantities correctly. No false statement was identified in this representation review. The released shared inputs pass the live readiness check. However, the seven-target inventory does not by itself certify every requested deliverable: explicit abstract thinning tails, concrete prefix transforms, conditional residual transform/tail specialization, and a single maximal-word exponential tail require additional proved declarations. In particular, `ResidualLaw` is a law identity, and `MaximalMeanIdentity` is a deterministic identity; neither is the requested corresponding tail theorem. These may be ordinary proved helper exports in the owned `Thinning/` directory with exact signatures and provenance recorded in the lane audit; they do not require new target predicates or shared-file changes. The existing LB-00 receipt authorizes the seven frozen targets. Only an actual shared-definition, frozen-target, or registered dependency change requires the coordinator's additive interface process.

## Evidence inspected

* User prompt `formalization/lower_bound_prompt_pack_2026-10-01/02_successive_thinning_and_uniform_prefix_concentration.txt`.
* Authoritative manuscript, lines 2995–3082 (`lem:successive-thinning-tail`), 3084–3106 (`cor:iterated-hypergeom`), and 3109–3142 (`prop:largest-prefix`).
* `Contracts/v1/ModelThinning.lean`, `AdditionalFinite.lean`, `AssemblyInputs.lean`, and the LB-02 entry in `OWNERSHIP.json`.
* `Shared/Model.lean`, `Statistics.lean`, `Adapters.lean`, `Empirical.lean`, and `Geometry.lean`.
* LB-00 `CONTRACT_READY.md`, `CONTRACT_READY.json`, `Contracts/v1/SOURCES.json`, `README.md`, `build.py`, and `scripts/lane.py`.
* Canonical `formalization/time_profile/RiffleTimeProfile/{Base,Ambient,FixedCountModel,FixedCountMoments}.lean` and foundations word definitions.
* Historical `lean/Shuffle/{FiniteLaw,Conditioning,Hypergeometric,HypergeometricMoments,HypergeometricConcentration,SubsetSampling,ResidualSampling,FixedColumns}.lean` and `lean-lower-bound/RiffleLower/FixedColumns.lean`.

Live read-only validation, run from `formalization/lower_bound_v2`:

```text
python3 scripts/lane.py LB02 --check-ready
LB02 CONTRACT_INPUTS_OK
```

This verifies frozen source/contract hashes, dependency revisions, the Lean runtime, and availability of the coordinator shared build. It does not prove any LB-02 target. The receipt records Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, the source SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, and v1 manifest SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.

## Exact frozen export inventory

Every required name below is to be a theorem in `RiffleLowerV2.Thinning`; its exact target type is a proposition-valued definition in `RiffleLowerV2.Targets`. A target definition is not a theorem or hypothesis automatically available to the lane.

| Required theorem | Exact target type | Target source |
| --- | --- | --- |
| `successiveThinning` | `RiffleLowerV2.Targets.SuccessiveThinning` | `ModelThinning.lean` |
| `prefixTails` | `RiffleLowerV2.Targets.PrefixTails` | `ModelThinning.lean` |
| `allPrefixConcentration` | `RiffleLowerV2.Targets.AllPrefixConcentration` | `ModelThinning.lean` |
| `prefixFailureUniform` | `RiffleLowerV2.Targets.PrefixFailureUniform` | `ModelThinning.lean` |
| `residualLaw` | `RiffleLowerV2.Targets.ResidualLaw` | `ModelThinning.lean` |
| `hypergeometricTransform` | `RiffleLowerV2.Targets.HypergeometricTransform` | `AdditionalFinite.lean` |
| `maximalMeanIdentity` | `RiffleLowerV2.Targets.MaximalMeanIdentity` | `AssemblyInputs.lean` |

All seven remain pending in the frozen ownership inventory. The latter two targets are not in `ModelThinning.lean`, so importing only that file is insufficient for the entry-point interface.

The quantified content, preserving exact order and constants, is:

1. `SuccessiveThinning`: for every `M d : ℕ`, `0 < M`, every `m : Fin d → ℕ` with `∀ j, m j ≤ M`, and every `s : ℝ` with `0 < s`, under `PMF.uniformOfFintype (Fin d → Permutation M)`,
   `expect ... (fun ω => s ^ thinningCount m ω) ≤ (1 - thinningQ M m + thinningQ M m * s)^M`
   and that right side is at most `Real.exp (M * thinningQ M m * (s-1))`.
2. `HypergeometricTransform`: for all `M x m : ℕ`, in order `0 < M → x ≤ M → m ≤ M → ∀ s : ℝ, 0 < s → ...`, the uniform-permutation expectation of `s` to the cardinality of `{i : Fin M | i.val < x ∧ (σ.symm i).val < m}` is at most `(1 - (m : ℝ)/M + (m : ℝ)/M*s)^x`.
3. `PrefixTails`: for all `Cuts k N K`, `0 < N`, and all `w : Prefix k K`, the conjunction consists of the two-sided inequality for every real `t > 0`, with event `t ≤ |(prefixCount w ω : ℝ) - prefixMean cuts w|` and denominator `4 * (prefixMean cuts w + t)`; the event `(prefixCount w ω : ℝ) ≤ prefixMean cuts w / 2` with bound `exp (-chernoffConstant * prefixMean cuts w)`; and the event `prefixCount w ω < 2` with bound `2 * exp (-prefixMean cuts w / 2)`.
4. `AllPrefixConcentration`: for all `Cuts k N K`, `2 ≤ N`, and real `ε > 0`, `probability (fixedCountPMF cuts) (fun ω => ¬allPrefixEvent ε ω) ≤ prefixFailure N k K ε`. There is no `2 ≤ k` premise.
5. `PrefixFailureUniform`: `∀ k : ℕ, 2 ≤ k → ∀ T ε δ : ℝ, 0 < T → 0 < ε → 0 < δ → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ K : ℕ, (K : ℝ) ≤ T * logScale N → prefixFailure N k K ε ≤ δ`. Thus the threshold depends on `k,T,ε,δ`, uniformly over `N,K` thereafter; the quantitative failure function already has no cut-array input.
6. `ResidualLaw`: for all `Cuts k N K` and `r : RowPrescription N k K b`, the premises are `b < N`, `Function.Injective r.row`, and strictly positive probability of `prescriptionEvent r`. The conclusion first existentially supplies `residual : Cuts k (N-b) K` with `residual.count j a = cuts.count j a - usedCount r j a`. For every injective `e : Fin (N-b) → Fin N` whose image is exactly the complement of the prescribed-row image, and every residual raw-row array `rows`, the conditional probability of `∀ q j, sampleEntry ω (e q) j = rows q j` equals `(((fixedCountPMF residual).map sampleRow) rows).toReal`.
7. `MaximalMeanIdentity`: `∀ k N K : ℕ, 2 ≤ k → ∀ (hN : 2 ≤ N) (cuts : Cuts k N K), ∃ w : Word k K, IsCanonicalMaxWord cuts w ∧ (N : ℝ)*wordMass cuts w = maximalMean cuts (deckPos hN) ∧ maximalMean cuts (deckPos hN) = (N : ℝ)^(beta cuts (deckPos hN) (horizon N K))`.

## Representation findings and required bridges

### PMF sampling and expectations

The canonical model is `TimeProfile.Cuts`, dependent `ColumnAssignments cuts j`, `ShuffleSample cuts := (j : Fin K) → ColumnAssignments cuts j`, and `fixedCountPMF cuts := PMF.uniformOfFintype (ShuffleSample cuts)`. Nonemptiness is proved, including empty decks. Each column PMF is uniform, but product independence must still be established by a finite product/cardinality identity; it is not literally defined as a product PMF. LB-01 owns its public `ColumnIndependence` target, so LB-02 must either prove the needed internal factorization independently from the finite sample definition or arrange a checked interface dependency. It must not assume the pending LB-01 target as an extra premise.

`RiffleLowerV2.expect` is the real finite sum `∑ ω, (P ω).toReal * f ω`; `probability` is this expectation applied to an indicator. The checked adapters are `expect_eq_integral` and `fixed_expect_eq_average`. `TimeProfile.column_product_factorization` and `column_marginal` in `FixedCountMoments.lean` are useful canonical source candidates, but that module is not among the eight canonical modules certified in the v1 imported project inventory. A fresh import needs coordinator registration/build or a documented lane-local source port; its existence on disk alone does not make it an available compiled dependency.

### Subsets and hypergeometric states

`thinningCount` uses images of initial segments under permutations, expressed as `(ω j).symm i < m j`. Each fixed-size subset appears the same `m! (M-m)!` times, but that equal-fibre result is a proof obligation when bridging to a uniform subset law. `HypergeometricTransform` fixes the marked set to an initial segment. Backward recursion requires its version for every deterministic current set `A : Finset (Fin M)`, with exponent `A.card`; prove row-permutation invariance/equinumerosity to transfer the initial-segment target. The current set becomes random only after conditioning on preceding columns. Do not apply the target to a random marked set without the conditioning/factorization step.

Empty `Fin d` correctly makes `thinningCount = M`, `thinningQ = 1`. Count bounds give `0 ≤ q_j ≤ 1`, including exact zero and one. The affine map `1-q+q*s` remains strictly positive for `s>0`. No row-independence claim is justified by this representation.

### Prefix domain and cardinality

`Word k n` is a length-indexed `List.Vector (Fin k) n`; `Prefix k K` is `RiffleShuffle.RawPrefix k K`, a sigma over lengths in `Fin (K+1)`. The count uses equality of the first `w.1.val` list entries with `w.2.toList`. A useful first bridge is that equality iff all coordinates indexed by `Fin w.1.val` agree with the word digits. It connects the actual list predicate to the subset intersection without choosing unused suffix digits.

The exact number of prefixes is `∑ ℓ=0..K, k^ℓ`. A union bound must genuinely run over this sigma domain and then prove the upper bound `(K+1) * k^K`; enumerating all full words once per length would add unnecessary suffix multiplicity and cannot justify the stated cardinality directly. Because `AllPrefixConcentration` allows `k=0,1`, a proof that assumes `1 ≤ k` globally is insufficient. For `k=0` and `K>0`, positive `N` makes the cuts impossible; for `k=0,K=0`, only the empty prefix exists and its event is deterministic. For `k=1`, every feasible prefix count is deterministic, and the ordinary geometric bound also applies.

Zero-mass prefixes must be included, with zero count proved from exact column counts. The checked `emptyPrefix_mass` and `emptyPrefix_count` handle the empty prefix, with mass one and count `N`. Note the namespace collision: `RiffleLowerV2.prefixMass` is dimensionless probability mass, whereas `TimeProfile.prefixMass` already includes the factor `N`. Always qualify the latter when adapting old canonical lemmas; confusing them silently introduces or loses `N`.

`prefixFailure` is exactly `2 * (K+1) * (k : ℝ)^K * exp (-(N : ℝ)^ε / 8)`. The pointwise tail at `t = N^ε(sqrt μ+1)` bounds the complement of the non-strict event by monotonicity, since failure is a strict inequality and `PrefixTails` uses `t ≤ ...`. The convergence proof must expose the polynomial count cost and the uniform quantifier order above, not merely convergence for a chosen sequence of cuts.

### Residual conditioning

`RowPrescription` deliberately stores only indices and digits, without injectivity/admissibility baked into the structure. The theorem's separate positive-probability premise must be used to prove `usedCount r j a ≤ cuts.count j a`, then the residual sum equals `N-b`. Natural subtraction without that inequality hides infeasible prescriptions.

The existential residual cuts retain every column and every digit, including zero remaining counts. The arbitrary enumeration `e` must be justified as a bijection onto unused labels. The frozen target equates point masses of the entire residual row array; this is strong enough to derive every residual function/event law by finite summation, but those expectation/probability pushforward adapters remain required work. Residual prefix counts are the original prefix counts minus the number of prescribed rows matching that prefix; for a full word they are original word counts minus prescribed full-word occurrences. Their mean is `(N-b)` times the product of residual digit fractions with denominator `(N-b)`, never `N`.

### Maximal word

`IsCanonicalMaxWord` requires both maximal count in each column and the smallest-digit tie rule. Any proof choosing an arbitrary maximizer must additionally discharge that tie condition. The word is existentially quantified before sampling and therefore deterministic. The frozen identity is restricted to `k≥2,N≥2`, whereas LB-10's finite `FiniteLargestWordTV` target permits any alphabet/deck with its stated hypotheses. A general maximal-word mass/tail adapter should therefore cover feasible `Cuts` with `N>0`; the vacuous zero-alphabet/empty-column case must be handled rather than silently importing the stricter identity premises.

## Missing explicit proof exports and helper proposals

These are additional proved outputs or useful internal bridge interfaces, not missing frozen target predicates and not changes to frozen assumptions. They can be implemented as ordinary lane-owned helper theorems without modifying `Contracts/` or `Shared/`. Record their exact names and types in the lane audit. This review does not require a new LB-00 receipt for such ordinary helpers; a new receipt is needed only if the implementation actually needs a shared-interface or dependency-registration change.

1. Abstract `thinningTails` under exactly `M>0`, `m_j≤M`, for all three manuscript bounds and `μ=M*thinningQ M m`. This records that the full subset-process lemma, not only its transform, has been proved.
2. A concrete `prefixTransform` under `N>0`, every sigma prefix, and all `s>0`, with both binomial and exponential bounds. It discharges the subset-process-to-canonical-matrix specialization.
3. A concrete conditional residual transform/tail result with `b<N`, injective rows and positive conditioning probability. Define the residual count and residual mean explicitly using the removed prescribed occurrences and denominator `N-b`. A theorem only parameterized by an unproved residual-law assumption is not completion.
4. A deterministic canonical maximal-word exponential tail usable by LB-10: existence of a canonical word with mean `maximalMean`, and its actual matrix-law probability of `wordCount < m` bounded by `exp(-chernoffConstant*maximalMean)` whenever real `m≤maximalMean/2` (or a direct `wordCount≤μ*/2` statement). The run/permutation/TV conclusion remains LB-10/LB-01 work.

The established `PrefixTails` and `MaximalMeanIdentity` can yield item 4 within their common domain after a short specialization, but a named checked theorem is still the requested export. The residual point-mass law can yield item 3 after actual finite-sum adaptation; reporting it as if specialization were already proved would be incorrect.

## Compatible reuse and provenance route

The old `lean` and `lean-lower-bound` toolchain files both specify Lean 4.19.0. Their `.olean` caches cannot be mixed with the new 4.33.1 environment. New-package `build.py` recognizes only `RiffleLowerV2`, `Contracts`, `RiffleTimeProfile`, and `RiffleShuffle` as project roots; it does not register `Shuffle` or `RiffleLower`. A direct old-namespace import will therefore fail lane readiness unless the coordinator supplies a separately checked port. New source ports can instead live entirely in owned `RiffleLowerV2/Thinning/` modules with recorded original paths/hashes and actual new-runtime compilation.

Historical reusable ingredients are substantive but require bridges:

* `Shuffle.HypergeomParams.expect_pow_le` is public only for `0<s≤1`. It is not the all-s theorem. The private `expect_one_add_pow_le` already proves the `s≥1` case via binomial coefficients and descending-factorial ratios, and private `expect_exp_le` uses both regimes. A source port may expose the all-s conclusion by this algebraic split; no averaging convergence argument is then needed. Do not refer to a mangled private name as the permanent public API.
* `HypergeomParams.expect_choose` and `expect_descFactorial` support that algebraic extension. The hypergeometric law has `Fin (draws+1)` support and real `FiniteLaw` masses. The frozen target instead uses permutation PMFs, so exact expectation equality after the equal-fibre/subset law bridge is mandatory.
* `Shuffle.FiniteLaw.toPMF`, `toPMF_toReal`, and `integral_toPMF` provide source material for a probability representation bridge. The old `FiniteLaw.prob` indicator arrangement and new `probability` are extensionally equal after proving PMF identification; they are not definitionally the same object.
* `Shuffle.sample_intersection_mass` / `sample_intersection_law` identify uniform fixed-size subset intersections with the hypergeometric coefficient law. `ResidualSampling` additionally supplies admissibility and conditional subset-intersection laws.
* `Shuffle.Histogram.conditional_residual_law` and `conditional_fixedMatrix_residual_law` supply the finite-column residual argument, including product factorization after rectangle conditioning. Their arbitrary finite-type histograms and complement subtypes need explicit adapters to `Cuts`, `ColumnAssignments`, labelled injections, and the user's `Fin (N-b)` residual enumeration.
* Historical `RiffleLower.wordCount_lower_tail` is only a variance/Chebyshev bound. It is useful background for model moments but cannot certify the requested exponential lower tail.

Recommended downstream imports after completion: `RiffleLowerV2.Shared`, `Contracts.v1`, and the newly compiled `RiffleLowerV2.Thinning.Main`. The lane build command is `python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Main`, which writes only the lane overlay. Whole-package/dependency-cache changes remain the coordinator's responsibility. Preserve the v1 manifest and old receipt. Ordinary lane-owned helper exports need a lane delivery ledger, not a contract rewrite. Any actual shared-interface changes need a separately reviewed additive version/receipt.

## Closure of this review

Readiness is verified; all target definitions and the mathematical sampling interpretations have been inspected. This report supplies no new proof and certifies no LB-02 axiom closure. Before delivery, compile every exported theorem and inspect its elaborated axiom dependencies, with allowed closure limited to checked Lean/mathlib foundations. Resolve the missing explicit exports and the PMF/subset/residual bridges above in the implementation ledger.

## Clarification on ordinary helper exports

The contract explicitly permits new proved helper lemmas. Additional abstract-tail, residual-specialization, and maximal-word-tail declarations inside the owned `RiffleLowerV2.Thinning` namespace require no shared target or `Contracts/` change when all seven v1 targets remain unchanged. No missing shared definition identified in this review forces an additive interface change. Their exact signatures are to be reviewed and documented locally in `audit/LB02/`. The existing LB-00 receipt covers starting proofs of the frozen v1 targets. This reviewer has no substantive objection to that plan.
