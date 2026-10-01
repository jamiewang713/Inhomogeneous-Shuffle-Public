# LB-03 independent representation review, v1

Reviewer scope: read-only pre-proof review of the assigned prompt, authoritative manuscript, frozen v1 definitions and targets, historical `FixedColumns.lean`, canonical `FixedCountModel.lean`, current build machinery, and relevant pinned mathlib source. No proof implementation or shared-file modification was performed. This report is a statement/API review, not a certification of the pending theorems.

## Verdict and readiness

The frozen representation expresses the requested finite mathematics without an additional shared-interface change. In particular, the two residual quantitative targets are already present in `Contracts/v1/TransferFinite.lean`; examining only `FactorialOccupancy.lean` and `AdditionalFinite.lean` would miss them.

`audit/LB00/CONTRACT_READY.{md,json}` releases contract v1, with manifest SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`, source SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, Lean 4.33.1, and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The read-only command

```text
python3 formalization/lower_bound_v2/scripts/lane.py LB03 --check-ready
```

returned `LB03 CONTRACT_INPUTS_OK` during this review. This verifies the frozen inputs and runtime identities; it is not an LB-03 proof build.

## Required exact exports

`OWNERSHIP.json` assigns the following declarations in namespace `RiffleLowerV2.Factorial`; each must be a proved theorem of the indicated type, rather than a new definition naming that proposition.

| Declaration | Frozen type | Source correspondence |
| --- | --- | --- |
| `exactJointFactorial` | `Targets.ExactJointFactorial` | Exact labelled-row formula in the proof of `lem:fixed-column-factorial` |
| `relativeJointFactorial` | `Targets.RelativeJointFactorial` | Statement of `lem:fixed-column-factorial` |
| `bonferroniSandwich` | `Targets.BonferroniSandwich` | `eq:collision-bonferroni-sandwich` |
| `bonferroniProduct` | `Targets.BonferroniProduct` | Product remainder in `lem:central-window` |
| `centralComparison` | `Targets.CentralComparison` | Two-variable conclusion of `lem:central-window` |
| `centralComparisonOne` | `Targets.CentralComparisonOne` | One-variable conclusion of `lem:central-window` |
| `rareSandwich` | `Targets.RareSandwich` | `eq:collision-rare-bonferroni`, as explicitly assigned by LB-03 |
| `residualJointFactorial` | `Targets.ResidualJointFactorial` | Prescribed-row/deleted-row exact formula, assigned extension |
| `residualRelativeFactorial` | `Targets.ResidualRelativeFactorial` | Uniform residual moment assertion used after `eq:collision-uniform-factorials` |
| `residualMeanComparison` | `Targets.ResidualMeanComparison` | Residual mean comparison preceding `eq:collision-conditional-stability` |

The entry point is `RiffleLowerV2.Factorial.Main`; the lane output area is `.build/lanes/LB03/lib/lean`. `UniformOccupancy`, despite being in `FactorialOccupancy.lean`, belongs to LB-08 and is not an LB-03 export.

## Domains, definitions, and source fidelity

1. `Sample cuts` abbreviates the canonical `TimeProfile.ShuffleSample cuts`, a dependent product of the genuine fixed-count assignment types `ColumnAssignments cuts j`. `fixedCountPMF cuts` is the uniform PMF on this finite product. This is a concrete law, not a record carrying the desired moments as fields. `expect` is the finite real sum of PMF weights times the observable. `fixed_expect_eq_average` and `TimeProfile.fixedCount_integral_eq_average` supply checked connections to finite averages/integrals.

2. Full words are length-`K` vectors (`Word k K`), and `rowWord_get` connects their entries to the canonical matrix entries. `wordCount` uses the full prefix, so a useful lane helper should identify it with the cardinality of rows satisfying `rowWord ω i = w`. A proof that treats words as arbitrary functions must explicitly use the vector/function equivalence and extensionality. Distinctness is `Function.Injective w` on `Fin d`; it is full-word distinctness, not digitwise distinctness in every column.

3. `falling n r` is the real cast of `Nat.descFactorial n r`. It agrees with the zero-extended natural falling factorial, including `r > n`. `requestedCount w r j a` is the natural sum of the orders whose words request digit `a`. `exactFactorial` has exactly the manuscript factor `(N)_R` outside the product and one denominator `(N)_R` for every column. The exact target assumes `R ≤ N`; thus its denominator is positive, including the case `N = R = 0`, where it is 1. Neither positivity of individual piles nor `N > 0` should be added to this exact theorem.

4. The quantitative target has quantifier order
   `∀ c C, 0<c → 0<C → ∃ D>0, ∃ N0, ∀ N≥N0, ∀ k K d, ...`.
   Hence `D,N0` may depend on `c,C` but not on the alphabet size, number of words, actual words, orders, column counts, or `K` within the stated range. The source permits a finite upper-bound constant `C`; replacing it by a positive larger constant covers that convention, so the frozen positive-`C` formulation is sufficient. The hypothesis `R ≤ N^(1/5)` is a real-power comparison, not natural-number division. The missing explicit `R≤N` premise is intentional: choose `N0≥1` and derive it. For `R=0` the stated right side vanishes, requiring exact equality. For `K=0`, the empty product makes the unique full word have count/mean `N`; its falling factorial still has the stated small relative error. The factor `K+1` is essential here.

5. `bonferroni` is the finite real sum over `Finset.Icc 2 m`, with natural subtraction in `(r-1 : ℕ)`. `bonferroniRemainder` and `poissonRemainder` likewise use `(m-1 : ℕ)`. Under the declared lower bounds these coincide with the source coefficients. The sandwich is quantified over all `n : ℕ`; it cannot be limited to `n≤m`. The product target includes both the nonnegative lower bound and the complete `D(X)+D(Y)+D(X)D(Y)` upper bound. The rare target correctly uses coefficient `1/3` on the third falling factorial.

6. `CentralComparison` and `CentralComparisonOne` quantify over `(Ω : Type) [Fintype Ω] (P : PMF Ω)`, with natural-valued observables. This is a deliberate finite-space specialization of the source's general random-variable statement and covers every canonical matrix/residual model in this package. No extra `Nonempty Ω` assumption is needed: a PMF already provides nonempty support. Two-variable moment premises cover every pair of natural orders with `r+s≤2*m`, including orders 0 and `(m,m)`. They do not merely cover each marginal through order `m`. All constants and `f,d_m` match the manuscript exactly; `0≤ε≤1`, positive means, evenness, and `m≥2` are explicit.

7. A proof of the Poisson benchmark cannot instantiate the finite-space central-comparison target with `Ω=ℕ` or `ℕ×ℕ`. Use separate infinite-sum/measure arguments or a direct analytic polynomial benchmark. This is a proof-representation issue, not a reason to alter the frozen finite target.

## Residual representation audit

`RowPrescription N k K b` contains only a row map and full words. Row injectivity and positive probability of `prescriptionEvent p` are separate premises, as required. No injectivity of `p.word` is assumed: several prescribed rows may carry the same full word.

`ResidualJointFactorial` explicitly uses `b<N`, `R≤N-b`, and conditional expectation divided by the positive prescription probability. Its observable is

```text
∏ i, falling (wordCount (w i) ω - #{q | p.word q = w i}) (r i).
```

On the conditioning event, the prescribed rows really contribute exactly the subtracted count. Prove that inclusion before converting the natural subtraction to an identity; a cast of natural subtraction outside its valid order range is not an acceptable shortcut. The right-hand side uses residual digit counts `cuts.count j a - usedCount p j a`, population `N-b`, and one residual falling-factorial denominator per column. Positive prescription probability implies `usedCount p j a≤cuts.count j a`; injectivity implies the total removed population is `b`.

The two quantitative residual targets quantify `b0` before `D,N0`, require `b0<N0` and `2≤N0`, and are uniform over every `b≤b0`, admissible prescription, word family, and column data. The requested pile bound is on the original counts only. Prove `usedCount≤b`, then obtain a lower bound such as `(c/2)(N-b)` for the selected residual counts once `N` is large enough. This does not require the prescribed words themselves to select large piles: only their positive-probability admissibility is needed.

`residualWordMean` is currently a numerical expression. A lane helper should identify it with the conditional expected deleted-row count, using the residual exact theorem at order 1. This identity is a proved output, not a permissible hypothesis of the residual estimates.

The residual order cutoff is **`R≤N^(1/5)`**, while the population is `N-b`. Therefore direct application of the original theorem with population `N-b` does not discharge the cutoff premise. Prove the quantitative factorial-ratio estimate at the numerical level with an explicit smallness condition (for example `R≤M/2` and `(K+1)R²/M` bounded), or carry a fixed multiplicative factor in the `M^(1/5)` range. For fixed `b0`, `N` and `N-b` are uniformly comparable. This resolves the mismatch without any contract change. Similarly, the depth bound is `C log N`, not initially `C log(N-b)`.

The mean comparison contains the explicit factor `b`, so the case `b=0` requires exact equality. The case `K=0` reduces to comparing `N-b` and `N`, and is covered by choosing `D≥1`.

## Viable proof paths and pinned APIs

### Exact moments without an LB-02 dependency

Use the request type `Σ i : Fin d, Fin (r i)`; its cardinality is `R`. A factorial-product expansion can be represented as embeddings from each requested block into its occupancy fiber. Distinct full words make these occupancy fibers disjoint, giving an equivalence with globally injective labelled-row requests satisfying the assigned words. Pinned mathlib provides

```text
Fintype.card_embedding_eq
  : Fintype.card (α ↪ β) =
      (Fintype.card β).descFactorial (Fintype.card α)
```

in `Mathlib.Data.Fintype.CardEmbedding`, plus `Fintype.card_sigma`, `Fintype.card_pi`, finite sum/product interchange, and standard subtype/cardinality equivalences. This avoids an ad hoc induction on the whole multivariate moment.

For one column, establish invariance of uniform assignments under a row permutation. Double count pairs consisting of a column assignment and an embedding of the request set into row labels. Exchangeability makes the probability independent of the embedding; on each fixed assignment, the number of successful embeddings is the product of descending factorials of its digit-fiber cardinalities. Dividing by the number of all embeddings gives the exact one-column formula. The actual product sample law then factors its expectation by `Fintype.prod_sum`/`Fintype.card_pi`. These elementary facts can be proved locally using the canonical uniform average, so LB-03 does not require LB-01 or LB-02 proofs.

For residual moments the same double counting can be done on the prescription event with embeddings into unprescribed rows, or with an explicit equivalence of conditioned columns and residual fixed-count assignments. Both prove the concrete conditional law directly. The existing `RiffleLowerV2.Thinning.residualConditionalExpect` documents a usable mathematical transport construction, but **importing it would add an LB-02 dependency forbidden by the assigned LB-03 dependency contract**. Reusing the idea requires an independently checked, provenance-documented lane implementation or a reviewed additive shared adapter from LB-00.

### Quantitative ratios

The key numeric helper should prove positivity and control of `log((n)_v/n^v)` under explicit finite hypotheses. Relevant pinned declarations are `Nat.descFactorial_eq_prod_range`, `Nat.descFactorial_pos`, `Real.log_le_sub_one_of_pos`, `Real.log_inv`, and logarithm/product rules. Applying the log inequality also to the reciprocal of `1-h/n` bounds `-log(1-h/n)` by `2h/n` when `h/n≤1/2`. Sum over requests, using `∑a requestedCount=R` and `∑a requestedCount²≤R²`, then exponentiate after establishing a uniform small exponent. Prove all claims about natural differences before casting them to real differences.

An important zero issue: unrequested digit piles may be zero. Logarithms of these piles must never be introduced. Split off `requestedCount=0`, whose falling-factorial and power factors are 1; positive requests force membership in a selected word's positive pile.

### Bonferroni and central comparison

Pinned `Mathlib.Data.Nat.Choose.Sum` provides `Int.alternating_sum_range_choose_eq_choose` for partial alternating binomial sums, and `Int.alternating_sum_range_choose` for the full sum. Weighted sums follow from the adjacent-binomial identity for `r * choose(n,r)`. Prove the finite identity in integers or reals before applying sign/parity arguments, with separate `n=0,1`, `n≤m`, and `n>m` cases. The source's explicit positive remainder is a suitable target. `Nat.descFactorial_eq_factorial_mul_choose` supplies the exact bridge between binomial expectations and factorial moments.

For the central comparison, first prove a scalar benchmark for the polynomial

```text
B_m(t) = ∑ r∈Icc 2 m, (-1)^r * (r-1) * t^r / r!
```

against `poissonCollision t`, with error between 0 and `poissonRemainder m t`. This can be obtained by integrating the pointwise Bonferroni bounds against explicitly normalized Poisson weights, or by a separately proved analytic remainder identity. The series route may use the pinned exponential-series `HasSum` APIs; it must prove summability before interchanging sums. It does not require the central theorem itself on an infinite probability space.

The expectation of the product error uses the `(m,0)`, `(0,m)`, and `(m,m)` premises and is bounded by `(1+ε)(d_m(μ)+d_m(ν)+d_m(μ)d_m(ν))`. Compare the finite polynomial expectation to `B_m(μ)B_m(ν)` term by term using the remaining mixed moments, then add the scalar benchmark product remainder. The factor 3 is `1+ε+1≤3`. This accounts for large-count outcomes through polynomial moments exactly as required. No estimate of the probability of a large-count event can replace this step.

## Import compatibility and implementation boundary

The historical `lean-lower-bound` package uses Lean 4.19.0 and its own `RiffleLower.FiniteLaw` representation. Its `wordCount_expect`, `wordCount_factorial_second_moment`, and permutation symmetry ideas are useful references, but there is no arbitrary mixed-moment theorem there. Its cached artifacts cannot be imported into the Lean 4.33.1 integration package. Any needed source port belongs in the owned `RiffleLowerV2/Factorial/Compat/` tree with provenance and a checked bridge to the canonical PMF law.

The canonical `formalization/time_profile` package matches Lean 4.33.1 and is already rebuilt by the coordinator from source. The package's actual pinned mathlib source root is `formalization/.lake/packages/mathlib`, not `formalization/lower_bound_v2/.lake/packages/mathlib`. The lane build command must remain `python3 scripts/lane.py LB03 RiffleLowerV2.Factorial.Main` from the integration package. If a newly selected mathlib import has no registered compiled module in the coordinator overlay, request that dependency build from LB-00; do not change shared caches or use old oleans.

No required frozen statement change was identified. New combinatorial, numerical, expectation-linearity, and residual-mean-identification helpers may remain in the lane. All ten required exports are still proof obligations at this review stage.
