# Proposed shared Lean interface (before freeze)

Owner: lean_design. All declarations below belong to namespace `TimeProfile` in `TimeProfile/Base.lean`. This is a Markdown interface proposal, not Lean source. Mathematical statements are F01–F04 and F06–F08 of the contract; simple definitional projections merely expose the frozen structures.

## Types and definitions exported by Base

| Name | Parameters / mathematical definition |
|---|---|
| `Simplex k` | Abbreviation for the subtype `stdSimplex ℝ (Fin k)`. |
| `prob p l` | Real coordinate `p.val l`; arguments p:Simplex k, l:Fin k. |
| `pileMax p` | Real coercion of the finite supremum in ℝ≥0 of the simplex coordinates; empty sup is zero. |
| `digitCost z` | `Real.log (1/z)`. |
| `maxCost p` | `digitCost (pileMax p)`; source a_p. |
| `powerSum p theta` | Sum over l:Fin k of `(prob p l) ^ theta` using real powers. |
| `psi p theta` | `-Real.log (powerSum p theta)`. |
| `Cuts k N K` | Structure fields `count : Fin K → Fin k → ℕ`, `sum_count : ∀j, ∑l,count j l=N`. |
| `Cuts.profile cuts hN j` | Simplex point with coordinate `cuts.count j l / N`; hN:0<N. |
| `logScale N` | `Real.log (N:ℝ)`. |
| `columnTime N j` | `((j.val:ℝ)+1)/logScale N`, for j:Fin K. |
| `horizonDepth N T` | `Nat.floor (T*logScale N)`. |
| `BorelPartition k` | Structure fields `cellCount : ℕ`, `classify : Simplex k → Fin cellCount`, `measurable_classify`, `rep : Fin cellCount → Simplex k`, `classify_rep : ∀i,classify(rep i)=i`. |
| `BorelPartition.cell P i` | Fiber `{p | P.classify p=i}`. |
| `BorelPartition.IsRegular P chi C` | Prop structure with the four exact source conditions. Field names `psi_oscillation`, `maxCost_oscillation`, `good_digit`, `exceptional_digit`. Each quantifies over p,p' in one classifier fiber, or p and its fiber representative, as appropriate. No positivity of every coordinate. |
| `BorelPartition.IsGoodDigit P chi p l` | `2*chi < prob (P.rep (P.classify p)) l`. |
| `TimeMesh T` | Structure fields `cellCount : ℕ`, `cellCount_pos : 0<cellCount`, `boundary : Fin(cellCount+1)→ℝ`, `strictMono_boundary`, `boundary_zero : boundary 0=0`, `boundary_last : boundary (Fin.last cellCount)=T`. |
| `TimeMesh.cell mesh q` | Ico between boundary(q.castSucc),boundary(q.succ), except q.val+1=cellCount uses Icc. |
| `TimeMesh.MeshLE mesh Delta` | Every successive boundary difference≤Delta. |
| `TimeMesh.cellIndex mesh t ht` | Unique cell index from F06, with ht:t∈Icc 0 T. |
| `TimeLaw k` | Arbitrary function ℝ→MeasureTheory.ProbabilityMeasure(Simplex k). No measurability field. |
| `profileMaxCost mu t` | Integral of maxCost under mu t. |
| `profilePsi mu t theta` | Integral of psi(·,theta) under mu t. |
| `integratedMaxCost mu r s` | Interval integral of profileMaxCost from r to s. |
| `integratedPsi mu theta r s` | Interval integral of profilePsi(·,theta) from r to s. |
| `cellMass mu P i t` | Real value of `(mu t)(P.cell i)`. |
| `intervalCount cuts hN N P a b i` | Number of j:Fin K with a≤columnTime N j≤b and P.classify(cuts.profile hN j)=i. The redundant N may be implicit from cuts. |
| `AlmostLike cuts hN mu P T rho phi` | Literal source closed positive-length rho-grid definition, including 0≤a, a<b=min(a+rho,T)≤T and a∈rhoℤ, with discrepancy≤phi*(b-a)+1/logScale N. |
| `GoodColumn p chi` | There exist distinct l,m with chi≤prob p l and chi≤prob p m. |
| `LocalGood cuts hN chi gamma rho r T` | Every interval [a,a+rho]⊆[r,T] contains at least gamma*rho*logScale N good column indices, counted as a real. |

The profile definition containing the time integral J still needs the parent to freeze the source's tilted-weight, I, and H definitions explicitly. If accepted, Base will add `tiltedWeight`, `tiltedCost`, `shannonEntropy`, `tiltedEntropy`, `profileTiltedCost`, `profileTiltedEntropy`, and `integratedTiltedCost`; no theorem about them is added in this finite tranche.

## Theorem exports

| Contract ID | Export names |
|---|---|
| F01 | `prob_nonneg`, `prob_le_one`, `sum_prob` |
| F02 | `exists_prob_pos`, `prob_le_pileMax`, `pileMax_nonneg`, `pileMax_pos`, `pileMax_le_one`, `inv_card_le_pileMax` |
| F03 | `Cuts.profile_prob`, `Cuts.profile_pos_iff` (normalization membership is proved in `Cuts.profile` itself) |
| F04 | `logScale_pos`, `horizonDepth_error`, `horizonDepth_zero` |
| F06 | `TimeMesh.existsUnique_mem_cell`, `TimeMesh.cellIndex_mem`, `TimeMesh.cells_disjoint`, `TimeMesh.column_cellIndex_mem` |
| F07 | `BorelPartition.IsRegular.good_prob_pos`, `BorelPartition.IsRegular.good_actual_gt`, `BorelPartition.IsRegular.good_digitCost_error` |
| F08 | `BorelPartition.IsRegular.exceptional_actual_le`, `BorelPartition.IsRegular.maxCost_rep_error`, `BorelPartition.IsRegular.psi_rep_error` |

`TimeMesh.existsUnique_mem_cell` includes the t∈[0,T] assumption. `TimeMesh.column_cellIndex_mem` takes the explicit bound `0<columnTime N j ∧ columnTime N j≤T`; it does not silently assume the desired depth relation. `Cuts.profile_pos_iff` uses only hN:0<N. Digit-log nonnegativity may be exposed as the pointwise F01 consequence `digitCost_nonneg (hz:0≤z) (hz1:z≤1)`; at z=0 the totalized real logarithm equals zero, and identities still use strict positivity separately.

## Other owners

`TimeProfile/Analysis.lean` imports Base and exports the F05 real bounds, F09 regular partition existence with C=1, and E01 Gibbs inequality. Suggested names: `maxCost_bounds`, `powerSum_pos`, `powerSum_le_one`, `psi_bounds`, `exists_regular_partition`, `finite_gibbs`.

Root-owned ambient/digit files import Base (and Analysis only where F05/E01 are needed). Root defines words, positions, finite side masses, cL/cE/cF, digit counts, S/Q/R/H, and the margin/source predicates. Numeric algebra can remain independent of Base except for eventual source instantiation.

No agent changes another owner's structure/definition after freeze. Any missing interface projection that is only a definitional restatement can be communicated and added by its owner; a new mathematical assumption or theorem statement requires another explicit contract comparison, not an opportunistic proof edit.
