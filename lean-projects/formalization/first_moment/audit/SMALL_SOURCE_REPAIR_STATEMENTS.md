# Small source exponent repair: exact supplementary statement candidate

Status: DESIGN ONLY. No Lean implementation or new freeze. This proposal has **zero definitions and four exported theorems**. All existing statements remain immutable.

Proposed module: `FirstMomentModel/SmallSourceRepair.lean`. Proposed namespace: `InhomogeneousShuffle.FirstMoment.Model`, with `open TimeProfile Set`, importing `RiffleTimeProfile.SourceNumerical`. The names below therefore belong to our supplemental namespace; all existing numerical, source, and profile names resolve to `TimeProfile`.

I compared both `SMALL_SOURCE_REPAIR_ALGEBRA.md` and `SMALL_SOURCE_REPAIR_INEQUALITIES.md` with the actual `Numerical`, `Source`, `SourceNumerical`, `Digits`, `IntegratedBounds`, and `AnalyticParameters` Lean sources and the authorized article's first-moment margin, profile estimates, numerical lemma, and first-moment proof. The four statements below implement the common conclusion of those audits. They do not assert a probability-law identification or a large-block density estimate.

## Scope and shared-parameter decision

The valid coarse small-block density estimate needs `H + 2*E + 8*delta + 4*eb`. Its numerical repair uses N1 and the **derived** source fact `0 ≤ profileS`. The original source small theorem remains valid and unchanged, but its conclusion containing `-F` is not used to erase that term.

The new uniform theorem must co-produce every conclusion of `TimeProfile.exists_uniform_source_margins` and the new repaired conclusion using **one** regular partition and one family of thresholds. Applying two existential uniform theorems independently would not identify their partitions. The proof should replay `exists_source_parameter_thresholds` once, choose `P` once with `exists_regular_partition`, retain the fine budgets, and prove all four conclusions. The second branch uses one real F for its large, original small, and repaired small implications. Equality of their `WithBot` representations identifies the independently obtained real witnesses.

This is a finite source-numerical supplement. It uses the literal `Cuts k N (horizonDepth N T)` model and the same `AlmostLike`, ambient approximation, legal prefix, crossing, profile cutoff and margin assumptions as the existing source theorem. A separate actual-list-word adapter may instantiate its `ParentCrossing` premise from proper Gamma. No Gamma membership, small-block size condition, density law equality, or additional fluctuation premise is silently inferred here.

## SR1: separated-error pointwise scalar inequality

All displayed scalar binders are implicit except their explicit proof premises, matching the existing scalar style. No sign is imposed on `Lv`, `F`, `E`, `H`, `beta`, `Dtail`, or values of `B`.

```lean
theorem small_coarse_numerical_core
    {Lv F E H S beta Dtail theta eBeta eF eS eH eE : ℝ}
    {B : ℝ → ℝ}
    (htheta : theta ∈ Icc (3 : ℝ) 4)
    (heBeta : 0 ≤ eBeta) (heF : 0 ≤ eF) (heS : 0 ≤ eS)
    (heH : 0 ≤ eH) (heE : 0 ≤ eE)
    (hS : 0 ≤ S)
    (hparent : S ≤ Lv - F + eS)
    (hfluc : Lv / 2 - eF ≤ F)
    (hmax : Lv ≤ beta + eBeta)
    (hentropy : H ≤ theta * S - B theta + eH)
    (htail : E ≤ -Dtail + eE) :
    H + 2 * E ≤ largeObjective beta B Dtail theta +
      ((7 / 2 : ℝ) * eBeta + 7 * eF + 7 * eS + eH + 2 * eE)
```

The new generic scalar premise `hS` is proved from source definitions in SR3; it is not added to the model interface. The five scalar error signs are exactly the independently reviewed separated-error interface, even where their nonnegativity is stronger than a proof step needs.

## SR2: optimization over the literal N1 infimum

There is no free theta binder or membership premise. Entropy holds for every theta in the existing closed interval.

```lean
theorem small_coarse_numerical_infimum
    {Lv F E H S beta Dtail eBeta eF eS eH eE : ℝ}
    {B : ℝ → ℝ}
    (heBeta : 0 ≤ eBeta) (heF : 0 ≤ eF) (heS : 0 ≤ eS)
    (heH : 0 ≤ eH) (heE : 0 ≤ eE)
    (hS : 0 ≤ S)
    (hparent : S ≤ Lv - F + eS)
    (hfluc : Lv / 2 - eF ≤ F)
    (hmax : Lv ≤ beta + eBeta)
    (hentropy : ∀ theta ∈ Icc (3 : ℝ) 4,
      H ≤ theta * S - B theta + eH)
    (htail : E ≤ -Dtail + eE) :
    H + 2 * E ≤
      sInf (largeObjective beta B Dtail '' Icc (3 : ℝ) 4) +
        ((7 / 2 : ℝ) * eBeta + 7 * eF + 7 * eS + eH + 2 * eE)
```

The exact trusted input is `TimeProfile.numerical_le_infimum_add`. Its pointwise lower bound provides the required bounded-below image; no optimizer, continuity, compact-image premise, or separate boundedness hypothesis is allowed.

## SR3: actual finite source margin with explicit loss budget

The initial binders and scientific assumptions are the same as `TimeProfile.source_small_margin`. Its explicit finite error budget is replaced by the newly stated budget for the newly stated exponent; the old theorem itself is untouched. `C` is the regular-partition error constant here, not the boundary-admissibility constant of a `Riffle.Setup`.

```lean
theorem source_small_coarse_margin
    {k N R : ℕ} {T rho phi chi C r b er eb eta alpha delta : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C)
    (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T) (her : 0 ≤ er) (heb : 0 ≤ eb)
    (heta : 0 < eta) (halpha : 0 ≤ alpha) (hdelta : 0 ≤ delta)
    (hFM : FirstMomentMargin mu r b T eta)
    (x : Fin (horizonDepth N T) → Fin k)
    (timeClass : Fin (horizonDepth N T) → Fin R)
    {w v n : ℕ} (hwv : w ≤ v) (hvn : v ≤ n) (hnK : n ≤ horizonDepth N T)
    (hlegal : LegalPrefix (cuts.profile (by omega)) x n)
    (hambient : AmbientApproximation N (cuts.profile (by omega)) x w r b er eb)
    (hR : profileR N (cuts.profile (by omega)) x P chi v n ≤ alpha)
    (hcross : Crossings (cuts.profile (by omega)) x w v chi)
    (hbudget :
      let A := 4 * Real.log (k : ℝ)
      let Qerr := quadratureError N T rho phi P.cellCount A (C * chi)
      (7 / 2 : ℝ) * (Qerr + A * (er + 1 / logScale N)) +
        7 * ((eb + Real.log (1 / chi) / logScale N) / 2) +
        7 * (C * chi * T + Real.log (1 / chi) / logScale N) +
        (Qerr + A * alpha) + 2 * Qerr + 8 * delta + 4 * eb ≤ 3 * eta / 4) :
    ∃ F : ℝ, cF N (cuts.profile (by omega)) x w v = (F : WithBot ℝ) ∧
      (ParentCrossing N (cuts.profile (by omega)) x b w v n F delta →
        profileH N (cuts.profile (by omega)) x P timeClass chi v n +
          2 * cE N (cuts.profile (by omega)) n + 8 * delta + 4 * eb ≤ -eta / 4)
```

The finite expression contains `4*eb`, not the signed ambient discrepancy and not zero. A later density adapter will use the existing absolute ambient approximation to dominate that discrepancy by eb. SR3 itself makes no claim equating an EdgeLocalization quantity with a TimeProfile quantity.

## SR4: the same ordered parameter construction with all margins

This statement keeps **exactly** the original initial scientific assumptions and `epsilon ≤ eta/28`. It retains the old singleton, large, small, and fallback conclusions. Only the extra repaired implication is appended inside the common-F branch. The fallback branch still requires `0 < delta`, independently of the middle branch's `delta ∈ Icc 0 epsilon`.

```lean
theorem exists_uniform_source_margins_with_small_coarse
    {k : ℕ} (hk : 2 ≤ k)
    {T eta epsilon : ℝ} (hT : 0 ≤ T) (heta : 0 < eta)
    (hepsilon : 0 < epsilon) (hchoice : epsilon ≤ eta / 28) :
    ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 ≤ 1 / (k : ℝ) ∧
      ∀ chi : ℝ, 0 < chi → chi < chi0 →
        ∃ P : BorelPartition k, P.IsRegular chi 1 ∧
          ∃ rho0 : ℝ, 0 < rho0 ∧
            ∀ rho : ℝ, 0 < rho → rho < rho0 →
              ∃ phi0 : ℝ, 0 < phi0 ∧
                ∀ phi : ℝ, 0 ≤ phi → phi ≤ phi0 →
                  ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
                    ∀ N : ℕ, ∀ hNN : N0 ≤ N,
                      ∀ (cuts : Cuts k N (horizonDepth N T)) (mu : TimeLaw k),
                        AlmostLike cuts (by omega) mu P T rho phi →
                        ∀ r b : ℝ, 0 ≤ r → r ≤ T → FirstMomentMargin mu r b T eta →
                          (∀ er : ℝ, 0 ≤ er → (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4 →
                            ∀ (x : Fin (horizonDepth N T) → Fin k) (w v : ℕ),
                              w ≤ v → v ≤ horizonDepth N T →
                              LegalPrefix (cuts.profile (by omega)) x v →
                              |(w : ℝ) / logScale N - r| ≤ er →
                              cL N (cuts.profile (by omega)) x b w v +
                                cE N (cuts.profile (by omega)) v ≤ -eta / 2) ∧
                          (∀ er eb delta : ℝ, 0 ≤ er → 0 ≤ eb →
                            (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4 → eb ≤ epsilon →
                            delta ∈ Icc (0 : ℝ) epsilon →
                            ∀ (R : ℕ) (timeClass : Fin (horizonDepth N T) → Fin R)
                              (x : Fin (horizonDepth N T) → Fin k) (w v n : ℕ),
                              w ≤ v → v ≤ n → n ≤ horizonDepth N T →
                              LegalPrefix (cuts.profile (by omega)) x n →
                              AmbientApproximation N (cuts.profile (by omega)) x w r b er eb →
                              profileR N (cuts.profile (by omega)) x P chi v n ≤
                                exceptionalAllowance chi →
                              Crossings (cuts.profile (by omega)) x w v chi →
                              ∃ F : ℝ, cF N (cuts.profile (by omega)) x w v = (F : WithBot ℝ) ∧
                                (StableAt N (cuts.profile (by omega)) x b w n F delta →
                                  4 * cL N (cuts.profile (by omega)) x b w n - F +
                                    2 * cE N (cuts.profile (by omega)) n +
                                    profileH N (cuts.profile (by omega)) x P timeClass chi v n ≤
                                      -eta / 2) ∧
                                (ParentCrossing N (cuts.profile (by omega)) x b w v n F delta →
                                  -F + 2 * cE N (cuts.profile (by omega)) n +
                                    profileH N (cuts.profile (by omega)) x P timeClass chi v n ≤
                                      -eta / 2) ∧
                                (ParentCrossing N (cuts.profile (by omega)) x b w v n F delta →
                                  profileH N (cuts.profile (by omega)) x P timeClass chi v n +
                                    2 * cE N (cuts.profile (by omega)) n +
                                    8 * delta + 4 * eb ≤ -eta / 4)) ∧
                          (∀ er eb delta : ℝ, 0 ≤ er → 0 ≤ eb →
                            (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4 → eb ≤ epsilon →
                            0 < delta →
                            ∀ (x : Fin (horizonDepth N T) → Fin k) (w v : ℕ),
                              w ≤ v → v ≤ horizonDepth N T →
                              LegalPrefix (cuts.profile (by omega)) x (horizonDepth N T) →
                              AmbientApproximation N (cuts.profile (by omega)) x w r b er eb →
                              Crossings (cuts.profile (by omega)) x w v chi →
                              ∃ F : ℝ, cF N (cuts.profile (by omega)) x w v = (F : WithBot ℝ) ∧
                                cL N (cuts.profile (by omega)) x b w (horizonDepth N T) - F <
                                  delta)
```

In particular, the existential proof binder `hN0` and subsequent `hNN` precede every `(by omega)` proof of `0 < N`, exactly as in the compiled original theorem. The map dimension `R`, timeClass, source cut array, law, ambient data, and word are universally quantified after N0. No time measurability assumption is introduced.

## Exhaustive proof-local schemas to review

These are proof facts only, with all premises either the printed scalar premises or facts available inside the original parameter construction. They are not new scientific assumptions or new exported declarations.

### 1. Scalar rearrangement

For SR1, put `a := eBeta/2 + eF + eS`. The given parent, fluctuation and maximal bounds imply `S ≤ beta/2 + a`, and error nonnegativity gives `0 ≤ a`. Since `0 ≤ S` and `theta ∈ [3,4]`,

```text
theta*S ≤ (theta+3)*S
        ≤ ((theta+3)/2)*beta + (theta+3)*a
        ≤ ((theta+3)/2)*beta + 7*a.
```

Adding the entropy and twice the tail inequality gives the literal SR1 loss. SR2 applies `TimeProfile.numerical_le_infimum_add`. No sign of beta is used.

### 2. Source-error signs and ordered endpoints

For SR3's printed source data, derive `0 ≤ 4*log k`, `0 < logScale N`, `0 ≤ log(1/chi)`, and the five nonnegative errors appearing in its budget. `quadratureError_nonneg` supplies the quadrature sign. These are the same calculations as the existing private `source_errors_nonneg`; because that declaration is private, the supplementary proof may rederive them locally, not presume a new public input.

The same applies to the existing private time-order facts. From `m ≤ horizonDepth N T`, `hN`, and `hT`, natural-floor comparison gives `m/logScale N ≤ T`. With `v ≤ n`, this proves

```text
r ≤ max r (v/logScale N)
  ≤ max r (n/logScale N)
  ≤ T.
```

These are the exact endpoints passed to `hFM.2.1`; its **first projection** gives N1. The definition `TimeProfile.firstMargin` is definitionally the `largeObjective` image infimum in SR2. Neither endpoint is replaced by T.

### 3. Actual source substitution and derived nonnegativity

Use the proved facts:

- `TimeProfile.profileS_nonneg` at the legal word and regular partition gives `0 ≤ S`.
- `TimeProfile.profile_parent_crossing_horizon` gives `S ≤ Lv - F + eS` when the displayed ParentCrossing implication is entered.
- `TimeProfile.cF_lower_bound_of_crossings`, used at `M = v`, gives finite F, its exact `cF` representation, and `Lv/2 - eF ≤ F`. Legality at v is derived from legality at n and `v ≤ n`.
- `TimeProfile.source_prefix_max_bound`, `source_entropy_bound`, and `source_tail_bound` give the remaining comparisons. For entropy, replace `profileR` by alpha using its stated upper bound and `0 ≤ 4*log k`.

The exact substitutions are

```text
Lv    = cL N p x b w v
S     = profileS N p x P timeClass chi v n
H     = profileH N p x P timeClass chi v n
E     = cE N p n
beta  = localBeta mu r b (max r (v/logScale N))
B θ   = integratedPsi mu θ (max r (v/logScale N)) (max r (n/logScale N))
Dtail = integratedPsi mu 2 (max r (n/logScale N)) T

eBeta = Qerr + (4*log k)*(er + 1/logScale N)
eF    = (eb + log(1/chi)/logScale N)/2
eS    = C*chi*T + log(1/chi)/logScale N
eH    = Qerr + (4*log k)*alpha
eE    = Qerr,
```

where `p = cuts.profile (by omega)` and Qerr is exactly SR3's budget let-expression. SR2 plus N1 gives `H + 2*E ≤ -eta + repairLoss`; the stated finite budget gives SR3 by linear arithmetic. No additional profile nonnegativity premise survives into SR3.

### 4. Fine budget statement, with all original premises

The allowed proof-local fine-budget schema has the following exact binders and premises. Here m is the already chosen partition's cell count when applied; there is no new condition on its growth.

```lean
{k N m : ℕ} {T chi rho phi er eb delta epsilon eta : ℝ}
(hk : 2 ≤ k) (hN : 2 ≤ N) (hT : 0 ≤ T)
(hchi : 0 < chi) (hchiK : chi < 1 / (k : ℝ))
(hrho : 0 < rho) (hphi : 0 ≤ phi) (her : 0 ≤ er) (heb : 0 ≤ eb)
(hepsilon : 0 < epsilon) (heta : 0 < eta)
(hdelta : delta ∈ Icc (0 : ℝ) epsilon)
(hchoice : epsilon ≤ eta / 28)
(hchiBudget : chi * T ≤ epsilon / 16)
(hbadBudget : (4 * Real.log (k : ℝ)) * exceptionalAllowance chi ≤ epsilon / 4)
(hrhoBudget : 2 * (4 * Real.log (k : ℝ)) * rho ≤ epsilon / 16)
(hphiBudget : (4 * Real.log (k : ℝ)) * m * phi * T ≤ epsilon / 16)
(herBudget : (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4)
(hebBudget : eb ≤ epsilon)
(hNbudget :
  ((chi + (4 * Real.log (k : ℝ)) + 2 * (4 * Real.log (k : ℝ)) * m) *
    (⌊T / rho⌋₊ + 1 : ℕ) + (4 * Real.log (k : ℝ)) + Real.log (1 / chi)) /
      logScale N ≤ epsilon / 16)
```

Its conclusion is the following conjunction, using lets local to that proposition:

```lean
let A := 4 * Real.log (k : ℝ)
let Qerr := quadratureError N T rho phi m A chi
let qchi := Real.log (1 / chi) / logScale N
(Qerr ∈ Icc (0 : ℝ) (5 * epsilon / 16)) ∧
(chi * T + qchi ∈ Icc (0 : ℝ) (epsilon / 8)) ∧
((eb + qchi) / 2 ∈ Icc (0 : ℝ) (17 * epsilon / 32)) ∧
(Qerr + A * (er + 1 / logScale N) ∈ Icc (0 : ℝ) (5 * epsilon / 8)) ∧
(Qerr + A * exceptionalAllowance chi ∈ Icc (0 : ℝ) (9 * epsilon / 16)) ∧
((7 / 2 : ℝ) * (Qerr + A * (er + 1 / logScale N)) +
  7 * ((eb + qchi) / 2) + 7 * (chi * T + qchi) +
  (Qerr + A * exceptionalAllowance chi) + 2 * Qerr + 8 * delta + 4 * eb ≤
    3 * eta / 4)
```

To prove it, split hNbudget into the sum of three nonnegative terms

```text
qRound + A/logScale N + qchi ≤ epsilon/16,
qRound = (chi + A + 2*A*m)*(floor(T/rho)+1)/logScale N.
```

Bound each term by epsilon/16. The exact quadrature definition then gives `Qerr ≤ 5*epsilon/16`. The remaining five-term envelope is obtained by finite distributivity and linear arithmetic, preserving the original chi, rho, phi, er, eb and N budgets. The scalar repair loss is at most `(255/32)*epsilon`; adding `8*delta+4*eb` gives at most `(639/32)*epsilon`. Since `epsilon ≤ eta/28` and eta is positive, this is at most `3*eta/4`. The resulting exponent is actually at most `-(257/896)*eta`, which implies the proposed `-eta/4` conclusion. No eta/65 restriction or smaller parameter choice is needed.

It is also allowed to retain the shared rounding budget during the arithmetic, but the implementation need only prove the displayed weaker bounds. This schema applies to regularity constant one, exactly the partition selected in SR4; for arbitrary C in SR3 the explicit C-dependent budget remains visible.

### 5. One parameter choice and preservation of old branches

Call `TimeProfile.exists_source_parameter_thresholds hk hT hepsilon` once. Its chi bounds give `hchiBudget` and `hbadBudget`. Choose `P` once by `TimeProfile.exists_regular_partition hk hchi hchiK`, then pass that fixed `P.cellCount` to the returned mesh construction. It supplies the same rho, phi and N thresholds and the exact remaining budgets listed in schema 4.

For each later finite N and ambient data, the already proved `source_error_bounds` and `numerical_budgets_of_common_bounds` still give the four old numerical budgets. Schema 4 separately gives the repaired budget; it is not inferred from the old coarse common-error summary. Apply `source_singleton_margin`, `source_large_margin`, `source_small_margin`, `source_no_terminal_fallback`, and SR3 at that same P and those same finite data. Preserve the original fallback delta premise and the old singleton's absence of ambient mass or crossing premises. Identify the three finite-F witnesses through their equal cF values.

This construction does not need to compare or merge two independently chosen partitions. It uses the existing quantified parameter theorem without strengthening any tolerance. If a future varying ambient family supplies uniformly vanishing er and eb, `TimeProfile.uniformly_vanishing_ambient_budgets` can be applied afterward and its threshold combined with N0. No such family is introduced into the four proposed interfaces.

## Remaining integration boundaries

The actual proper-Gamma list branch still requires the already identified structural adapters and the original horizon equality; terminal fallback and root singleton are different branches. SR4 co-produces their existing numerical tools but makes no stochastic claim about them. For the coarse density theorem, the EdgeLocalization prefix, ambient-size, tail-exponent and ambient-mean definitions must still be proved equal to the corresponding source quantities, and any graph-law identification must be proved separately. No such equality is a premise or conclusion here.

The source interface retains the existing full `AlmostLike` premise. Instantiating it from a tail-local version in the article is a separate obligation, not a stronger assumption silently added to the paper. Profile-counting and localization losses also retain their own reserves; the repaired eta/4 class margin does not automatically pay for them. Large-block density remains unresolved by this batch.

This candidate is ready for exact independent algebra and adversarial review before any freeze or implementation. No earlier source or contract has been edited.
