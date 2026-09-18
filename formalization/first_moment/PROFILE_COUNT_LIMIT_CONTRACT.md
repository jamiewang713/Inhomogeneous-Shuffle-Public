# Actual profile-class count with ordered source parameters: frozen supplemental contract

Status: FROZEN at 2026-09-17T22:31:25.152925+00:00, after three independent exact-interface approvals of the identical candidate. No implementation existed at freeze. This supplement preserves every earlier assumption, definition and theorem statement. Mathematical sources remain the three authorized files. The source fixes the boundary constant before chi, a finite partition/time dimension after chi, and then N; this contract proves that order for the existing actual refined encoder.

Implementation file: `FirstMomentModel/ProfileCountLimit.lean` in namespace `InhomogeneousShuffle.FirstMoment.Model`, using the common Lean 4.33 runtime. There are no new definitions and three frozen exported results. The existing definitions `profileCountBound`, `boundaryBudget`, `exceptionalBudget`, `ProfileClass`, and `TimeProfile.exceptionalAllowance` remain unchanged. The latter is exactly `1 / sqrt(log(1/chi))`.

## CL1: uniform finite-depth consequence of the frozen exponential count

`profileCount_uniform_eventually` has

```lean
(k d : ℕ) (T a b tb te : ℝ)
(hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
(htb : 0 < tb) (htb1 : tb ≤ 1) (hte : 0 < te) (hte1 : te ≤ 1)
(eps : ℝ) (heps : 0 < eps) :
  ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N K qb qe : ℕ, N0 ≤ N →
    (K : ℝ) ≤ T * Real.log (N : ℝ) →
    (qb : ℝ) ≤ a * Real.log (N : ℝ) →
    (qe : ℝ) ≤ b * Real.log (N : ℝ) →
    (profileCountBound K k qb qe d : ℝ) ≤
      (N : ℝ) ^ (2*a*Real.log (1/tb) + b*Real.log (1/te) +
        (k : ℝ)*T*(2*tb+te) + eps)
```

This is the pointwise-uniform version of the already proved `profileCount_eventually`. A proof must obtain its threshold from the fixed logarithmic polynomial alone and then apply `profileCount_exp_bound` to arbitrary finite K, qb, qe satisfying the three displayed inequalities. It must not assume a threshold uniform over arbitrary sequences merely from separate sequence-dependent thresholds. No bound `qb,qe≤K` is required.

## CL2: chi before dimension before N

`profileCount_small_chi` has

```lean
(k : ℕ) (T C eps : ℝ)
(hk : 2 ≤ k) (hT : 0 ≤ T) (hC : 0 < C) (heps : 0 < eps) :
  ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 < min 1 (1 / (k : ℝ)) ∧
    ∀ chi : ℝ, 0 < chi → chi < chi0 → ∀ d : ℕ,
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N K : ℕ, N0 ≤ N →
        (K : ℝ) ≤ T * Real.log (N : ℝ) →
        (profileCountBound K k
          (Nat.floor ((C / Real.log (1/chi)) * Real.log (N : ℝ)))
          (Nat.floor (TimeProfile.exceptionalAllowance chi * Real.log (N : ℝ)))
          d : ℝ) ≤ (N : ℝ) ^ eps
```

The exact count bound is `4*(k+1)^2*(K+1)^(d+3)*sparseCount(K,k,qb)^2*sparseCount(K,k,qe)`. All boundary and exceptional labels, both boundary factors, and the route factor four remain present. The fixed dimension d may depend on chi, but not on N after choosing N0. No mesh dimension or partition cardinality is assumed uniformly bounded in chi.

## CL3: actual realized class count

`profileClass_small_chi` has exactly the initial fixed parameters and premises `k T C eps hk hT hC heps` of CL2 and concludes

```lean
∃ chi0 : ℝ, 0 < chi0 ∧ chi0 < min 1 (1 / (k : ℝ)) ∧
  ∀ chi : ℝ, 0 < chi → chi < chi0 → ∀ c : ℕ,
    ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ D : Riffle.Model, D.k = k → N0 ≤ D.N →
        (D.K : ℝ) ≤ T * Real.log (D.N : ℝ) →
        ∀ A : Riffle.Setup D, A.C = C → A.chi = chi →
          ∀ (cell : Fin D.K → Fin c) (good : Fin D.K → ℕ → Prop)
            (route : ProfileWord A good (TimeProfile.exceptionalAllowance chi) → Fin 4),
            (Nat.card (ProfileClass A cell good
              (TimeProfile.exceptionalAllowance chi) route) : ℝ) ≤
                (D.N : ℝ) ^ eps
```

The setup equalities bind its existing parameters to the fixed source choices; they do not change the setup or presume new model properties. The class domain retains its actual admissible pair, actual stable word, and real exceptional cutoff. No extra legality, retention, finiteness, source profile regularity, or probabilistic routing premise is added. Fixed c may be the later source time-cell/simplex-cell product. Cell and good maps may otherwise vary with the finite model; the statement only requires their codomain dimension to have been fixed before N0.

## Proof-local schemas to review before freeze

1. For fixed nonnegative T, finite k,d and positive eps, logarithmic-polynomial absorption supplies a single N0 with
   `4*(k+1)^2*(K+1)^(d+3) ≤ N^eps`
   for all N≥N0 and K≤T log N. Derive this from the same standard log-power little-o theorem already used in the frozen `profileCount_eventually`; the comparison `K+1≤(T+1)log N` holds after `log N≥1`.
2. The frozen `profileCount_exp_bound`, nonnegative `log(1/tb)`/`log(1/te)`, and the three finite budget inequalities give the rate in CL1. Convert exp(rate*log N) to the positive-base real power and add the polynomial exponent.
3. For fixed k≥2,T≥0,C>0,eps>0, choose a fixed `0<t≤1` such that `3*k*T*t≤eps/4`; using T+1 permits T=0. Then choose chi0 below `min(1,1/k)` such that, for every `0<chi<chi0`,
   `2*(C/log(1/chi))*log(1/t) + (1/sqrt(log(1/chi)))*log(1/t) ≤ eps/4`.
   This follows from `log(1/chi)→∞` or an explicit exponential cutoff. Neither t nor chi0 depends on d or N. CL1 with `tb=te=t` and residual eps/2 gives CL2.
4. For chi below one, both floor arguments in CL2 are nonnegative for N≥2. `Nat.floor_le` supplies the two exact budget inequalities, even if a budget exceeds K. Natural flooring is used only for the existing counting bound; it does not replace the real ProfileWord predicate.
5. Apply the already proved `profileClass_card_le` to every actual class domain, then CL2 at dimension `c*k`, rewriting only `D.k=k`, `A.C=C`, and `A.chi=chi` in the existing definitions. No identification with another package's different descriptor type is needed.

Empty horizons, c=0, T=0, empty actual profile domains, and floor budgets larger than K remain within the statements. No homogeneous cutoff or new variational assumption enters these counting results. They do not supply an edge localization or density estimate.

The primary agent compared all three exact reports before this freeze. They unanimously approve CL1–CL3 and all five local schemas, including all coefficients, casts, floors and quantifier order. No extra exported declarations, scientific premises, axioms or unproved terms are permitted. No earlier frozen statement may be modified.
