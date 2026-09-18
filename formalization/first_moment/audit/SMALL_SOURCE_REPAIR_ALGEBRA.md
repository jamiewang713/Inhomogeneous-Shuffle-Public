# Small proper-Gamma contribution: algebra and source integration audit

This is a read-only reconstruction of the existing source and Lean inputs, followed by proposed proof-local algebra. It changes no frozen definition, assumption, or theorem and contains no new Lean declaration. The mathematical source is the authorized unified TeX, especially Definition `def:first-moment-margin` (line 332), Definition `def:space-time-digit-profile` (line 700), Lemma `lem:ub-profile-estimates` (line 899), and the numerical and first-moment proofs (lines 1660–1914). The previously recorded `SMALL_BLOCK_REPAIR.md` is sharpened below using the now-proved finite density estimate.

## Conclusion and scope

The valid coarse density exponent closes the actual **small proper-Gamma case** through the original N1 condition, with an explicit total loss. The original quantified choice `epsilon ≤ eta/28` suffices and leaves a class exponent at most `-eta/4`, using the sharper individual bounds derived in that same construction. Nonnegativity of `profileS` is already a proved consequence of the source definitions, rather than an added model assumption. Neither the false endpoint anti-concentration bound nor a sign assumption on the local exponent beta is needed.

The remaining work for this branch is finite model adaptation and a new reviewed/frozen assembly statement, or proof-local assembly inside an already authorized final statement. The algebra below is not yet an exported Lean theorem. It does not close the large-block case, prove per-edge localization, or identify the complete final graph law.

## Existing proved inputs inspected

1. `EdgeLocalization.Exponent.Estimates.matrix_internal_density_le_small_coarse_exponent` has the literal conclusion

   `edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord xM)`
   `  ≤ N^(2 * tailEdgeExponent N n M + 8 * delta + 4 * ambientMeanError N n hA wA b) / 4`.

   Its premises are the column totals, `M ≤ K`, ambient length `a ≤ M`, coordinatewise ambient-prefix equality, `2 ≤ N`, a legal prefix, and `ambientSizeExponent < 2 * delta`. There is no anti-concentration premise. The displayed ambient error is signed. The proof uses the proved bound on the expected number of equal-row pairs, followed by the nonnegative finite-sum inequality. No conclusion about an actual fluctuation distribution is used.

2. `Exponent.Mean.prefixMean_eq_rpow_ambientSizeExponent` proves the exact identity

   `prefixMean(xM) = N^(ambientSizeExponent(xM) + ambientMeanError(wA,b))`.

   `Exponent.Tail.tailSquareFactor_eq_rpow_tailEdgeExponent` is exact, and `tailCollisionFactor_le_rpow_tailEdgeExponent` bounds the actual two-row tail collision factor by it. The latter is an inequality, not generally an equality.

3. `TimeProfile.Digits.profileS_nonneg` proves `0 ≤ profileS` under the existing source inputs `N ≥ 2`, positive chi, partition regularity, and prefix legality. Its proof is a finite sum of nonnegative good-digit frequencies times nonnegative representative costs. It adds no probabilistic or time-measurability assumption.

4. `TimeProfile.SourceNumerical.profile_parent_crossing_horizon` supplies the parent upper bound for S. `TimeProfile.SideMass.cF_lower_bound_of_crossings` supplies a finite real F and the fluctuation lower bound. `TimeProfile.IntegratedBounds.source_prefix_max_bound`, `source_entropy_bound`, and `source_tail_bound` supply the other three one-sided comparisons used below.

5. `TimeProfile.Numerical.numerical_le_infimum_add` passes a uniform pointwise theta bound to the literal infimum over `[3,4]`. The pointwise bound itself provides a lower bound on the range. No continuity, attained minimizer, or additional boundedness assumption is needed.

The existing `source_small_margin` concludes `-F + 2E + H ≤ -eta/2` from N2. That conclusion alone cannot be used by deleting `-F`. The repair instead combines its already-proved source inputs with N1.

## Exact finite scalar calculation

Write

`V = cL(join(y,z))`, `E = cE(x.length)`, `H = profileH`, `S = profileS`,

and set

`s* = max r (join(y,z).length / log N)`,
`u* = max r (x.length / log N)`,
`beta = localBeta mu r b s*`,
`B(theta) = integratedPsi mu theta s* u*`,
`Dtail = integratedPsi mu 2 u* T`.

For every theta in `[3,4]`, the established source estimates give

```
0 ≤ S,
S ≤ V - F + eS,
V/2 - eF ≤ F,
V ≤ beta + eBeta,
H ≤ theta*S - B(theta) + eH,
E ≤ -Dtail + eE.
```

The first four imply

`2*S ≤ beta + eBeta + 2*eF + 2*eS`.

Since S is nonnegative and theta+3 is nonnegative,

```
theta*S ≤ (theta+3)*S
        ≤ ((theta+3)/2)*(beta + eBeta + 2*eF + 2*eS).
```

The error terms `eBeta`, `eF`, and `eS` are nonnegative. Since theta≤4, this yields

```
H + 2*E ≤ ((theta+3)/2)*beta - B(theta) - 2*Dtail + Rnum,
Rnum = (7/2)*eBeta + 7*eF + 7*eS + eH + 2*eE.
```

Applying `numerical_le_infimum_add` and then the **first** component of the two-interval part of `FirstMomentMargin` gives

`H + 2*E ≤ -eta + Rnum`.

This uses the literal time-inhomogeneous N1 objective. N2 is not needed for this repaired branch, and no homogeneous cutoff constant appears. In particular, beta is allowed to be negative. The inequality using S≥0 is what makes the added coefficient 3 valid without assuming beta≥0.

## Explicit source errors and the complete loss

To avoid confusing the tail exponent with quadrature error, write

```
L = logScale N,
Alog = 4*log k,
qchi = log(1/chi)/L,
Omega = quadratureError N T rho phi P.cellCount Alog (Creg*chi),

eBeta = Omega + Alog*(er + 1/L),
eF    = (eb + qchi)/2,
eS    = Creg*chi*T + qchi,
eH    = Omega + Alog*alpha,
eE    = Omega.
```

Here `Creg` is the partition regularity constant, not the admissibility constant `A.C` of a boundary setup. These are precisely the finite errors used in `SourceNumerical`. They are nonnegative under its original sign/range assumptions. The entropy replacement uses the actual exceptional cutoff `profileR ≤ alpha` and `Alog ≥ 0`.

After the ambient equality listed below, `AmbientApproximation` gives

`|ambientMeanError| ≤ eb`, hence `ambientMeanError ≤ eb`.

Consequently the per-class exponent is bounded by

```
H + 2*E + 8*delta + 4*ambientMeanError
  ≤ -eta + Rtotal,

Rtotal = (7/2)*eBeta + 7*eF + 7*eS + eH + 2*eE
         + 8*delta + 4*eb
       = (13/2)*Omega + (7/2)*Alog*(er + 1/L)
         + (15/2)*eb + (21/2)*qchi + 7*Creg*chi*T
         + Alog*alpha + 8*delta.
```

The factor `1/4` in the density theorem remains available. If `Rtotal ≤ eta/2`, a class contributes at most `N^(-eta/2)/4` before any class-count or localization loss.

The application can retain the **unchanged** original choice `epsilon ≤ eta/28`. For `Creg=1` and `alpha=exceptionalAllowance chi`, write

`qRound = (chi+Alog+2*Alog*P.cellCount)*(floor(T/rho)+1)/L`.

The original construction in `exists_source_parameter_thresholds` and the premises retained inside `exists_uniform_source_margins` give

```
chi*T ≤ epsilon/16,
Alog*alpha ≤ epsilon/4,
2*Alog*rho ≤ epsilon/16,
Alog*P.cellCount*phi*T ≤ epsilon/16,
Alog*er ≤ epsilon/4,
eb ≤ epsilon,
qRound + Alog/L + qchi ≤ epsilon/16,
0 ≤ delta ≤ epsilon.
```

All three terms in the last logarithmic budget are nonnegative. Thus each is at most epsilon/16, and the literal quadrature formula gives

```
Omega = 2*chi*T + Alog*P.cellCount*phi*T + 2*Alog*rho + qRound
      ≤ 5*epsilon/16,
eS    ≤ epsilon/8,
eF    ≤ 17*epsilon/32,
eBeta ≤ 5*epsilon/8,
eH    ≤ 9*epsilon/16,
eE    ≤ 5*epsilon/16.
```

These are derived estimates, not new premises or parameter choices. Substitution gives exactly

```
Rnum ≤ (255/32)*epsilon,
Rtotal ≤ (639/32)*epsilon < 20*epsilon.
```

Under the existing `epsilon ≤ eta/28`, the class exponent is therefore at most

`-eta + (639/896)*eta = -(257/896)*eta ≤ -eta/4`.

There is no need to strengthen that choice to eta/65. Using only the common exported bounds `eBeta,eF,eS,eH,eE,delta,eb ≤ epsilon` would instead give the loose coefficient `65/2`; that coarse summary is insufficient at eta/28. My initial sufficient eta/65 re-budgeting is superseded by the sharper derivation above. The exact uniform proof should retain or rederive the intermediate budgets from `exists_source_parameter_thresholds`, `source_error_bounds`, and `uniformly_vanishing_ambient_budgets`; the already-exported `exists_uniform_source_margins` does not expose these sharper individual bounds as part of its conclusion. Its old conclusions alone do not imply the repaired estimate.

The source order is unchanged: choose the target epsilon, then sufficiently small chi, then the finite regular partition and its dimension, rho, phi, and finally a uniform large-N threshold; ambient data and words are quantified after that threshold. The stability parameter stays within the existing `[0,epsilon]` range. For arbitrary fixed `Creg`, the displayed finite loss remains valid; one must arrange its budget rather than silently apply the `Creg=1` quantified construction.

I independently checked these derived constants against `SMALL_SOURCE_REPAIR_INEQUALITIES.md`, SHA-256 `c8a5f92c99d8244634a7dc25dfa863e69cde01d5554f686c2856987e52ac391b`. Its `255/32`, `639/32`, and `257/896` coefficients agree. Its optional `619/32` total is also valid if one keeps the shared rounding budget: the coefficients on `qRound`, `Alog/L`, and `qchi` are respectively `13/2`, `7/2`, and `21/2`, so their combined contribution is at most `(21/2)*epsilon/16`. This sharpening is unnecessary for the retained eta/28 choice.

## Why an actual proper-Gamma word provides the inputs

Suppose `(y,z)` is an actual admissible pair, the join does not satisfy `Stop`, and `x ∈ Gamma A y z`.

* `admissiblePair_rawPair` gives `RawPair`. `gamma_first_crossing` gives `join.length < x.length`, a legal parent, and failure of `Stop` at the parent. The list-prefix facts put the join and ambient word below x.
* Since x is legal, `x.length ≤ K`. The strict join inequality therefore gives `join.length < K`. Both boundary words prefix the join, so the pair is nonterminal. Thus nonterminality is derived in this branch, rather than supplied as a new hypothesis.
* The proved `StableNumericalBridge.rawPair_crossings` and `legalVector_legal` give the exact `TimeProfile.Crossings` and legal-vector inputs. Applying `cF_lower_bound_of_crossings` at the join length gives a real F. `StableNumericalBridge.cF_eq` identifies it with the actual boundary-pair cF. Then `gamma_parentCrossing` gives the exact `ParentCrossing` predicate, so `profile_parent_crossing_horizon` applies.
* `cL_prefix_eq` and `ambientApproximation_iff` already identify the literal list exponents and expected ambient mass with the time-profile layer. The original horizon condition `D.K = horizonDepth D.N T` is still needed to apply the horizon-indexed source theorems; transporting along that original equality is finite bookkeeping, not a new asymptotic assumption.
* The time order `r ≤ s* ≤ u* ≤ T` follows from prefix lengths, the horizon floor, `N≥2`, and `r≤T`, as in the existing source proof. The N1 hypothesis is consequently applicable to these exact clipped endpoints.

No lower bound of the form `F ≥ delta - 1/sqrt(log N)` is required for the repaired proper-Gamma case. The argument also allows `x.length=K` if x is a genuine first-crossing word; its tail exponent is then zero. For a general stable word, identifying the proper-Gamma branch still requires the source's separate singleton split and terminal-fallback exclusion. This report does not infer Gamma membership solely from stability or block size.

## Passing from words to a refined profile class

The already-proved finite fibre entropy theorem bounds the actual fibre cardinality by `N^(keyH)`. The now-verified normalization theorems PN7–PN8 identify `keyH` with the literal source `profileH` for realized source keys. I independently audited their implementation in `PROFILE_NORMALIZATION_IMPLEMENTATION_ALGEBRA.md`, at source hash `9bc0039bbdbe5f970ad07bdcf8063c5c2bb46067a80d35fd53e9f60c64f73971`.

For a fixed realized refined key, the two boundary words, word length, good counts, and exceptional positions and values are fixed. Thus the join, H, and E are fixed. The ambient setup fixes the signed ambient error. One may restrict this fibre to the words that are small and proper Gamma; the subset cardinality is at most the full fibre cardinality. Exact `cL(x)` need not be constant on a profile fibre, and the proof must not assume that it is. The coarse small density bound is uniform over the restricted fibre, so finite summation gives

`sum_(x in the small proper-Gamma subfibre) density(x)`
`  ≤ N^(H + 2*E + 8*delta + 4*eb)/4`
`  ≤ N^(-eta + Rtotal)/4`.

Under the unchanged original quantified budgets this is at most `N^(-eta/4)/4`. Any later profile-counting or localization loss must be paid separately from this margin.

The unrealized-key case is empty. There is no appeal to `Nat.card` of an infinite type: finiteness and the actual fibre cardinality bound are already proved in `ProfileFibreEntropy`. Source profile classes are ranges of refined keys, not an injection of all words into their count vectors.

## Exact remaining EdgeLocalization model adapters

The following are mathematical identities or implications to prove, not additional assumptions. The stable-to-time-profile equalities have been proved already; their EdgeLocalization counterparts have not been supplied by the inspected four exponent files.

Let `n := (asCuts D).count`, let x be a legal list of length M, and let `X := legalVector x hx`. Define the short vector by restriction, `xM(t) := X(Fin.castLE hx.1 t)`. If `a=A.w.length` and `A.w` prefixes x, restrict xM once more to `wA : Fin a → Fin k`. This makes the coordinatewise prefix premise immediate.

1. **Literal word and legality.** Prove `prefixWord xM = x`, `prefixWord wA = A.w`, and `EdgeLocalization.legalPrefix n hx.1 xM`. The existing `prefixWord_represents_list` proves existential representability; the canonical restriction also aligns the already-fixed time-profile vector. Proofs use the proved digit equality, `List.ofFn` extensionality, list-prefix digit equality, and positive counts in `Riffle.Legal`.

2. **cL identity.** Prove

   `EdgeLocalization.ambientSizeExponent D.N n hx.1 a A.b xM`
   `  = Riffle.cL A x`
   `  = TimeProfile.cL D.N (asProfile D) X A.b a M`.

   The first equality is the finite reindexing of `Fin M` filtered by `a≤t.val` with `Finset.Ico a M`; the summands have exactly the same digit counts. The second equality is already `cL_prefix_eq`. No approximate ambient normalization can replace `A.b` in this equality.

3. **Ambient mean identity.** Prove

   `EdgeLocalization.prefixMean D.N n hA wA`
   `  = TimeProfile.prefixMass D.N (asProfile D) X a`
   `  = (Riffle.expectedCount D (Riffle.Cylinder D A.w) : Real)`.

   Reindex the finite products over `Fin a` and `positions K 0 a` and use `singleFactor = count/N`. The second identity is already supplied by the stable numerical bridge. EdgeLocalization's `prefixMass` is a probability, whereas TimeProfile's `prefixMass` is N times a probability; equating those two definitions directly would lose the factor N.

   The identity yields `ambientMeanError = log(TimeProfile.prefixMass)/log N - A.b`, and hence its absolute bound eb. The existing root theorem gives the exact error zero for ambient length zero and b=1.

4. **cE identity.** First prove

   `columnPsiTwo D.N (n j) = TimeProfile.psi (asProfile D j) 2`.

   It uses `singleFactor = prob`, and natural square equals real power at exponent 2. Then finite reindexing, with the `j.val<K` condition automatic, gives

   `tailEdgeExponent D.N n M = TimeProfile.cE D.N (asProfile D) M`.

   This equality holds for every M; when M≥K both tail sums are empty. There is no positivity requirement on each pile. Zero piles are allowed, and the existing tail theorems use the column sum N to obtain positivity of the total square sum. Positive counts are needed only along a legal prefix in the mean/cL identities.

5. **Probability-law compatibility, if the chosen final representation needs it.** The deterministic identities above suffice to combine the EdgeLocalization density theorem with source numerical quantities for EdgeLocalization's actual `matrixLaw`. If the final first-moment theorem uses the TimeProfile sample measure or another graph-law representation, the equivalence of fixed-column sample types, their uniform product laws, and the graph/rank labels must still be proved. `matrixLaw_uniform_weight` and `fixedCount_integral_eq_average` provide finite-average routes. An equality of expectations or graph events does not follow merely from equal pile counts.

All of these adapters preserve the original fixed-pile model. None repairs the outstanding large-block stochastic estimate, and none may be replaced with an unproved equality in the final assembly.
