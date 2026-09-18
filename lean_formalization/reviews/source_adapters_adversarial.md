# Independent adversarial review of finite source adapters S01–S05

Reviewed candidate: `FINITE_SOURCE_ADAPTERS_CANDIDATE.md`. Reviewed interfaces: `RiffleProfiles/Estimates.lean`, `RiffleTimeProfile/Base.lean`, and `RiffleTimeProfile/Ambient.lean`, together with the previously audited source definitions. No Lean implementation or frozen-contract edit was made during this review.

**Disposition: approve all five statements as written for the adapter freeze. No mathematical correction or additional assumption is required.** This approval is limited to their finite deterministic meanings and does not close any analytic, stochastic, asymptotic, or stopping-family obligation.

## S01: regular digits and cost convention

Approved. `RiffleProfiles.RegularDigits` requires exactly positive `chi`, the good-digit actual lower bound and cost error, and the exceptional upper bound. `TimeProfile.BorelPartition.IsRegular` supplies the latter two clauses at `i=P.classify(p j)`, while the candidate explicitly supplies `chi>0`.

The equality `TimeProfile.digitCost z = RiffleProfiles.cost z` holds for every real `z` under Lean's total logarithm convention, using `1/z=z⁻¹` and `Real.log_inv`. This includes zero; it is an identity of the existing total functions, not a claim that a zero selected pile is physically legal. Positivity of selected masses must still come from legality wherever a later theorem needs it. No full-support hypothesis is justified or needed.

The finite position set here is a `Finset (Fin K)`, so the already given `p` and `x` are defined at every selected position. Neither positive `C` nor `chi<1/k` is needed for this application of an already supplied regularity witness. The adapter does not claim existence of that witness for arbitrary parameter choices.

## S02: finite cE target approximation

Approved. Apply F06/F08 on `J=positions K M K` with actual value `psi(p j,2)`, classifier `P.classify(p j)`, and representative value `psi(P.rep i,2)`. Regularity applies because `2` lies in the closed interval `[2,4]`.

The source `cE` is the negative normalized sum, so the displayed expression `abs(cE + sum m_i*psi(rep_i,2))` has the correct sign. The finite error is exactly `card(J)*C*chi/L + sum |psi(rep_i,2)|*delta_i`.

No sign condition on `m_i` is needed. The count-error assumptions already bound the relevant differences; interpreting `m_i` as integrals would be a separate, currently unproved step. `N>=2` supplies `L>0`. The statement is valid for an empty tail and even `M>K`, because the existing range definition clips to available columns. This broader finite domain must not be confused with a claim that an overlong word is a legal source prefix.

## S03: finite maximal-pile target

Approved. Every position in `positions K w M` has `j.val<M`, so `LegalPrefix p x M` supplies positive selected mass even without an added assumption `w<=M` or `M<=K`. Simplex membership supplies `selected<=pileMax`; positivity of the latter follows immediately. F09 reverses the log-cost comparison in the required direction:

`cL <= b - actual normalized maximal cost`.

F06 controls the absolute difference between that actual cost and `sum m_i*maxCost(rep_i)`, yielding the stated one-sided error with the correct sign. The candidate retains all finite cell-cardinality factors and adds no integral interpretation. Empty/clipped ranges and negative ambient exponent `b` create no counterexample.

## S04: side mass, crossing factor, and NNReal maximum

Approved. Write

`earlier = prefixMass(N,p,x,w) * product_{h in positions K w j.val} prob(p h)(x h)`.

Since the witness satisfies `w<=j.val<v<=K`, the actual product factorization gives

`prefixMass(N,p,x,v) = earlier * product_{h in positions K j.val v} prob(p h)(x h)`.

The second product includes the crossing factor at `j`. Omitting that factor would give a wrong identity. All its factors lie in `[0,1]`, and `earlier` is nonnegative. The witness gives `chi*earlier<=sideMass(...,j)`, so frozen F10 proves the desired lower bound for this individual side mass.

`N>=2`, legality through `v`, and `chi>0` also give `0<chi*prefixMass(...,v)`. Consequently the witness side mass is positive. At this witness, `Real.toNNReal` converts back exactly to the original real value, and membership in `positions K w v` permits the finite supremum comparison.

No global nonnegativity assumption on the arbitrary function `side` is needed. Its values at other positions may be negative; truncating those values to zero in `sideMaximum` cannot invalidate the positive witness lower bound. Empty ranges do not require special assumptions because then no witness exists.

## S05: exact exponent and WithBot conversion

Approved. The hypotheses allow `cL_exact_mass_exponent` to rewrite

`cL(N,p,x,b,w,v) + (log(prefixMass at w)/L-b)`

as `log(prefixMass at v)/L`. Thus the left side in S05 is exactly

`(log(prefixMass at v)+log chi)/(2L)`.

Apply S04 once to each component of `Crossings`. Both side maxima `U,V` are at least the positive quantity `chi*prefixMass at v`, so `U,V>0`. Frozen F11 gives the corresponding minimum of `log U/(2L)` and `log V/(2L)`.

For positive `U,V`, both square roots are positive, and `log(sqrt U)=log U/2`, with the analogous identity for `V`. Therefore the two `logExponent` values in `cF` take their real branches. Casting the real inequality into `WithBot Real` and commuting the cast with the minimum gives exactly S05. No use of `log 0`, the bottom branch, an arbitrary representative of bottom, or a missing positivity assumption is permitted or needed.

The ambient discrepancy remains displayed exactly. It is not assumed small and may have either sign. A zero horizon or `w=v` makes `Crossings` impossible, so the statement remains valid without artificially strengthening the length inequalities. This is a comparison of the defined deterministic exponents only; the first-column variance/anti-concentration counterexample from the source audit remains unaffected.

## Scope boundaries preserved by this approval

- No time law, measurable kernel, Bochner-integral replacement, random matrix law, expected row count, or asymptotic limit is used.
- No source boundary family or stopping predicate is changed. In particular these statements never identify the existing non-strict `StableAt` with the source's strict first-crossing rule.
- The source's coarse profile is not refined or redefined.
- The adapters can be frozen and implemented without changing any assumption of F01–F20. Later applications to the paper must still prove all corresponding source-model hypotheses and transport identities.

## Pre-patch review of Lean 4.19 proof compatibility

Approved the following two proof-body-only compatibility changes in a local dependency snapshot; the original source files, definitions, theorem statements, and assumptions must remain unchanged.

1. **`TimeProfile.prefixWeight_extension_le`:** retain the exact statement with `v<=M` and its existing `hlegal`. Prove `positions K 0 M = positions K 0 v union positions K v M`, with disjoint parts, by the defining index inequalities. This identity remains true when either range clips at `K`; no new `M<=K` assumption is needed. Factor the prefix product accordingly. The earlier product is nonnegative, and every tail factor lies in `[0,1]`, hence the tail product is at most one. Multiplication gives the original inequality. If desired, the retained `hlegal` supplies positivity of the earlier product by restriction, but no additional full-support hypothesis is needed.
2. **`TimeProfile.cL_exact_mass_exponent`:** verified in the pinned mathlib source that Lean 4.19's `Real.log_prod` takes explicit finite-set and function arguments before the existing nonzero-factor proof. Replacing the proof invocation `Real.log_prod hp` by `Real.log_prod _ _ hp` is a pure API correction. The existing `hp` already establishes the exact required nonzero premise, so no statement or assumption changes are justified.
