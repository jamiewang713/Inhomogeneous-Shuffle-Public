# LB05 independent implementation review v1

Reviewer: the one-column/representation worker, reviewing the independently written Selection, Empirical and Rounding modules. This report concerns the helper-module snapshots below, not a final coldWitness theorem or subsequent edits.

## Snapshot and verification

- `Witness/Selection.lean`: `1faff3cd95f508d2dc5c839479cd36765a30c9dbe34c759b25f452996499dfb4`.
- `Witness/Empirical.lean`: `f77db0ae1c4083b96fb9685ec391e5ce067831f35afe37e743a998bc12df2695`.
- `Witness/Rounding.lean`: `c8b3b2ee0b8eb897607b7c9f1c2d13e87cd659561a355b75a2912f0e24caf959`.

All three existing lane oleans imported successfully in the pinned runtime. The 24 key checked declaration axiom closures are recorded in `implementation_review_axioms_v1.log`: each contains only `propext`, `Classical.choice`, `Quot.sound`. No forbidden proof token occurs in the current Witness source directory. This reviewer did not modify the reviewed modules.

## Variational and selection audit

`variational_pair` correctly handles the real conditional-completeness requirements. For each allowed pair it derives boundedness below of the inner image from continuity on compact [3,4]. The outer image is bounded above by M because every inner infimum is at most the alpha=3 value. The triangle is nonempty through (0,0) using T>=0. Strict inequality `7*eta/8 < sSup` follows from eta>0 and the margin hypothesis, so `lt_csSup_iff` gives an actual pair. The final inner infimum comparison is correctly directed. No supremum/infimum interchange or unproved attainment occurs.

`select_tilt` covers both endpoint cases then applies the intermediate value theorem with the correctly reversed endpoint interval in the remaining case. It needs no monotonicity hypothesis: continuity and endpoint ordering suffice. This is a valid simplification of the manuscript route, not a weakened conclusion.

`shorten_selection` preserves the three-case distinction. The theta=4 branch uses the explicit pointwise no-loss premise and imposes no bound on displacement. Every other moving branch has initial j<=b/2 and final j=b/2-4*kappa, hence loss<=16*kappa. A stationary selection must be theta=3 because the opposite alternative would force j>=b/2. The positivity of the target shortening level follows from b>=eta/4 and kappa=eta/1000.

`cold_identity`, `rounding_margins`, `final_margins` and `endpoint_error_algebra` use the manuscript's exact expressions and constants. The product correction `(theta-3)*(jp-b/2)` is bounded below by -5*kappa using theta in [3,4] and the theta=3 exception. The geometry inequalities follow from H<=J, nonnegativity, and J<=b/2-3*kappa. The two endpoint allowances `r+4e` and `5r+20e` retain the source constants.

Both terminal-clearance helpers use the beta gap rather than assuming birth-time clearance. They correctly compare a displacement multiplied by log k with `b-betaS`, use the kappa0<=kappa/100 branch of the definition, and retain a strictly positive gap from eta/4. Their log N denominator premises must be discharged in concrete use, as planned.

## Empirical interpolation audit

`columnFraction_sum` telescopes the clamped ramps and proves that their sum is t log N throughout [0,K/log N]. It includes K=0 without assuming a nonexistent column. The resulting constant-integral identity is exact, so the upper endpoint estimate scales with interval length and not with the number of columns.

Monotonicity and positivity rely explicitly on N>=2, hence log N>0. The absolute-integral bound handles both orientations by antisymmetry; the endpoint bound splits the difference into the two displaced endpoint integrals. The hypotheses require all four endpoints to lie inside the actual finite horizon. These are the needed hypotheses for rounding, with no macroscopic profile or temporal regularity assumption.

Continuity is proved directly for finite clamped sums, including parameter continuity from finitely many continuous column functions. The linearity identity is a finite ring/sum identity. These generic helpers are proved facts, but by themselves do not discharge specialized one-column bounds or the empirical target; the ongoing specialized implementation must instantiate them with the actual cuts.

## Integer and bridge audit

`rounded_indices` defines exactly the manuscript floor/min/ceiling construction. Strict left clearance proves ms+b<=K before natural subtraction is used, avoiding saturation errors in K-b. It then proves ms<=mu, mu+b<=K, and the two endpoint errors. The clipped case is bounded by the ceiling error and the original u<=K/L condition.

`good_bridge_columns` applies LocalGood on `[u+rho/2,u+3rho/2]`, a length-rho interval strictly inside the length-at-least-2rho bridge. Its left time is strictly larger than u, so all counted columns satisfy the required zero-based lower index mu. Its right time is at most the bridge endpoint. Thus the possible one-column loss from a closed interval starting exactly at u is avoided by a permitted interior interval; no strengthening of LocalGood is introduced. The premise `3 < density*rho*log N` is stronger than the cardinality-two requirement and will be discharged by a fixed logarithmic threshold.

The two threshold lemmas choose their natural threshold before N and contain no cut parameter. When combined by a maximum, they preserve the required cut-uniform quantifier order.

## Verdict

No mathematical or representation defect was found in these snapshots. All generic assumptions are legitimate local lemma premises and have a clear route to discharge from the fixed contract. The next audit boundary is the concrete assembly: the final theorem must derive each premise, construct W, preserve the frozen numerical margins and place N0 before every cut array. This report does not pre-certify that later assembly.
