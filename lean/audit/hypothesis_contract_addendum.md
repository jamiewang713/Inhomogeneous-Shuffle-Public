# Final adversarial review of CONTRACT_DRAFT.md

Reviewer: hypothesis audit agent. Reviewed after the raw-source report `hypothesis_audit.md` and before any Lean implementation. No assumptions or theorem statements are changed by this report.

## Decision

**Approve F1–F5, H0–H7, C1–C4, N1–N2, and the exact finite content of X1 for freezing.** The earlier support, null-conditioning, empty-population, zero-variance, and ambient-buffer objections are addressed in the draft. I found no mathematical counterexample to these finite targets. The final approval includes the root's subsequent clarifications of F4's conditional weights, C3's `A⊆V`, and X1's two-column and cumulative-count wording; those versions were reread explicitly. No mandatory mathematical correction remains.

Two wording clarifications are recommended before the text is marked frozen; neither adds an assumption to a valid target:

1. In C4, say expressly that transferring H1–H7 preserves all their respective premises, including `t≥0` for H5, `v(z)>0` for H6, and `0<s≤1` for H7. “Any threshold constant on each atom” means any threshold satisfying the premise of the transferred theorem.
2. In X1's explanatory connection to the source, distinguish the residual population `2L` from the original column populations `3L` and `2L+1`. The source boundary/stability interpretation uses `k=3`, `0<χ<1/3`, at least two columns, and the definition's positive `δ`. The unconditional fixed-column endpoint count and residual law need none of those asymptotic assumptions. They should remain the actual finite theorem; the source interpretation should list its existing context explicitly.

This is approval of the statements as mathematical targets, not certification of any as-yet-unseen proof or specific numerical anti-concentration constant.

## ID-by-ID check

| ID | Decision | Adversarial check |
|---|---|---|
| F1 | Approve | Finite nonnegative masses summing to one suffice. Empty outcome types cannot carry D1, so no hidden nonempty hypothesis is needed. All real-valued functions are finite sums; variance expansion and positivity are valid without integrability assumptions. |
| F2 | Approve | `f≥0,t>0` is precisely the required Markov regime. Centered square is nonnegative and `t²>0`, giving Chebyshev. These are clearly auxiliary and do not replace exponential concentration. |
| F3 | Approve | The denominator is strictly positive. A uniform law on its finite outcome type gives positive mass to every point, so a nonempty fibre has positive probability. A null fibre of a general finite law may contain zero-mass outcomes, but its total contribution to weighted sums is still zero. |
| F4 | Approve | Only positive atoms require conditional bounds. Null atoms have zero mixture weights. In the coarser version the weights must be the conditional atom probabilities given the positive coarse atom, which is the stated analogous finite law of total probability. No independence is needed. |
| F5 | Approve | On a fixed finer atom the shift is fixed and addition from naturals to integers is injective. If `j−A(z)<0`, the event is empty and `b≥0` covers it. The good set is a union of finer atoms; the arbitrary event `S` is merely contained in it, which suffices. It need not be measurable in the finer reveal. Positive coarse atoms are explicitly required. |
| H0 | Approve | `choose(N,m)>0` follows from `m≤N`, including `N=m=0`. On `Fin(m+1)`, positivity is equivalent to the stated two binomial support conditions. D3's separate zero-mass rule for `q>m` repairs the natural-subtraction trap. Agreement with subset sampling and a trusted PMF/measure representation remains a theorem to prove. |
| H1 | Approve | At `N=0`, feasibility forces `K=m=0` and the canonical law is the atom at zero. Total real division gives mean zero. At positive population the usual mean formula is valid without positivity of either pile size. |
| H2 | Approve | The falling-factorial identity is valid for all `r`. If `r>N`, then `r>m`, so the integrand and numerator vanish and total division yields zero. At `r=0` the denominator is one even for `N=0`. The real second-factorial-moment formula also vanishes correctly at `N≤1`. |
| H3 | Approve | For `N≥2`, all four numerator factors are nonnegative and the denominator is positive; the zero set is exactly the four stated deterministic boundary cases. For `N≤1`, feasibility forces one of those cases. Casting before subtraction avoids accidentally importing natural truncated subtraction into the real algebra. |
| H4 | Approve | Sampling zero elements or marking none gives zero; sampling the whole population gives exactly `K`; marking the whole population gives exactly `m`. Intersections of these cases, including `N=0`, agree. Positive centered tails vanish and point masses are at most one. |
| H5 | Approve | Absolute `c` is quantified before parameters. All `t≥0` and all small means are included. At `μ=t=0`, the tail event is the full event and RHS is two. At `μ=0,t>0` the count is zero. There is no hidden `N≥2`, positive-mean, or variance-lower-bound premise. |
| H6 | Approve | Absolute `C` is quantified before parameters; `v>0` implies a positive square root and excludes every deterministic case. Arbitrary `q>m` has zero mass by D3. H4 handles `v=0`, so no erroneous bound by division by zero is asserted. A proof choosing `C=16` still needs an actual derivation. |
| H7 | Approve | It is a theorem of the canonical law, not an extra axiom about it. At `N=0`, feasibility gives `K=m=0`; both sides equal one. At `s=1`, both sides equal one. At `m=0` or `K=0`, both sides equal one. At `m=N>0`, equality is `s^K=s^K`. All powers use natural exponents. |
| C1 | Approve | D5 already supplies `m≤|V|`. `B⊆R`, `|B|≤m`, and `m−|B|≤|V\R|` are exactly the extension conditions for `S∩R=B`. The complement map is a bijection to residual samples and preserves uniformity. A test set disjoint from `R` gives exactly the stated residual hypergeometric law. When `V\R` is empty, feasibility forces zero residual draws and the unique empty law. |
| C2 | Approve | A legal fixed assignment on `R` has digit totals summing to `|R|`. The inequalities `r_l≤n_l` make every residual count nonnegative, and their sum equals the number of residual labels. This is sufficient as well as necessary for a legal extension. With independent columns, the conditioning event factors by column, so residual independence is valid. It is correctly not asserted for arbitrary exploration events. |
| C3 | Approve | “Determined by already revealed information” means the marked set is constant on each reveal atom. The conditional sample law on that atom then supplies the exact D5 experiment, with no within-column independence assumption. Feasibility is inherent in D5's uniform-subset law. In successive thinning, the fixed sample still lives in the full labelled population rather than in the previous survivor set. |
| C4 | Approve | Exact conditional-law equality is enough to transfer finite moments and event probabilities. Random parameters and thresholds are harmless when fixed on an atom. Null atoms are excluded and finer-to-coarser transfer uses F4/F5. This cannot establish a shuffle application's law by itself; the contract correctly requires C1–C3 or a proved law argument at each application. Preserve the original target's premises as clarified above. |
| N1 | Approve | For `N≥2`, `v=μ(1−K/N)(1−m/N)N/(N−1)` and `N/(N−1)≥1`. The three nonnegative lower bounds yield the conclusion by multiplication. These are explicit premises of a separate arithmetic statement; no such reserves are assumed of the false ambient source theorem. |
| N2, first clause | Approve | `m+r≤N−h` implies `N−r−m≥h`. As `0≤r<N`, both denominators are positive and `N−r≤N`, so `(N−r−m)/(N−r)≥h/(N−r)≥h/N`. No missing bound on `m` is needed. |
| N2, second clause | Approve | `N>0,r<N` gives `N−r>0`; no lower bound on `r` is needed for this algebraic clause. The exact identity is `(K−s)/(N−r)−K/N=−(s−rK/N)/(N−r)`. Taking absolute values gives the bound. |
| X1 | Approve | For every `L≥1`, `N_res=2L,K=L,m=2L` samples the whole residual population, hence is the atom at `L`, with mean `L`, variance zero, and sample complement zero. Removing the middle-digit labels from either histogram `(L,L,L)` or `(L,1,L)` leaves precisely this residual experiment. Exact original block endpoints are `L,2L` in the first case and `L,L+1` in the second, under the manuscript's count-endpoint convention. The latter block has one row. |

## Comparison with the raw-source findings

- D3 fixes the conflicting positional hypergeometric conventions by naming population, marked count, and draws.
- D5 fixes the omitted independence issue by using a fixed marked set and one uniform sample.
- D4 and H1–H4 explicitly handle empty populations, singletons, all-zero and full-pile cases.
- H5 keeps the source's small-mean regime; H6 preserves the positive-variance requirement.
- D2 and F3–F5 prevent null-atom conditioning and handle a global good event that need not be finer-measurable.
- C1–C3 specify the information that yields genuine conditional hypergeometric laws, instead of treating arbitrary conditioning as harmless.
- N1/N2 isolate valid arithmetic without presenting the missing ambient reserves as assumptions of the original theorem.
- X1 retains the counterexample, while the false ambient claims and unsupported general exploration-preservation assertion remain outside the freeze.

No Lean code was written in this review.
