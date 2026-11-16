# Final probability review of the exact candidate contract

Reviewed `CONTRACT_DRAFT.md` against my independent reconstruction from the three authorized mathematical sources. This is approval of the mathematical statements before implementation; it is not a claim that their Lean proofs exist.

**Decision: approve D1–D6 and every candidate ID F1–F5, H0–H7, C1–C4, N1–N2, X1 as written.** No mathematical correction or extra hypothesis is required. The manuscript's false ambient theorems remain excluded, exactly as the contract states.

## Individual review

| ID | Review |
|---|---|
| F1 | Valid finite probability/expectation/variance identities; no population nonemptiness assumption is needed. A finite law already forces a nonempty outcome type. |
| F2 | Valid Markov and Chebyshev inequalities with the stated strict positivity of thresholds; neither replaces exponential concentration. |
| F3 | Positive-event normalization and uniform-fiber conditioning are valid. Null fibers have zero unconditioned mass and are not conditional probability laws. |
| F4 | Valid finite tower identities and bounds, including on positive coarser atoms. In the conditional version, atom weights are naturally P(Z=z given U=u). |
| F5 | Valid even when S is not Z-measurable. On a good atom, the shifted integer event is either Y=q for a natural q or empty; then sum over atoms. |
| H0 | Valid. `Fin(m+1)` ensures q<=m, so the natural subtraction in the mass formula cannot produce spurious q>m masses. The remaining support inequalities are exact. |
| H1 | Valid at all feasible parameters, with the N=0 branch giving 0=0. |
| H2 | Valid for every r. At r=0 both sides are 1; at r>N both sides are 0 with total division. The real-polynomial second-factorial display is also valid at N=0,1. |
| H3 | Valid exact variance and degeneracy equivalence. Its complement implies 0<K<N and 0<m<N, hence N>=2 automatically. |
| H4 | Valid deterministic laws in every stated degenerate case, including N=0,1. |
| H5 | Valid with an absolute constant quantified before all parameters; c=1/2 is mathematically possible. Zero mean and zero threshold are treated correctly. |
| H6 | Valid with an absolute constant; the elementary log-concavity proof in my reconstruction gives C=16. Requiring v>0 is necessary for this reciprocal-variance conclusion. |
| H7 | Valid for every feasible parameter and 0<s<=1; detailed verification below. |
| C1 | Valid with exactly the stated feasibility conditions; detailed verification below. |
| C2 | Valid. Per-digit admissibility is necessary and sufficient; the event factors across independent columns, so residual columns remain independent. A zero residual population is valid. |
| C3 | Valid conditional sampling interface, provided the marked set's being determined by revealed information means it is constant on each reveal atom, as stated. The full population N is correctly retained. |
| C4 | Valid substitution of the exact conditional law into H1–H7, retaining each theorem's original domains (e.g. v>0 for H6 and 0<s<=1 for H7), followed by F4/F5. It does not assume a missing shuffle law. |
| N1 | Valid multiplication of nonnegative lower bounds in v=mu(1-K/N)(1-m/N)N/(N-1). The explicit N>=2 makes the last factor at least one. |
| N2 | Both arithmetic inequalities are valid under their stated premises; no missing feasibility or sign condition is needed. |
| X1 | Valid deterministic hypergeometric counterexample and endpoint description. The alternative histogram (L,1,L) gives the same residual law and a singleton stable block. Its endpoint counts are L and L+1, whereas those for (L,L,L) are L and 2L. |

## H7 verification, especially boundaries

Write p=m/N. If N=0, feasibility gives K=m=0, so the two sides are 1 and `(1-0+0*s)^0=1`. If N>0, 0<=p<=1. By intersection symmetry, the same count is obtained by sampling K positions without replacement from an N-element zero-one population with m ones. Hoeffding's convex comparison with K independent samples applies to the convex function x -> exp(log(s)*x), since s>0. This gives exactly

    E[s^Y] <= (1-p+p*s)^K.

At s=1 the two sides are 1. At K=0 or m=0 the two sides are 1. At m=N the count equals K and both sides equal s^K. At N=1 all cases are deterministic. No positive-mean or positive-variance hypothesis is needed. Proving the finite convex comparison, or using a matching trusted mathlib theorem, remains an implementation obligation; it cannot be assumed as an axiom.

## C1 verification, especially feasibility

With R subset of V and B subset of R, write r=|R| and b=|B|. Every sampled set in the fiber satisfies

    S = B union T,
    T subset of V minus R,
    |T|=m-b.

This is a bijection between the fiber and the `(m-b)`-subsets of `V minus R`. Such a subset exists exactly when b<=m and m-b<=|V minus R|. The original uniform law gives every legal m-subset positive mass, so nonempty fiber is equivalent to positive fiber probability. The bijection then proves conditional uniformity directly. For a test A subset of the residual population, its conditional intersection count is the hypergeometric law with population |V minus R|, marked |A|, and draws m-b.

If V minus R is empty, feasibility forces m=b, and there is exactly one residual subset, the empty set. If the event is infeasible, the contract does not assert a normalized conditional law. Thus the statement handles both the empty-population and null-event cases without added premises.

## N2 algebra checked explicitly

The first premise implies (N-r)-m>=h, hence

    1-m/(N-r) >= h/(N-r) >= h/N.

The second inequality uses the exact identity

    (K-s)/(N-r)-K/N = (r*K/N-s)/(N-r).

Its denominator is positive because r<N; absolute values therefore give the claimed bound, even when r or K is negative in this purely real statement.

## Freeze recommendation

Freeze the candidate contract without changes. The two parenthetical clarifications above about conditional atom weights and the alternative counterexample's endpoint counts merely spell out the existing statements; they do not change assumptions or conclusions. No Lean implementation was written during this review.

The coordinator's final clarifications are also approved: F4 explicitly uses conditional coarser-atom weights, C3 explicitly includes A subset of V, and X1 explicitly uses at least two columns and cumulative endpoint counts.

## Additional reviewed proof route for H7

The coordinator proposed a factorial-moment route that avoids a separate Hoeffding comparison theorem. It is mathematically valid. For u>=0, expand (1+u)^Y into its finite binomial series, use H2, and use

    (m)_r/(N)_r <= (m/N)^r

for the orders r<=K<=N that occur. For N>0 and r<=m this follows factor by factor from (m-i)/(N-i)<=m/N; for m<r<=N the left side is zero. This gives

    E[(1+u)^Y] <= (1+(m/N)*u)^K.

For 0<s<=1 set Z=K-Y. Complementing the selected subset, while retaining the same marked subset, gives Z law Hyp(N,K,N-m). Apply the preceding inequality to Z with u=1/s-1>=0 and multiply by s^K. Since Y+Z=K, the result is precisely H7. If one instead records the equivalent swapped law Hyp(N,N-m,K), one must bound the other descending-factorial ratio to retain the exponent K. This orientation detail prevents a wrong binomial comparison. The case N=0 is handled directly before any cancellation.
