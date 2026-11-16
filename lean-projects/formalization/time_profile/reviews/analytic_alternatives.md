# Can literal almost-likeness supply the missing measurability?

This is an analysis of the three authorized sources and the frozen literal definitions. It does not change the contract or introduce Lean declarations.

## The fixed-partition hypothesis is insufficient, even at zero tolerance

Choose k=2 and a sufficiently small chi. Take a chi-regular finite coordinate-grid partition. There are distinct rational points p=(a,1-a) and q=(b,1-b), with 1/3<a<b<1/2, in one cell D_i; they can be chosen in the interior of that grid cell. Their maximal-pile costs and their theta=2 collision costs are different. All their coordinates exceed 1/3.

Let V be a non-Lebesgue-measurable subset of [0,T]. Define mu_t=delta_p on V and delta_q on its complement. Every mu_t is a probability measure. For this partition, however, every cell mass is constant: mu_t(D_i)=1 and all other cell masses are zero. This statement holds pointwise; there is no measurability problem in the cell-mass functions themselves.

Use deterministic cuts equal to p when the integer pile sizes permit it. For a full sequence of deck sizes, round the p pile size; for all sufficiently large N the resulting p_N remains in the interior of D_i. All sampled columns then belong to D_i. Lattice counting gives, for every source closed grid interval I,

|# {j : j/log N in I}/log N - length(I)| <= 1/log N.

Thus the literal AlmostLike condition holds with phi=0, for every positive rho and every sufficiently large N. The local good-column condition also holds with any fixed chi<1/3 and sufficiently small positive gamma (up to the explicit endpoint rounding). This is a stronger cell-count assumption than the finite tranche requires.

Nevertheless profileMaxCost(t) alternates between the two distinct positive constants maxCost(p) and maxCost(q), so it is not Lebesgue measurable and is not integrable on [0,T]. The same is true of profilePsi(t,2). Their ordinary time integrals are undefined; Lean's totalized Bochner integrals are zero. The empirical normalized max cost converges to T*maxCost(p)>0, and the empirical normalized psi_2 cost converges to T*psi(p,2)>0. Consequently the source's two-sided quadrature and tail equalities do not follow from literal AlmostLike. Their failure is of constant order, even when the regular-cell oscillation is arbitrarily small.

The reason is that bounded nonmeasurable perturbations of arbitrarily small amplitude do not preserve totalized Bochner integrals. A small pointwise oscillation within a regular cell cannot replace a measurability proof.

This counterexample applies to the source's fixed chosen partition, exactly the form used by its first-moment proposition. “On every compact time interval” does not add a requirement to test every spatial refinement. It therefore does not eliminate the example.

## What an actually stronger all-refinement hypothesis could imply

For one fixed finite partition and one bounded interval I, suppose empirical cell frequencies approximate the totalized cell integrals with errors tending to zero, and the total frequency tends to length(I). Let G be the finite set of cells whose time-mass functions are integrable on I. The nonintegrable cells have totalized integral zero. Therefore

sum_{i in G} integral_I mu_t(D_i) = length(I).

The pointwise missing mass h(t)=1-sum_{i in G}mu_t(D_i) is nonnegative and integrable. Its integral is zero, so h=0 almost everywhere. Each omitted cell mass lies between zero and h, hence is almost everywhere zero and is integrable after all. Thus sufficiently accurate limiting cell counts can force integrability of the cell masses of that fixed partition.

This still does not force integrability of costs varying inside a cell; the example above already has every cell-mass function measurable. A countable refining sequence of partitions generating the simplex Borel sigma algebra, with the requisite approximation property for each refinement, could force measurability of all continuous cost functions by uniform approximation. It might also produce an almost-everywhere probability-kernel version of the family. The source does not state that stronger all-refinement quantifier, so adding it would be another substantive contract, not a consequence of the fixed-partition AlmostLike definition.

## A narrower one-sided route might prove the numerical implication

There is a possible finite approximation route that avoids asserting the source's false two-sided integral equalities. It uses the precise totalized integral semantics already declared in Base. This is an unfrozen proof proposal, not a completed theorem.

Let f be a nonnegative bounded one-column function, 0<=f<=M, with oscillation at most omega on every spatial cell. On a single rho-grid block I, write h_i(t)=mu_t(D_i) and F(t)=integral f dmu_t. Let G contain precisely those h_i integrable on I, and let h=1-sum_{i in G}h_i. Then h is a nonnegative integrable function, even when the individual omitted h_i are not integrable. AlmostLike plus total column counting controls the integral of h by the sum of the finitely many cell-count discrepancies and endpoint errors.

The finite representative sum over G is integrable. Pointwise,

|F(t)-sum_{i in G} f(rep_i)h_i(t)| <= omega + M*h(t).

If F is integrable on I, this proves an integral approximation with an explicit extra loss controlled by the missing mass. If F is not integrable, its totalized integral is zero, while the empirical f sum is nonnegative. In both cases one can seek the **one-sided** bound

empirical f sum >= totalized integral_I F - explicit error.

For an arbitrary interval, block it into full rho-grid intervals. If F is integrable on the arbitrary interval, it is integrable on all its subblocks and the preceding argument adds. If it is not integrable, the desired one-sided lower bound is again immediate from nonnegativity. Boundary intervals cost at most their length times M in the integrable branch. No time continuity is required.

This one-sided direction is exactly the direction required by the finite numerical kernel: an upper bound on c_E, an upper bound on c_L by beta, and an upper entropy bound after subtracting the profile collision cost. It does not recover the source's two-sided profile-estimate statements and does not make its ordinary time integrals meaningful. A formal continuation could potentially prove the numerical implication for the explicitly totalized definitions, with new carefully compared analytic theorem statements, while truthfully retaining the failure of the stronger source equalities.

To use this route, all agents would first need to reconstruct and freeze the exact missing-mass and interval-blocking error bounds. It must not be presented as a proof that arbitrary mu_t was secretly a measurable kernel, nor as an unchanged proof of the manuscript's full analytic layer.

## Conclusion

The original two-sided analytic layer cannot proceed unchanged under the literal fixed-partition hypothesis. The counterexample satisfies stronger fixed-partition counting than requested. A measurable-kernel/integrability contract remains the direct faithful interpretation of the intended ordinary integrals. Separately, a one-sided totalized-integral route appears viable for the numerical upper-bound implication and deserves independent review if the user declines additional profile regularity.
