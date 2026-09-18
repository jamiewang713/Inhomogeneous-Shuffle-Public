# Independent audit: coarse continuity partition and fine guard-band input

Source restriction: only the three authorized mathematical sources, with the relevant definitions and first-moment proposition checked in `time_inhomogeneous_riffle_shuffle_unified_article.tex`. No Lean or source changes. No other agent's report was read.

## Verdict

The proposed construction gives a valid deterministic perturbation-transfer lemma and can avoid strengthening the mathematical first-moment theorem. It works if the upper theorem is allowed to CHOOSE its one input partition and sufficiently small input parameters before quantifying over cut sequences. It does not follow from almost-likeness for an arbitrary partition that has already been fixed or supplied. The exact application to the completed first-moment theorem still depends on its partition, time-grid, ambient-size, and uniformity quantifiers.

The spatial-boundary difficulty itself is repairable without a non-atomicity assumption on the profile. Two additional issues must be handled explicitly: good-column thresholds under perturbations, and small final time cells after resetting/rescaling block time.

## 1. Construction of a coarse continuity partition

Let D be the compact simplex and let nu(A)=integral_0^T mu_t(A) dt. This presumes the usual measurable-probability-kernel meaning of the profile; the manuscript uses integrals over partition cells but does not spell that measurability out formally.

For each coordinate, at most countably many levels c have nu({p:p_l=c})>0. Choose finitely many internal coordinate cuts avoiding these levels, with maximum spacing h_0=O(chi^2). Their intersections with D give a finite Borel partition C_1,...,C_d. Use relative topology on the simplex: its fixed facets p_l=0 are not automatically included among partition boundaries. The union B of the internal cutting hyperplanes is closed in D and nu(B)=0.

Choose representatives in nonempty cells. A diameter bound O(chi^2) already implies the manuscript's chi-regularity:

- if the representative coordinate exceeds 2chi, every coordinate in the cell exceeds chi and logarithms differ by O(chi);
- if it is at most 2chi, every coordinate in the cell is at most 3chi;
- p_max is at least 1/k, and psi_p(theta), theta in [2,4], have uniform continuity/Lipschitz bounds on the simplex.

Consequently no hyperplane must be fixed exactly at chi,2chi,3chi, where the profile might have atoms. The manuscript says cuts can be placed 'near' these thresholds, and its actual regularity definition only demands the displayed cell inequalities. The construction respects those inequalities.

## 2. Guard bands and the ONE fine input partition

For epsilon>0 let U_epsilon be the union of closed coordinate slabs of width epsilon around the internal coarse cutting hyperplanes. Since nu(B)=0, nu(U_epsilon) tends to zero as epsilon decreases. Choose a fixed epsilon for the desired target error.

Refine the coarse cells by all slab boundaries and, if wanted, an additional small mesh. The resulting finite partition F_1,...,F_M refines every C_i and has U_epsilon as a union of cells. It remains chi-regular after choosing representatives, since refinement does not enlarge cell diameter. Its boundaries need not be nu-null for the transfer proof, although those extra levels can also be chosen to avoid atoms.

This F is the ONE partition tested in the original upper-bound assumption. There is no second independent testing assumption. However, the hypothesis must be posed for F from the outset. Knowledge that cuts are almost-like for some earlier coarse partition does not imply they are almost-like for F.

## 3. Exact transfer inequality

Let p_j be the original cut proportions and q_j the induced cut proportions, and suppose max_j ||q_j-p_j||_infinity<epsilon. For every coarse cell C_i,

    |1_{q_j in C_i}-1_{p_j in C_i}| <= 1_{p_j in U_epsilon}.

For a time interval I for which the original fine-cell almost-like estimates hold, write H_p(A,I)=(1/log N)*#{j:j/log N in I,p_j in A}, and nu_I(A)=integral_I mu_t(A)dt. Summing fine-cell errors gives

    |H_q(C_i,I)-nu_I(C_i)|
      <= nu_I(U_epsilon)+2M*phi_in*|I|+2M/log N.

This is the required deterministic lemma. It holds simultaneously for every induced sequence with the stated coordinate perturbation bound, so it introduces no probabilistic exceptional set and no union-bound loss over exploration blocks.

If all target grid cells have length at least ell_min>0, choose

    nu(U_epsilon) <= phi_out*ell_min/4,
    phi_in <= phi_out/(8M),

and then choose N sufficiently large that 2M/log N<=phi_out*ell_min/4. The desired coarse bound with phi_out follows, even with the manuscript's exact +1/log N convention, since the accumulated floor error is absorbed into the phi_out margin.

For the fixed absolute grid on [0,T], ell_min is min(rho, the positive terminal remainder T-rho*floor(T/rho)); if the remainder is zero, use ell_min=rho. The often-stated condition nu(U_epsilon)<<phi_out*rho must account for that terminal remainder if it is much smaller than rho.

## 4. All tails and temporal grid changes

No time continuity of mu_t is required. Since nu_I(U_epsilon)<=nu(U_epsilon), the same guard bound controls every interval, and hence every tail, as long as the target cells have a common positive minimum length.

If tail almost-likeness means only the original absolute-grid cells contained in [r,T], this is enough uniformly in r. That convention should be frozen explicitly.

If the first-moment theorem resets the grid at each birth r, or after scaling by the random block size, arbitrary target intervals need an additional time-blocking argument. For a fine input time mesh rho_in, covering a target interval by full input cells gives an extra error O(rho_in)+O(M*T/(rho_in*log N)). It is enough to choose rho_in much smaller than phi_out times the minimum target FULL-cell length, then choose phi_in and N. This is allowed only when the upper theorem can choose rho_in before testing the cuts; one cannot demand a smaller input mesh retrospectively from a hypothesis at a prescribed mesh.

There is a real remaining issue for terminal partial cells of reset grids: their length can be arbitrarily small as r varies. Global smallness of nu(U_epsilon) gives no bound proportional to every arbitrarily short interval. The profile can spend all of a short time interval near the coarse boundary while its total guard-band mass is small. Thus the null-boundary construction alone does NOT prove exact almost-likeness on all such partial cells.

Possible derived repairs include applying first moment at a slightly shortened, grid-aligned horizon and absorbing its O(rho) numerical loss, or establishing that the completed interface only uses full absolute-grid cells and already tolerates endpoint errors. Such a repair must be proved with the exact first-moment quantifiers; it is not a new assumption that may be inserted silently. Dropping the last few columns gives a supergraph of the full shuffle graph under the common-matrix coupling, so an earlier-horizon shared-edge bound can dominate the desired one.

## 5. Block-size normalization

For a large induced block with m cards, set b_N=log m/log N and r_N=M_prefix/log N. If the completed theorem uses m as its base population and restarts time, the correct transformed profile is

    mu^{r_N,b_N}_tau = mu_{r_N+b_N*tau}.

Then integrals scale by 1/b_N; the remaining horizon is (T-r_N)/b_N. For large blocks b_N>=xi>0 (or >=xi/2 after rounding), the same spatial partition and guard band work uniformly because

    integral mu^{r_N,b_N}_tau(U_epsilon)dtau <= nu(U_epsilon)/xi.

A target time cell of length rho_FM corresponds to a global cell of length at least xi*rho_FM. Choose the input time mesh and guard mass accordingly. This does not by itself prove the first-moment constants and N-threshold are uniform over all transformed profiles, horizons, r_N and b_N. That uniformity must be read from the checked theorem interface or derived from its proof.

If the completed first-moment theorem genuinely accepts ambient exponents and absolute times with original N as reference scale, these rescalings may be unnecessary. The current TEX statement uses that notation, but the precise conditional law/interface still needs checking.

## 6. Local good columns are a separate perturbation issue

From two coordinates p_l>=chi and q=p+o(1), one can only conclude q_l>=chi/2 for large N, not q_l>=chi. Equality at the threshold is allowed by the original hypothesis.

A valid parameter choice is to apply the first-moment theorem with threshold chi_FM and choose the original upper-bound good-column threshold 2chi_FM. The fine input partition can still be (2chi_FM)-regular: a sufficiently fine chi_FM mesh also has that property. This uses the existing freedom to choose a small threshold; it adds no separate model hypothesis. It must be fixed before freezing statements. If chi has already been prescribed and the exact FM theorem insists on that same value, the stated implication is false.

If a much finer input time mesh is used, its local good-column density implies density at least gamma/2 on target intervals much longer than that mesh, by discarding at most one incomplete subinterval. Apply FM with that smaller gamma. Again this is a derived quantitative loss, not an additional requirement.

## 7. Parameter and quantifier order

A consistent order is:

1. Fix model/profile, eta, k,T and the large-block lower exponent xi.
2. Choose admissible target FM parameters and a coarse continuity partition of the required regularity.
3. Fix target full-cell scales (and settle terminal-cell convention).
4. Choose guard-band width so its total nu mass is below all target error budgets.
5. Choose the ONE fine input spatial partition refining coarse cells and guard bands; record its finite cardinality M.
6. Choose a fine enough input time mesh, fine-cell tolerance phi_in small relative to phi_out/M, and the input good-column constants with the derived threshold/density losses.
7. Only then quantify over original deterministic cuts satisfying those input hypotheses and take N sufficiently large for the fixed guard width, M, and coordinate-error bounds.

The manuscript's informal hierarchy needs enough freedom for this two-layer construction. The fine input partition may depend on a target tolerance, while its own input tolerance is chosen only afterward. Calling both quantities 'phi' would conceal a circular choice. The first-moment theorem is applied to the coarse partition, so its own constants need not depend on the fine-cell count M.

If the already completed FM theorem is universal over all sufficiently regular chosen partitions, this construction can apply it verbatim. If it is proved only for a specific canonical partition selected once, one cannot replace that partition with a nu-continuity partition without an additional proved invariance/corollary. The current TEX proposition says 'the chosen chi-regular partition', which suggests freedom but does not substitute for the checked formal interface.

## Conclusion

The route is mathematically sound as a pre-freeze choice of one sufficiently fine input partition, with a derived coarse perturbation-transfer lemma. It removes the earlier atom-at-boundary counterexample because the coarse boundaries are deliberately chosen as nu-null and the original hypothesis now measures guard-band frequency. It does not justify the skeleton's unconditional claim for arbitrary preassigned partitions, nor does it finish conditioning, good-column transfer, time reset/terminal-cell handling, or uniform application of the completed first-moment theorem.
