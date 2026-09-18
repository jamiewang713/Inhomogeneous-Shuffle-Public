# Focused independent review: two-partition guard-band robustness

Source checked: the original TeX's almost-profile definition (around lines 249-303), parameter hierarchy (around 474-487), regular-partition/interval-blocking lemma (around 857-896), and first-moment proposition (around 1817-1838). This review proves a finite-partition perturbation lemma. It does not certify that the existing uninspected Lean first-moment interface accepts its output.

## Verdict

The proposed coarse/fine guard-band construction is mathematically valid. It can derive exact coarse-cell almost-profile bounds for perturbed conditional pile vectors from a single, predetermined fine-partition almost-profile assumption. Neither a weak-almost-like assumption nor a second independent empirical hypothesis is needed **if the original theorem allows the input partition to be chosen as this fine partition before its hypotheses are fixed**, and if the completed first-moment theorem applies to the coarse partition with the predetermined larger error tolerance.

It is not a consequence of almost-likeness on an arbitrary partition already fixed in advance. The source says 'Fix a finite measurable partition' in the definition, and 'the chosen chi-regular partition' in the first-moment proposition. Those words are consistent with a proof that chooses the input partition, but they do not explicitly give the quantifier statement needed to certify the two-partition application. Therefore the formal theorem has not passed its freeze audit solely on this proposal.

## 1. Exact setup

Let X=D_k be the compact probability simplex with its relative topology and the infinity metric. Let (mu_t)_{0<=t<=T} be a measurable probability kernel, or any already specified profile structure for which nu(E)=integral_0^T mu_t(E)dt is a finite Borel measure. Nu(X)=T.

The original source calls the profile a family of probability measures and uses these integrals implicitly. A formalization must supply the corresponding measurability as part of the definition of time profile. Measurability of only a few cost functions is not enough by itself to define nu on arbitrary Borel guard bands.

Fix chi>0, rho>0, and a target coarse almost-profile tolerance phi_out>0. Let I_r=[r rho,min((r+1)rho,T)] range over the positive-length original grid intervals. This is a finite family. Define ell_min=min_r |I_r|>0. If T is a grid point, ell_min=rho (or T if T<rho); otherwise the final clipped interval can be much shorter than rho.

For N>1, set h_N=1/log N and index the columns at j/log N. For any interval I and Borel set E define

M_N^p(I,E)=h_N * #{j: j/log N in I, p_j in E},
nu_I(E)=integral_I mu_t(E)dt.

The original exact almost-profile condition for a finite partition Q is

|M_N^p(I,Q)-nu_I(Q)| <= phi_in |I|+h_N

for every Q-cell and every grid interval I.

## 2. Construct a coarse chi-regular partition with nu-null boundary

For each coordinate l, the finite pushforward measure (p -> p_l)_*nu has only countably many atoms. Choose a finite coordinate grid on [0,1] with maximum spacing h<=c chi^2, with every **internal** grid threshold outside the countable set of atoms of that coordinate marginal. This is possible by choosing thresholds in small open intervals around a nominal mesh. Half-open coordinate boxes, intersected with X and with consistent endpoint conventions, form a finite Borel partition P of X.

Let H be the union, inside X, of all the internal coordinate-threshold hyperplanes. Then nu(H)=0. Relative boundaries of the P-cells lie in H. Do not add the exterior faces p_l=0 or p_l=1 to H merely because they are boundaries in ambient Euclidean space: mu_t may be supported on those faces, and they do not obstruct stability of membership in the relative simplex partition.

Every nonempty P-cell has infinity diameter at most h. Choose an arbitrary representative in each cell. The diameter estimate implies the source's chi-regular requirements, uniformly over representatives:

* max p>=1/k, so a_p=log(1/max p) changes by at most C_k h within a cell;
* for theta in [2,4], sum p_l^theta>=k^(1-theta)>=k^-3; the coordinate derivatives of -log(sum p_l^theta) are uniformly bounded, so psi_p(theta) changes by at most C_k h;
* if representative coordinate r_l>2chi, then every cell point has p_l>=r_l-h>chi and |log p_l-log r_l|<=h/(2chi-h)<=C chi;
* if r_l<=2chi, then p_l<=2chi+h<=3chi.

Thus no grid threshold is forced to equal chi, 2chi, or 3chi. The source's phrase about inserting cuts 'near' those thresholds is compatible with avoiding atoms. The basic mesh construction alone already supplies the stated regularity inequalities.

## 3. Choose and resolve a fixed guard band

For delta>0 let

U_delta = union over internal coordinate thresholds a in coordinate l of {p in X: |p_l-a|<=delta}.

These are closed relative subsets, decrease to H as delta decreases to zero, and nu is finite. Continuity from above therefore gives nu(U_delta)->0. Choose a **fixed positive** delta such that

nu(U_delta) <= (phi_out/4) ell_min.

It may also be chosen smaller than one fourth of the minimum spacing between distinct grid thresholds.

Define the fine partition Q to contain the nonempty sets

C intersect U_delta, and C minus U_delta,

as C ranges over P. It has at most 2|P| cells, refines P, and U_delta is a union of its cells. Its cells need not be connected or simplices: the source's definition only requires finite Borel cells. Every Q-cell lies in one small coordinate box, so the same diameter argument proves Q is chi-regular even when its representative differs from the coarse representative.

Only the **coarse** boundaries need to be nu-null. Fine boundaries at a plus/minus delta may carry mass; this causes no difficulty because the perturbed q_j are never required to keep their fine-cell membership.

## 4. Exact counting estimate

Suppose p_j and q_j are probability vectors satisfying ||p_j-q_j||_infinity<delta for all columns under consideration. If p_j is outside U_delta, its coordinate lies more than delta from every coarse threshold, so p_j and q_j belong to the same coarse cell.

Let b be the number of fine cells contained in U_delta. For a coarse cell C let f_C be the number of its fine constituent cells, so f_C<=2. Suppose the p_j satisfy the fine almost-profile condition with tolerance phi_in. Summing it over constituent cells gives

|M_N^p(I,C)-nu_I(C)| <= f_C phi_in |I|+f_C h_N,

and

M_N^p(I,U_delta) <= nu_I(U_delta)+b phi_in |I|+b h_N.

A perturbed coarse indicator differs from its original value only at a column in U_delta. Consequently

|M_N^q(I,C)-nu_I(C)|
 <= |M_N^p(I,C)-nu_I(C)| + M_N^p(I,U_delta)
 <= (f_C+b) phi_in |I| + nu_I(U_delta) + (f_C+b)h_N.

This is the exact finite-N result. The rounding coefficient becomes f_C+b, not 1. It must be accounted for explicitly.

Let C_*=max_C(f_C+b), a finite positive integer. Choose phi_in<=phi_out/(4 C_*). Since nu_I(U_delta)<=nu(U_delta)<=phi_out ell_min/4<=phi_out |I|/4, the two non-rounding errors total at most phi_out|I|/2. For N sufficiently large that

(C_*-1)/log N <= (phi_out/2)ell_min,

the bound becomes exactly

|M_N^q(I,C)-nu_I(C)| <= phi_out |I|+1/log N.

Thus the perturbed vectors satisfy the source's exact coarse-cell almost-profile condition, with no change to its final unit rounding term.

The weaker suggested bound nu(U_delta)<=phi_out rho is insufficient for the final clipped interval when its length is less than rho. Using ell_min repairs this. Alternatively, if the formal theorem uses only full rho intervals, using rho is sufficient with the same slack constants.

## 5. Uniformity needed for conditional blocks

P,Q,delta,phi_in,phi_out are fixed before N tends to infinity and do not depend on the realized explored history, chosen prefix, or conditional block. Hence the preceding bound applies simultaneously to every conditional block on an event on which its induced tail proportions q_j satisfy max_j ||q_j-p_j||_infinity<delta.

For large blocks of expected size at least N^xi, a concentration estimate such as

|n_j^x(l)-|I_x|p_j(l)| <= C(N lambda_x)^(4/5),
|I_x| >= (N lambda_x)/2

implies max_{j,l}|q_j(l)-p_j(l)|<=C' N^(-xi/5), which is eventually less than delta uniformly. This uses a previously proved conditional concentration statement; the guard-band lemma does not establish concentration.

The lemma applies on every common original grid interval on which both the fine empirical hypothesis and the perturbation estimate are available. For a tail [r,T], use original-grid intervals contained in that tail. If the first-moment theorem reanchors its grid at arbitrary r or rescales by log|I_x|, the exact interval interface must be checked separately. Arbitrarily short r-dependent clipped intervals do not have a uniform ell_min, and a bound on total nu(U_delta) cannot imply a uniform relative error phi|I| on all arbitrarily short intervals. The source's interval-blocking lemma instead supplies additive O(rho+phi)+o(1) errors for arbitrary subintervals; this is another possible interface, but it must be used explicitly rather than called exact almost-likeness.

Zero coordinates in induced vectors are harmless for partition membership: the proof operates in the closed simplex. Positivity/good-column preservation is separate: if an original coordinate is at least g and q-p is less than g/2, the induced coordinate is at least g/2. One must not call it g-good at the unchanged threshold without a margin. Keeping a fixed original good threshold g and applying subsequent definitions at g/2 is a derived property, provided both thresholds and parameter uses are frozen in advance.

## 6. Required quantifier structure

A precise theorem in which this repair is legitimate can have the following order:

For each k,T,eta,gamma and suitable profile mu, choose a small chi, a coarse chi-regular partition P, and first-moment parameters (including rho and phi_out). Then choose a fixed guard band, its fine chi-regular refinement Q, and phi_in>0. There exists N_0 such that for every N>=N_0 and every original cut sequence whose proportions are fine-Q-(rho,phi_in)-almost-like and satisfy the original local-good and margin hypotheses, all sufficiently close induced conditional sequences are coarse-P-(rho,phi_out)-almost-like.

The assumption is still one almost-profile condition on **one selected input partition Q**. Almost-likeness on P is deduced, not separately assumed. The first-moment theorem is invoked with P. This is compatible with an upper theorem whose partition is chosen by the proof or whose hypothesis requires almost-likeness for every sufficiently fine regular partition.

However, if the intended frozen theorem has already selected a specific partition P_0 and assumes almost-likeness only for P_0, imposing almost-likeness on a new refinement Q is a real strengthening. Coarse-cell counts provide no information about how columns split inside a coarse cell, so there is no general implication from P_0-almost-likeness to Q-almost-likeness. The construction may not silently change P_0 to Q.

Similarly, the completed first-moment theorem must either accept any chi-regular coarse partition with the stated uniformity, or its designated partition must be shown to permit the boundary-null construction. One cannot replace a fixed theorem's partition merely because the new one is also regular.

## 7. Parameter hierarchy and possible circularity

The guard-band width depends on rho and phi_out, whereas the source describes choosing chi and its regular partition before the smaller numerical parameters. This does not create a mathematical circularity if the first-moment estimates are uniform over partitions with the same diameter bound, regularity constants, and a bounded number of cells: Q has at most twice as many cells as P, and its regularity constants do not depend on the guard width. One can choose first-moment parameters against this predetermined cardinality bound and choose the guard band afterward.

But this uniformity is another interface fact to verify in the completed theorem. The prose 'all constants may depend on parameters to their left' and 'the chosen partition' does not by itself formalize it. A clean formal approach is to state and prove the finite guard-band lemma independently, then inspect whether the frozen first-moment parameter-selection theorem provides a partition/parameter choice that can be instantiated in the order above. Do not add a robustness or fine-partition assumption after freezing.

## 8. What this establishes and what remains

Established here: boundary-null regular partition existence, finite guard-band refinement, exact perturbation counting inequality, predetermined error absorption including the 1/log N rounding term, and uniform applicability to all blocks whose conditional proportions are close.

Not established here: the conditional concentration event, the exact self-reduction law, the first-moment theorem's coarse-partition/absolute-time applicability, the original theorem's missing partition quantifiers, or the exponential-moment upper bound as a whole.

Therefore the mathematical guard-band method is a viable repair, but the formal freeze still requires the exact partition and parameter quantifiers to be resolved from the intended theorem statement, not inferred as a new hypothesis.
