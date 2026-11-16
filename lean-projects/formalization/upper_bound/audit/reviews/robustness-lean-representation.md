# Focused review: two predetermined partitions

This is an independent representation/quantifier review of the requested repair. Mathematical source scope remained the three authorized files. No Lean code was written. The completed first-moment Lean declaration is still unavailable.

## Verdict

The proposed two-partition construction gives a correct deterministic transfer from one chosen fine-partition input condition to a coarse-partition almost-like condition for perturbed conditional pile vectors. It can avoid assuming a weak first-moment theorem. It requires choosing the fine input partition before N and the cut sequence, with its dependence on the fixed profile and all fixed parameters explicit.

This repairs the exact-cell-preservation obstruction for such an upfront choice. It does NOT show preservation of an arbitrary already fixed partition, and does not repair the separate conditional-law, exploration, or first-moment-import gaps.

## 1. Exact source quantifiers

The relevant manuscript text is:

- Definition `almost-time-profile-like-cuts`, lines 249-262: “Fix a finite measurable partition ...” and then require the cell-count inequality for every positive-length rho-grid interval and every cell.
- Definition `chi-regular-partitions`, lines 276-302: only Borel partition, representatives, the cost-variation bounds, and the good/exceptional coordinate comparisons are required. No canonical partition or fixed cell boundary is prescribed. The final sentence describes one construction, not an additional defining condition.
- Parameter hierarchy, lines 474-486: k,T,eta,gamma fixed; chi chosen small; Delta,rho,phi,delta then chosen; N last. All constants can depend on parameters to their left.
- Proposition `ub-first-moment`, lines 1817-1840: “Fix eta>0, then choose chi,Delta,rho,phi,delta according to the parameter hierarchy above, with the almost-like condition imposed for the chosen chi-regular partition.”
- Lemma `ub-regular-partition-interval-blocking`, lines 857-896: its proof invokes only the defining regularity bounds, finiteness, and the grid cell-count estimates. It converts them to estimates on arbitrary intervals with total error O(rho+phi)+o(1), not the original exact per-grid tolerance on every arbitrarily short interval.
- Randomized definition, lines 265-273: refers to “the finite partition and parameters fixed in the application.”

Thus the written proof supports selecting a profile-dependent regular partition as part of the fixed setup before N. It does not restrict the partition to be independent of mu. It also does not state an explicit formally quantified theorem of the form `forall regular partitions ...`; this must be made precise in the frozen declaration. The exact completed Lean first-moment theorem may be partition-polymorphic, may existentially choose its partition, or may hardcode one. Until that declaration is available, compatibility is a proof obligation, not a verified import fact.

The safe interpretation for an upper theorem proved from this sketch is:

    fixed profile and margin parameters
      -> choose one fine input partition and its tolerances
      -> for every sufficiently large N and every cut array satisfying
         those fixed input requirements, conclude the upper bound.

It is not:

    arbitrary already fixed partition P and cuts almost-like for P
      -> freely replace P by a finer partition after inspecting the cuts.

Refinement increases information required of the cuts. The replacement is legitimate only while choosing the original partition in the existential setup.

## 2. Pure finite counting transfer: exact interface

The first lemma should be independent of topology, integration, probability, and shuffles.

Data:

- A finite index set J of sampled columns.
- Finite coarse and fine cell index types C and F.
- Classifiers coarse:X->C and fine:X->F and a parent map parent:F->C satisfying coarse(x)=parent(fine(x)).
- A finite set V of fine cells designated as the boundary band.
- Two sample arrays p,q:J->X.
- An exceptional set Z subset J.
- A positive normalization lambda (later log N).
- Nonnegative target fine masses m_f and a nonnegative discrepancy epsilon.
- The mismatch implication: for each j, if coarse(q_j) differs from coarse(p_j), then fine(p_j) is in V or j is in Z.
- For every f, the input bound

      |#{j in J: fine(p_j)=f}/lambda - m_f| <= epsilon.

For c in C let F_c={f:parent(f)=c}, let b=card V, and let a_c=card F_c. Define the coarse target m_c=sum_{f in F_c}m_f and band target m_V=sum_{f in V}m_f. Then the conclusion is

    |#{j in J: coarse(q_j)=c}/lambda - m_c|
      <= (a_c+b)*epsilon + m_V + card Z/lambda.

Proof obligations are only disjoint finite sums and triangle inequalities:

1. Original coarse discrepancy is at most a_c*epsilon.
2. The perturbed coarse count differs from the original one by at most the number of original band samples plus card Z.
3. The band sample count divided by lambda is at most m_V+b*epsilon.

This exact inequality exposes every accumulated rounding error. It must not be replaced prematurely by “the same almost-like condition is preserved.”

### Time-grid specialization

For each time interval I in a fixed finite family G of positive-length intervals, set

    J_I = {j: j/log N in I},
    lambda = log N,
    m_f(I) = integral_I mu_t(D_f) dt,
    epsilon_I = phi_f*|I| + 1/log N.

Finite additivity of the profile measure gives

    m_c(I)=integral_I mu_t(C_c) dt,
    m_V(I)=integral_I mu_t(Band) dt.

Therefore, for every coarse c,

    |#{j in J_I:q_j in C_c}/log N - integral_I mu_t(C_c)dt|
    <= (a_c+b)*(phi_f*|I|+1/log N)
       + integral_I mu_t(Band)dt
       + card(Z intersect J_I)/log N.

No assertion about probabilities of q appears here. The conclusion holds deterministically for every perturbed array meeting the mismatch condition; a conditional concentration theorem can later provide that condition on its good event.

### Explicit tolerance absorption

Let R>=max_c(a_c+b), R>0, and let ell_min=min_{I in G}|I|>0. Given desired coarse tolerance phi_c>0, it suffices to require

    phi_f <= phi_c/(4R),
    integral_I mu_t(Band)dt <= phi_c*|I|/4 for every I,
    card(Z intersect J_I)/log N <= phi_c*|I|/4 for every I,
    log N >= 4R/(phi_c*ell_min).

Then the transfer proves the stronger discrepancy bound <=phi_c*|I|, and hence the manuscript's required <=phi_c*|I|+1/log N.

Usually Z is empty because all coordinates of all relevant conditional pile vectors are close simultaneously. The exception term remains useful if only selected columns are controlled. None of these tolerance requirements should be assumed in the final shuffle theorem independently: choose phi_f, choose the band, choose N0, and prove the concentration requirement.

## 3. Constructing a suitable coarse partition without assumptions on mu

Let D be the simplex with its relative topology, and define the finite integrated profile measure

    nu(A)=integral_0^T mu_t(A) dt.

This uses the measurability already necessary for the profile integrals. There is no need to assume that nu is atomless or that the profile has a density.

Construct a finite coordinate-box partition of mesh at most c*chi^2. Each interior coordinate threshold can be chosen to avoid atoms of the corresponding coordinate pushforward of nu: a finite measure has only countably many atoms, so every nonempty real interval contains an allowable threshold. Intersect the boxes with the simplex and assign threshold boundaries consistently (e.g. half-open boxes with the last box closed).

Let Z_boundary be the finite union, inside the simplex, of the chosen threshold hyperplanes. Then nu(Z_boundary)=0. Use relative boundaries: treating the whole ambient Euclidean boundary of the simplex as a cell boundary would incorrectly exclude profiles supported on faces or vertices.

The diameter bound gives chi-regularity for any chosen representative in a nonempty cell:

- The max-coordinate logarithm and psi_p(theta), theta in [2,4], vary by at most C_k*chi on cells of diameter O(chi^2).
- If a representative coordinate exceeds 2chi, every coordinate in that cell exceeds chi, and the logarithm difference is O(diameter/chi)=O(chi).
- If the representative coordinate is at most 2chi, every coordinate in the cell is at most 2chi+O(chi^2)<=3chi.

Consequently no mandatory threshold at exactly chi,2chi,3chi is needed. Imposing such exact thresholds could create positive boundary mass; choosing generic nearby box thresholds avoids this while meeting the definition.

This construction supplies a concrete coarse partition acceptable to the written first-moment argument. The first-moment proof should be instantiated for this partition, with later tolerances and N0 allowed to depend on it.

## 4. Choosing a thin band and the single fine input partition

For h>0 define a closed coordinate band around every selected threshold:

    Band_h = {p in D: |p_a-t|<=h for some selected threshold t in coordinate a}.

These bands decrease to Z_boundary as h decreases to zero. Since nu is finite and nu(Z_boundary)=0, continuity from above gives nu(Band_h)->0.

For the fixed finite time-grid family G, choose h>0 so small that

    nu(Band_h) <= (phi_c/4)*ell_min.

Then for every I in G,

    integral_I mu_t(Band_h)dt <= nu(Band_h)
      <= (phi_c/4)*ell_min <= (phi_c/4)*|I|.

The choice is simultaneous over every interval; no uniform-in-time density or continuity of mu_t is assumed.

Define the ONE original fine partition by splitting every coarse cell into its band and nonband parts:

    D_(c,0)=C_c intersect Band_h,
    D_(c,1)=C_c setminus Band_h,

discarding empty parts. There are at most 2*card C fine cells. It is a Borel partition, refines C, resolves band membership exactly, and still has the same diameter bound. Choose arbitrary representatives of its nonempty cells; the metric argument above proves its chi-regularity. Abstract chi-regularity alone need not be inherited under arbitrary changes of representative, so the inherited diameter bound is the clean proof.

Here a_c<=2 and b<=card C. Thus one can take R=card C+2, improving the rough R=2*card F bound. Crucially, making h smaller does not increase the number of fine cells in this construction, so there is no circular dependence between band mass and accumulated fine-cell errors.

If p is outside Band_h and ||q-p||_infinity<=h, no coordinate comparison to any threshold changes, so p and q have the same coarse cell. This proves the mismatch implication with Z empty. Only the fine classification of p must be known; q need not stay in the same fine cell.

## 5. Permissible quantifier order

An explicit consistent order is:

1. Fix k,T,eta,gamma and the profile mu; obtain the desired margin reserve.
2. Choose the first-moment regularity scale chi_c sufficiently small.
3. Choose a mesh-O(chi_c^2), nu-null-boundary coarse partition C as above. It depends on the fixed profile and chi_c, but not on N, cut realization, or exploration history.
4. Instantiate the first-moment theorem for C, choosing its Delta,rho,phi_c,delta in the prescribed hierarchy. All dependencies on the finite partition are fixed here.
5. Fix the actual absolute time-grid family G used for applying that theorem and compute ell_min>0.
6. Choose band width h from nu and phi_c,ell_min.
7. Define the fine input partition F by splitting C along Band_h. This is the ONLY empirical partition assumed of the original cuts.
8. Choose phi_f<=phi_c/(4R). Require original cuts to be almost-like for F with phi_f, as the original parameter choice in the upper-bound theorem.
9. Choose N0 large enough for the accumulated integer rounding errors and all conditional perturbation tolerances to be below h. Then quantify universally over N>=N0 and over all cuts satisfying the fixed input hypotheses.
10. For every exploration-generated large block, prove its actual conditional tail pile proportions are close to the original p_j. Apply the deterministic transfer to get the same coarse almost-like condition, and then invoke the already instantiated coarse first-moment theorem.

There is no adaptive partition depending on the sampled block, and no additional empirical requirement on the cuts beyond ONE chosen fine partition. Dependence of N0 on h and therefore on mu is harmless unless the intended theorem claims uniformity over all profiles; the source claims uniformity over cut sequences for a fixed profile.

If the first-moment theorem is only existential in its partition, without allowing selection of a null-boundary partition or proving that its selected partition has null boundaries, this order cannot be implemented directly. A partition-polymorphic theorem, or an inspected proof showing the coarse box partition can be selected, is required. The current TeX proof supports the latter, but the missing Lean declaration prevents verification.

## 6. Remaining precision issues not solved by the partition trick

### Local good-column threshold

Coordinate closeness does not preserve the exact threshold chi: a coordinate exactly chi can fluctuate below chi. Use a margin between the original good-column threshold and the first-moment threshold, selected before the freeze. For example, keep the original local condition at chi_g and instantiate first moments at chi_c=chi_g/2; if the conditional coordinate error is <=chi_g/2, every original chi_g-good column becomes chi_c-good. The fine partition can be constructed at the smaller mesh and is regular for both scales by the direct metric proof.

This does not require assuming more good columns than the original local condition gives. However, the parameter relationship must appear in the frozen setup. One cannot claim preservation with the same chi without proof.

### Time grids and very short moving intervals

The absorption of R/log N uses a positive minimum interval length independent of N. This is available for the fixed finite absolute rho-grid on [0,T], including its fixed final truncated interval. It remains available for every tail if the theorem only uses those same absolute grid intervals lying inside the tail.

It is NOT automatic for a grid newly anchored at every random birth time r, or for arbitrary clipped first/last intervals of lengths tending to zero with N. Nor does nu-null boundary imply a uniform relative band-mass bound for ALL arbitrarily short time intervals. A profile can spend very short time intervals entirely near a boundary.

The source interval-blocking lemma obtains an additive O(rho+phi)+o(1) error on arbitrary intervals. It does not state the same exact per-grid relative tolerance on every moving clipped interval. The frozen first-moment interface must specify the common absolute grid or explicitly use the already proved interval-blocking error. This is a scope issue, not grounds for adding uniform-in-time regularity of mu.

### Original N versus actual block size

The finite transfer above uses normalization log N and absolute times j/log N, matching the ambient-block notation in the TeX. If the completed first-moment theorem instead uses the conditional block size m as its base and times j/log m, a separate exact rescaling of the profile and grid is needed. The partition argument itself does not prove that normalization bridge.

### Conditional concentration and uniform first-moment constants

This construction assumes no probabilistic conclusion by definition. The proof must still establish uniform coordinate closeness of all relevant conditional tail arrays from the true residual-matrix law, with the stated conditional failure probability. For actual large blocks m>=N^xi and errors O(m^-c), fixed h is eventually exceeded by no good-event error, uniformly over blocks.

The first-moment conclusion and its N0 must be uniform over arrays having the derived coarse almost-like property. A declaration that proves a limit separately for each deterministic array is insufficient for averaging over the random conditional arrays.

## 7. Recommended frozen interfaces

The following mathematical interfaces are enough for the repair, with no weak-first-moment hypothesis:

1. `finite_refinement_perturbation_count`: exactly the finite counting theorem in Section 2, including R/log N accumulation.
2. `exists_profile_null_boundary_regular_partition`: for every finite integrated profile measure and sufficiently small chi, construct a finite regular coordinate-box partition with null internal boundary.
3. `exists_thin_resolved_refinement`: choose h and a finite regular refinement resolving Band_h, with target band mass small on a specified finite positive-length time-grid family.
4. `conditional_tail_coarse_almostlike`: combine uniform conditional coordinate closeness, the chosen one fine-partition hypothesis, and the counting transfer to conclude the coarse almost-like condition, on the already constructed good event.
5. `good_columns_transfer_half_threshold`: original chi_g-good counts imply conditional chi_g/2-good counts under sup-coordinate perturbation <=chi_g/2.
6. `apply_completed_firstMoment_coarse`: instantiate the genuine completed theorem at the predetermined coarse partition and smaller good-column threshold. This is an application, never an assumed theorem or placeholder.

The first three are purely constructive/finite-measure lemmas. The fourth and sixth remain dependent on the actual model conditioning estimates and the unavailable first-moment declaration. No global completion or freeze follows from the counting transfer alone.
