# LB-00 independent mathematical contract review

Reviewer: independent `math_review` agent. Date: 2026-10-01.

Scope: shared definitions, lane boundaries, endpoint hypotheses, and mathematical interface adequacy. No downstream theorem is proved by this report. Proposed declaration names below are specifications, not claims that a declaration exists or compiles. The final compiled signatures require a second review.

## Sources inspected and source agreement

The objective attachment, `PLAN.txt`, and all assigned lane mathematical scopes were read. The authoritative TeX has SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, agreeing with the objective/planning snapshot. I inspected the original `lean-lower-bound/FREEZE.md`, its README and `LowerBounds.lean`, the canonical `TimeProfile` freeze/Base/FixedCountModel and analytic-alternatives report, foundation Matrices/Graphs, and first-moment compatibility/profile interface notes.

The revised source's common setup explicitly states that displayed scalar time integrands are measurable and integrable (TeX lines 147–152). The old `TimeProfile.TimeLaw := ℝ → ProbabilityMeasure (Simplex k)` deliberately has no such property. Accordingly, the new macro endpoint is faithful to the revised ordinary-integral interpretation, but is a **strict hypothesis addition relative to the old arbitrary, totalized-TimeLaw freeze**. Preserve that distinction prominently.

## Dependency reconstruction

The lower proof is acyclic with these dependencies:

| Lane | Mathematical exports | Dependencies beyond shared definitions |
|---|---|---|
| 01 | Uniform fixed-count model, row relabelling, actual stable-sort law = independent graph-component mixture = chronological physical inverse law | None |
| 02 | All-positive-parameter thinning transform, residual prescriptions, prefix Bernstein/lower tails, simultaneous all-prefix event | None |
| 03 | Exact mixed factorial moments and residual versions, quantitative ratios, controlled Bonferroni polynomials | None |
| 04 | Relative-order independence, component ascent concentration/expectation, observable scan, conditional graph comparison | None |
| 05 | One-column tilt toolkit, empirical variational witness with rounding and bridge clearance | None |
| 06 | Supported rounded type classes, lower multinomial estimate, largest actual-mass bin | None |
| 07 | Two-sided A/B and margin transfer under explicit scalar integrability | None |
| 08 | Actual-model uniform marginal/pair relative collision estimates, family variance bound | 02, 03 |
| 09 | Constructed cold geometry, exact relative endpoints, reserve event, actual probabilistic localization | 02, 05, 06 |
| 10 | Largest-word test, many localized edges, physical empirical endpoint E | 01, 02, 04, 08, 09 |
| 11 | Explicitly integrable macro endpoint M | 07, 10 |
| 12 | Fresh-build and exact-assumption/dependency certification of E and M | 10, 11 |

Every lane depends on 00. In particular, 05/06/09 require no macro-profile transfer, and 04 may prove a conditional mixture theorem without assuming any identity for the actual shuffle. The actual identity must be discharged by 01 when 10 specializes that theorem. The upper first-moment program, random piles, and full cutoff are not dependencies.

Already checked candidates, requiring same-runtime imports/adapters: canonical cut/simplex/profile definitions; finite uniform assignment space and its finite integrals; deterministic full-word sorting/ranks/path graph components; old finite TV/event/Chebyshev facts; first/two-row word moments; increasing-run probabilities; finite cold algebra and the deterministic implication from localized keys to edges. They do **not** establish any of the new witness, localization, graph-law, all-prefix exponential, mixed occupancy, or two-sided transfer exports merely by import.

## Canonical representation and elementary adapters

Use `TimeProfile.Cuts k N K`, `ShuffleSample cuts`, `fixedCountPMF cuts`. A sample is an independent-uniform-column assignment model only after the product-uniform identity is proved; the underlying definition is the uniform PMF on the finite product type. Probabilities/expectations/variances are finite real-valued sums of PMF weights, and TV is `(1/2) * ∑σ |P(σ).toReal - Q(σ).toReal|`.

Use length-indexed prefixes `Fin m → Fin k` and full words `Fin K → Fin k` with the same lexicographic order. A full digit array plus prefix length is an acceptable adapter to canonical prefix predicates, but not a prefix-counting type: counting unconstrained arrays multiplies cardinality by `k^(K-m)`. For arbitrary position sets `I : Finset (Fin K)`, use `(j : I) → Fin k` or an explicit canonical extension, so an empty column set has one empty word. The same issue applies to exact type-class cardinalities.

Stable full-word sorting maps **sorted positions to original row labels**. Its pushforward of `fixedCountPMF` is the matrix inverse law. Define chronological physical forward shuffling independently as uniform interleaving of consecutive piles with order retained inside each pile, applied in chronological order; define its inverse pushforward unconditionally. The statement that this physical inverse is the matrix law is an LB-01 theorem, never a field in the physical model. Reversed chronological inverse sorts give earlier columns lexicographic priority. The uniform law's invariance under inversion and TV inversion invariance also need proved adapters before referring to forward/inverse equivalence.

Positions in Lean are `Fin N`. Put manuscript rank `rank i = (i.val : ℤ) + 1`. Prove:

* `L ≤ i.val ∧ i.val < U ↔ (L:ℤ) < rank i ∧ rank i ≤ U`.
* Equal-prefix ranks are exactly `[L,U)` in zero-based positions, and the count is `U-L`.
* Manuscript columns are `j.val+1`; manuscript `(a,b]` is Lean `a ≤ j.val < b`.

For integer finite sets `H`, represent integer-path edges by their left endpoint: `E(H)={z∈H | z+1∈H}` and `∂H={z | (z∈H) ≠ (z+1∈H)}`. Boundary is in the whole integer path, including boundary edges at ranks 0/1 and N/N+1. It is **not** the boundary restricted to the finite deck graph.

For `Hrel : Finset ℤ`, freeze

`clippedTranslate Hrel q = {i : Fin N | rank i - q ∈ Hrel}`.

This is exactly manuscript `(q+Hrel)∩{1,…,N}`. Using `i.val-q` instead would shift the cold set by one unless Hrel is separately redefined as the manuscript set minus one. The source's reserve slack allows either consistently translated representation, but the adapter must be explicit.

Define the observable ascent count on a deterministic `H⊂Fin N` and the scan

`∃ q∈{0,…,N}, X_(clippedTranslate Hrel q)(σ) > |E(clippedTranslate Hrel q)|/2 + s`.

It depends only on σ and the deterministic Hrel. The random chosen q used in the shuffle proof depends only on the graph, independently of the auxiliary uniform permutation.

## Exact empirical costs

Put `L=log N`, `K=floor(T L)`, `S_N=K/L`; assertions involving these costs use `N≥2`. For zero-based column j, its step interval is `(j/L,(j+1)/L]` and its profile is `cuts.profile hN j`. Define the following four bounded one-column costs using the canonical zero-coordinate conventions:

`a(p)=log(1/max_l p_l)`;

`ψ(p,α)=-log(∑_l p_l^α)`;

`I(p,α)=∑_{p_l>0} [p_l^α/(∑_a p_a^α)] log(1/p_l)`;

`H(p,α)=-∑_l q_l log q_l`, with `q_l=p_l^α/(∑_a p_a^α)` and zero terms zero.

A finite definition avoiding any temporal-integrability premise is obtained from the clipped primitive

`w_j(t)=min (max t (j/L)) ((j+1)/L)`

and `stepCost c r s = ∑_j (w_j(s)-w_j(r))*c_j`. This is the oriented step integral; on `0≤r≤s≤S_N` the weights are nonnegative overlap lengths. Define A_N/B_N/J_N/H_N by this same function applied to a/ψ/I/H. No macro `TimeLaw` occurs in these definitions.

For `a≤b≤K`, the exact grid adapter is

`stepCost c (a/L) (b/L) = (∑_{a≤j.val<b} c_j)/L`.

Additivity, zero-length values, sum of weights `s-r` on the domain, and clipping/column-time adapters are routine shared lemmas. The sharper analytic cost bounds belong to LB-05 (LB-06 may prove its own private needed bounds to remain independent).

Freeze exactly:

`β_N(s)=1-A_N(0,s)`;

`F_(α,N)(s,u)=((α+3)/2)*β_N(s)-B_(α,N)(s,u)-2*B_(2,N)(u,S_N)`;

`Λ_(1,N)=sup_{0≤s≤u≤S_N} inf_{3≤α≤4} F_(α,N)(s,u)`.

Use genuine real sSup/sInf over displayed nonempty sets. Boundedness/nonemptiness must be proved before their order properties are used. Do not replace Λ by existence of a witness or by a finite discretization unless an equality/controlled approximation is separately proved.

The macro definitions remain the existing `integratedMaxCost`/`integratedPsi` with the same formulas, β and Λ0=β(T), and the same real variational Λ1 over `[0,T]`.

## Witness and geometry: data separated from properties

An empirical witness data structure may contain only `m_s,m_u,b_N : ℕ` and `theta : ℝ`; derived s,u,b,J,H,Jt,Ht,h,Γ are definitions from the cuts and that data. The witness theorem, rather than input fields, proves the following predicate:

* `b_N=ceil(2*rho*L)`, `m_s≤m_u`, `m_u+b_N≤K`, `theta∈[3,4]`, and existence of two distinct χg-good columns in `[m_u,m_u+b_N)`.
* `κ=eta_f/1000`, `κ0=min(κ/100,1/1000)`, `Fθ(s,u)≥eta_f/2`.
* `J≤b/2-3κ`, and `theta=3 ∨ b/2-5κ≤J`.
* `h=b-J+H≥κ`, `H≤b-J-κ`, `Γ=2b-2J-2Jt+H+Ht`, `Γ-h/2≥κ`.
* `b-J-Jt≤β_N(S_N)<κ0`.

Witness existence has premises `eta_f>0`, `Λ1_N≥eta_f`, `β_N(S_N)<κ0`, positive rho/χg/γ, local-good and `2rho log k≤κ/100`. Geometry and E require the stronger budget with κ0. No witness is an input to the final E theorem.

A type-class data structure should carry the chosen supported integer counts and selected finite word bin (or enough raw choices to define it). `J*=binIndex/L`, `H*=log(card bin)/L` are definitions. Its output predicate includes nonempty bin, exact row counts and support, coordinate rounding errors ≤1, exact multinomial pre-bin cardinality, largest-bin property, selected probability ≥ξ, `card bin=N^H*`, and `e^-1 N^-J* < λ_x ≤ N^-J*`. The empirical I/H approximation is an explicit bound or a fixed-parameter epsilon/N0 predicate, not an unexplained o(1) field. Empty prefix/tail classes contain the empty word.

Geometry data carries prefix/tail families, their mass-bin indices, central bridge and two reserve bridge words; the maximal ambient prefix is canonically tie-broken. Hrel is defined, not independently supplied:

`Hrel=ℤ ∩ ⋃_{x∈P} N λ_(a_s) [t_x^rel,t_x^rel+λ_x)`.

Set `M=card Hrel`, `ell_p=b-Jp*`, `hN=ell_p+Hp*`, `ell_b=-log λ_bridge/L`, `zN=b-Jp*-Jt*-ell_b`, `gN=2zN+Hp*+Ht*`.

The geometry output predicate must include `ell_p≥b/2+2κ`, `Hp*≤ell_p-κ`, `hN≥κ/2`, `N^(κ/3)≤M≤N`, the uniform size exponent approximation, a fixed uniform bound `boundary(Hq)≤D sqrt M`, `gN-hN/2≥κ/2`, `zN≤2κ0`, exact `card Y=N^(Hp*+Ht*)`, and full mean interval `e^-2 N^zN<μ_y≤N^zN`. Reserve words differ from the central bridge at exactly their specified good column and satisfy the lex order and mean lower bounds. All selected/reserve digits have probability ≥`min(ξ,χg,1/k)>0`.

Localization is a separate probabilistic theorem about this constructed geometry. Its right endpoint identity necessarily includes `C(a_s)-μ_a`; the finite summed endpoint error is

`A*((2*sqrt(k*K)+1)*sqrt μ_a + 2*k*K+1)`.

On the simultaneous prefix event, reserves exceed that error by two with high probability. The conclusion is simultaneous localization for every selected full word (including all tail continuations), followed by an injective repeated-word-to-graph-edge assignment. A `localizedKeys` assumption is acceptable for a deterministic helper, never as an undischarged endpoint hypothesis.

## Typed lane export content to freeze

All quantities below refer to the shared concrete law, unless explicitly called a generic finite helper. These can be proposition-valued `Target` definitions, with no corresponding theorem/axiom/instance until their owner proves them.

* **01:** equality of `matrixInverseLaw cuts` and the pushforward of `fixedCountPMF cuts × uniformPerm` by `(S,π)↦componentSort(graph S,π)`; equality with `physicalInverseLaw cuts`; real event equality for every permutation event; inversion TV equality. No model contains these equalities as fields.
* **02:** for any actual prefix, `P(|C-μ|≥t)≤2 exp(-t²/(4(μ+t)))`, `P(C≤μ/2)≤exp(-cCh μ)`, `P(C<2)≤2exp(-μ/2)`, with `cCh=(1-log 2)/2`; all-prefix failure ≤`2*(K+1)*k^K*exp(-N^ε/8)` for the frozen N/ε domain; residual versions quantify over admissible positive-probability labelled-row prescriptions with population N-b and reduced counts. The shared conditioned law must be explicitly normalized on that event, not populated by a postulated product law.
* **03:** exact disjoint-row mixed factorial formula and multiplicative error `C1*(K+1)*R²/N` for distinct words, selected piles≥cN, K≤C log N, R≤N^(1/5), with constants/N0 before words/orders/cuts. For even m≥2, `0≤U_m(n)-1_{n≥2}≤D_m(n)`; central finite pair bound `ε(1+μ)(1+ν)e^(μ+ν)+3(d_m(μ)+d_m(ν)+d_m(μ)d_m(ν))`; rare coefficient is **1/3**, not 1/6.
* **04:** for arbitrary path G and H with |H|≤M, M,t>0, each centered one-sided tail≤`exp(-t²/M)`; mean≥`|E(H)|/2+|E(G)∩E(H)|/6-|∂H|`; scan≤`(N+1)exp(-s²/M)`; comparison failure≤`exp(-(r/6-d-s)²/M)` when its gap is positive. No boundary premise in the concentration theorem.
* **05:** one-column bounds `0≤H≤I≤log k`, `a≤I`, `ψ2≤2a≤2I`, `ψ4≥2ψ2`, `0≤ψα≤(α-1)log k`, entropy identity, α-continuity/monotonicity, and uniform eventual witness existence with the exact data/spec above. theta=4 shortening uses its ψ inequality, not a presumed bound on displacement.
* **06:** uniform eventual existence of the type/mass-bin data and complete specification for any I and α∈[2,4]. ξ is fixed before N0; `C*T*ξ*log(1/ξ)` is a fixed approximation budget, not o(1).
* **07:** selected-P scalar-integrability two-sided quadrature; uniform A/B error≤e, `|β_N(S_N)-Λ0(T)|≤e+C_k/L`, `|Λ1_N-Λ1(T)|≤13e/2+C_k/L`. The generic observable quadrature theorem also needs spatial integrability/continuity and temporal integrability of that observable, separately from the a/ψ-specific predicate.
* **08:** constants C1,N0 depending on fixed c,C only, then all cuts/K/families/words; `|p_w-f(μ_w)|≤C1*N^-0.01*f(μ_w)` and `|P(A_w∩A_v)-p_wp_v|≤C1*N^-0.01*p_wp_v` for distinct words. These multiplication forms avoid division before positivity. `Var Z≤EZ+C1*N^-0.01*(EZ)^2` for every deterministic finite family. No extra word-mean restriction.
* **09:** uniform constructed geometry and localization described above; right ambient error and reserve union bound retained.
* **10:** finite largest-word physical TV bound `1-exp(-cCh μ*)-(N-m+1)/m!` for `2≤m≤N`, `m≤μ*/2`; uniform empirical E; many-edge exponent may use δ=κ/5.
* **11:** M with the same chosen transfer partition, explicit scalar integrability, fixed positive margin and actual uniform quantifiers.

## Endpoints and quantifier order

Let βT abbreviate β_N(S_N). A useful exact empirical endpoint is the following single uniform alternative (alongside independently named largest/cold subtargets):

```text
∀ k≥2, T>0, bLargest>0, eta_f>0,
∀ chi_g>0, gamma>0, rho>0,
  2*rho*log k ≤ kappa0(eta_f)/100 →
∀ epsilon>0, ∃ N0≥2, ∀ N≥N0,
∀ cuts : Cuts k N (horizonDepth N T),
  (bLargest≤βT ∨
    (eta_f≤Λ1_N ∧ LocalGood cuts chi_g gamma rho 0 T)) →
  1-epsilon ≤ TV(physicalInverseLaw cuts,uniformPerm N).
```

The largest branch has no local-good premise. In the second branch, split internally at βT≥κ0, using the largest-word result there and the cold theorem otherwise. Having positive χg and γ only as fixed parameters in this combined statement is harmless; they impose no condition on the cuts in the first branch. A separately exported largest theorem should omit them entirely.

For M use a partition choice preceding its integrability predicate:

```text
∀ k≥2, T>0, eta>0,
∃ finite regular partition P, ∃ rho0>0,
∀ rho, 0<rho≤rho0, ∃ phi0>0,
∀ phi, 0<phi≤phi0,
∀ mu : TimeLaw k,
  ScalarTransferIntegrable mu P T →
  eta≤max(Λ0(mu,T),Λ1(mu,T)) →
∀ chi_g>0, gamma>0, ∀ epsilon>0,
∃ N0≥2, ∀ N≥N0, ∀ cuts : Cuts k N (horizonDepth N T),
  AlmostLike cuts mu P T rho phi →
  LocalGood cuts chi_g gamma rho 0 T →
  1-epsilon≤TV(physicalInverseLaw cuts,uniformPerm N).
```

The supplied rho0 must enforce the bridge budget with `eta_f=eta/2`, `κ=eta_f/1000`, `κ0=min(κ/100,1/1000)`. The transfer accuracy is fixed with `0<e<min(κ0/10,eta/100)`. Constants/N0 may depend on fixed rho,phi,χg,γ; all cut arrays and N-dependent witnesses follow N0. It is valid to strengthen the resulting threshold to be uniform in μ if proved, but unnecessary for the source statement. A sequence-specific Tendsto theorem alone is weaker than this contract.

`ScalarTransferIntegrable mu P T` should mean precisely:

1. `IntervalIntegrable (cellMass mu P i) volume 0 T` for each cell i of this P;
2. `IntervalIntegrable (profileMaxCost mu) volume 0 T`;
3. `IntervalIntegrable (fun t => profilePsi mu t alpha) volume 0 T` for every alpha∈[2,4].

Subinterval integrability follows from these on [0,T]. No macro J/H, differentiability, time continuity, or measurable-kernel condition is needed. The original same-cell nonmeasurable switching example shows this predicate does not follow from fixed-partition AlmostLike. Integrability of an unrelated partition cannot be silently transferred to/refined into P.

## Review outcome and residual checks

The source's repaired finite argument supports these interfaces, including the empirical/macroscopic split. The important contract risks are: accidentally defining away the physical law bridge; assuming rather than constructing a witness/localization; losing the rank +1 in clipping; counting unrestricted arrays as prefixes/type words; hiding scalar integrability in a renamed TimeLaw; and letting N0 depend on selected cuts/witnesses.

Pending before CONTRACT_READY: independent exact compiled-signature comparison, full declaration/axiom inspection for shared modules, same-runtime smoke build, and source/provenance/ownership receipt. This report approves the mathematical specification above, not any uninspected implementation and not the lower theorem itself.


## Concrete declaration proposal, second pass

`audit/LB00/WitnessGeometryProposal.lean` now proposes concrete declarations using the current `Shared.Model`, `Shared.Empirical`, and `Shared.Path` names. It is intentionally unbuilt, as requested, and is not an integration dependency. LB-00 should incorporate reviewed definitions into Shared and target definitions into its contract module, then compile and request the exact-type review.

Data and target separation is literal: `ColdWitnessData`, `RoundedTypeData`, and `ColdGeometryData` have no proof fields. The witness has only ms/mu/bridge length/theta; type data has integer counts and bin index; geometry has ambient/bridge/reserve words, distinguished columns, and type data. `WitnessSpec`, `TypeDataSpec`, `TypeApproximation`, `BridgeSpec`, and `GeometrySpec` are separate proposition-valued definitions. The selected class is derived from counts and the bin index, and largest-bin/smallest-index tie properties are proved outputs. The full family, Hrel, and h/z/g exponents are likewise derived, not arbitrary fields.

`WordOn k I := (j : I) → Fin k` ensures unused columns never multiply family sizes. `wordOnList` uses ascending column order for lexicographic comparisons. Empty I has its single empty function. The proposal's `prefixAt` is total using `min m K`; every substantive witness/endpoint contract separately proves the intended m≤K, so this totality convention must not mask missing bounds.

Owner targets are `LB05Target` (one-column toolkit, empirical tilt identities/bounds, witness existence), `RoundedTypeTarget`, and `LB09Target` (relative endpoints, deterministic geometry from any proved witness, uniform localization, and existence directly from empirical premises). Each only mentions shared definitions and propositions, so first-stage lanes 05/06 compile statements independently; neither assumes the other's proof. LB-09's intermediate geometry/localization can consume proved specifications, while its concrete target `ColdGeometryFromEmpiricalTarget` has no witness or localization input. There is no axiom or theorem asserting these targets.

The proposed geometry makes two source asymptotic statements quantitatively stronger but valid by increasing its uniform threshold: `exp(-2)*N^h ≤ M ≤ 2*N^h` and `boundary(Hq)≤4*sqrt M`. These replace the source's unspecified M=N^(h+o(1)) and boundary O(sqrt M), not its mathematical rate. The interval count bounds give M between `(exp(-1)*N^ell-2)*card P` and `(N^ell+2)*card P`; ell≥b/2+2κ and b≥4κ make the stated factors hold uniformly eventually. Then `Hp≤ell-κ` and clipping's extra two boundary edges give the fixed constant 4 uniformly eventually. If LB-00 elects different explicit constants, record that quantitative interface revision before freezing.

The proposal retains both empirical type approximation errors at `min(κ,κ0)/1000`; this is a fixed budget chosen before N, smaller than the source's permissible `min(κ,κ0)/100`. It does not demand these errors vanish at fixed xi. The type theorem explicitly isolates a spatial budget `Ctype*T*xi*log(1/xi)` and a rounding budget `Cround*(log(log N)+1)/log N`. `Ctype` is fixed by k and regularity constant, while `Cround,N0` are fixed by k,C,T,xi and cell count before the partition, N, cuts, I, and tilt. This uniformity is valid because no class estimate uses the locations or shapes of the cells beyond regularity and their number.

The exact relative right-endpoint target includes the ambient fluctuation and the source constant `A*((2*sqrt(k*K)+1)*sqrt(muA)+2*k*K+1)`. The concrete localization target quantifies cuts, witness, and geometry after N0, and its event covers every selected full word simultaneously. The rank shift follows `clipTranslate` unchanged.

Remaining review work: compiler elaboration of this proposal, required empty-word/empty-set definitional adapters, exact imported theorem axiom closure, and final target comparison after incorporation. No build or cache changes were made by this reviewer.

## Final mathematical review of the incorporated target types

This pass inspected the actual declaration bodies in `Contracts/v1/Endpoints.lean`, `AdditionalFinite.lean`, `ModelThinning.lean`, `FactorialOccupancy.lean`, `Ascent.lean`, and `WitnessGeometry.lean`, together with the shared Model/Empirical/Path/Statistics/Geometry definitions they use. No builds were run by this reviewer. The approval below is mathematical statement/representation approval, contingent on the coordinator's routine elaboration/build checks; it is not evidence for any pending theorem.

### Endpoint verdict

**Approve `RiffleLowerV2.Targets.EmpiricalCombinedTarget` as E.** It quantifies k,T,two positive margins, local-good parameters and accuracy before N0, then all N and all actual `Cuts`. Its conclusion is the half-L1 TV lower bound for `physicalInverseLaw`, the independently defined chronological physical inverse law. `EmpiricalAlternative` places the *whole* local-parameter restriction and `LocalGood` inside the second branch. Thus even invalid cold parameters do not restrict the largest-word branch. This is slightly cleaner than the earlier proposal and mathematically sound. The cold branch fixes κ/κ0 through etaCold and requires positive rho and `2*rho*log k≤κ0/100`; the terminal-beta split is internal to the proof. No `TimeLaw`, graph-law equality, witness, concentration, localization, or TV property is an input. The separately named `LargestOnlyTarget` and `ColdOnlyTarget` expose the two source obstructions accurately.

**Approve `RiffleLowerV2.Targets.MacroscopicIntegrableTarget` as M.** The transfer partition and regularity scale are chosen before the SAME-P `ScalarIntegrable` premise. The mesh threshold enforces the cold budget using etaCold=eta/2. For each fixed positive rho within that threshold, the frequency threshold is chosen; phi, positive good-column threshold/density, accuracy and the fixed profile all precede N0. N and every cut array follow N0. The placement of the macro margin as an implication after N0 is harmless: it is a fixed property of the profile, and in the false-margin case the statement is vacuous. It adds no cut-dependent threshold.

The exact additional M premise is interval integrability on [0,T] of this P's cell masses, `profileMaxCost`, and `profilePsi` for each alpha∈[2,4]. There is no macro J/H premise, kernel measurability, time continuity/differentiability, or positive lower bound on all piles. Relative to the authoritative revised manuscript's explicit ordinary-integral convention, this is the minimal used part of the declared regularity. Relative to the original `TimeProfile` freeze, it is an explicit strengthening; it cannot be inferred from old fixed-partition `AlmostLike` and does not certify the original unchanged arbitrary totalized-TimeLaw statement.

`ProfileTransferTarget` selects P before asking for its scalar-integrability premise and exposes dependence on fixed rho/phi. Its uniform A/B statements retain every interval endpoint and tilt after N0. `MarginTransferTarget` is an honestly conditional finite helper, while complete transfer must construct its error premise. The coefficient 13/2 is exact. The terminal coefficient 14 is safe: on the common domain the terminal B2 tail contributes at most `2 log(k)/L`; projecting s,u to min(s,S),min(u,S) changes the macro F by at most `(7/2+6+2) log(k)/L = (23/2) log(k)/L`, using a≤log k, ψ_alpha≤3log k and ψ_2≤log k. Their sum is `27/2 log(k)/L`, below the frozen 14. The beta terminal constant log(k)/L is also valid.

### Finite-target review

| File / target group | Verdict and exact checks |
|---|---|
| `ModelThinning`: column independence, graph representation/event identity, physical bridge, inversion TV | Approved. These are pending conclusions about concrete laws, not assumptions packed into definitions. The graph mixture independently samples the uniform permutation. The physical definition composes chronological forward interleavings and then inverts; the bridge asserts equality of laws, not pointwise equality of two differently indexed samples. |
| `AdditionalFinite`: row relabelling, stable ties, prefix ranks | Approved. Relabelling acts simultaneously on original labels in each column. Stable ties are ordered by original label. Prefix cuts are `[L,U)` in Fin N, matching the proved one-based `(L,U]` adapter. |
| `ModelThinning` and `AdditionalFinite`: subset transform, successive thinning, prefix tails | Approved. The transform includes every s>0 and requires M>0 with sizes≤M. Empty columns and zero/deterministic pile proportions are included. `PrefixTails` uses exactly the manuscript's Bernstein denominator and Chernoff constant. |
| `AllPrefixConcentration` / `PrefixFailureUniform` | Approved. The finite error is `2*(K+1)*k^K*exp(-N^epsilon/8)` and the eventual threshold is uniform in every allowed K. Absence of k≥2 from the finite target is harmless: k=1 is deterministic, and k=0 with N≥2 forces K=0 if such cuts exist, also giving zero failure. |
| `ResidualLaw` | Approved. It requires distinct prescribed labels and positive probability; residual sizes are exactly N-b and the reduced digit counts. The event-level identity allows every bijective enumeration of unused labels. Nothing asserts unchanged populations, means, or unproved residual independence. |
| `ExactJointFactorial` / `ResidualJointFactorial` | Approved. Distinct complete words give disjoint labelled-row requests. The total requested order is bounded by the relevant population, preventing zero falling-factorial denominators. Natural subtraction in the residual occupancy is correct on the conditioned event because prescribed copies are actually present. |
| `RelativeJointFactorial` | Approved. D,N0 depend only on fixed positive c,C, preceding k,K,family size, words, orders and cuts. This stronger uniformity in k/family size is valid: only total request count and the selected pile lower bound enter the ratio estimate. K=0 and total order 0 are included. |
| Bonferroni/central/rare targets | Approved. Even truncation m≥2, moments through total degree 2m, the pointwise product remainder, and factor 3 are retained. The rare third-factorial coefficient is 1/3. The source's rejected 1/6 and tail-probability-only remainder argument are absent. |
| `UniformOccupancy` | Approved. Its marginal and distinct-pair estimates are multiplication-form relative errors, including arbitrarily rare means. No independent-occupancy or extra mean hypotheses occur. The concrete family variance bound uses the same uniform D. |
| Relative-order independence, boundary comparison, Bernoulli MGF | Approved. Every prescribed relative order comes from a permutation, so it is consistent. Empty disjoint blocks are also valid: their factorial/binomial factors are 1. The Bernoulli estimate uses a genuine event under a PMF. |
| Ascent targets | Approved. Concentration is for the actual component-sorted statistic, with no boundary premise. One-sided constants, expectation `e/2+r/6-d`, infinite-integer-path boundary, scan union factor N+1 and positive comparison gap agree with the source. The uniform graph-scan target quantifies all H0,G after N0 and does not assume any actual-shuffle representation. |
| `FiniteLargestWordTV` | Approved. It concerns the physical inverse law and uses a contiguous-run conclusion through its pending proof. Natural `(N-m+1)` is safe under m≤N; m≥2 and m≤μ*/2 match the source. No macro/local-good premise is present. |

The public type inventory need not repeat every easy consequence as a separate theorem. For strict lane-to-prompt bookkeeping, LB-03's residual relative-moment and residual-mean-ratio estimates, LB-04's two-sided tail, and LB-10's many-edge threshold should be recorded as lane-owned proved helper obligations if they are not separately named contract targets. They are consequences to prove from the frozen inputs, not new final premises. This is an export-ledger completeness note, not a false statement or a mathematical blocker to this foundation freeze.

### Incorporated witness/geometry review

`Shared.Geometry` and `Contracts.v1.WitnessGeometry` retain the reviewed data/specification separation and the uniform quantifiers. No data structure contains witness inequalities, localization, or other target proof fields. `ColdGeometryFromEmpiricalTarget` existentially produces both W and G directly from empirical margins/local-good. The intermediate deterministic geometry and localization targets may consume their separately proved specs, so the source argument can be assembled without assuming its own conclusion. First-stage 05 and 06 targets depend only on shared definitions; their statements do not assume one another's results.

The exact witness constants eta/2, 3κ, 5κ, κ, κ0, bridge ceiling, bridge clearance, tilt interval, and terminal mean comparison are retained. The type words use only their actual selected columns. Exact class cardinality, selected-mass interval, selected-bin tie rule, the fixed xi error budget, and the rounding error are explicit. The source lower multinomial count remains an actual proof obligation of `RoundedTypeTarget`; it is not inferred from an old upper bound.

The proposed fixed geometry factors remain valid. Let Q=card(prefix class). Disjoint selected probability intervals give

`(exp(-1)*N^ell_p-2)*Q ≤ M ≤ (N^ell_p+2)*Q`.

Since Q=N^Hp, ell_p=b-Jp*, Jp*≥0 and ell_p≥b/2+2κ imply b≥4κ and ell_p≥4κ. Thus uniformly eventually `exp(-2)*N^h≤M≤2*N^h`. The source lower exponent M≥N^(κ/3) follows from h≥κ/2 and the fixed lower factor. For boundaries, clipping adds at most two edges, while `Hp≤ell_p-κ` gives `Q/sqrt(M)≤exp(1)*N^(-κ/2)`. Hence `2Q+2≤4sqrt(M)` uniformly eventually. No assumption that adjacent intervals stay disconnected is needed; merging only decreases the boundary.

The finite relative right-endpoint identity includes the ambient `C(a)-μ_a` term. Empty suffixes yield the correct lower endpoint 0 and upper count C(a). The localization event uses `clipTranslate` with manuscript rank i+1 and proves every selected full-word copy lies in the same graph-dependent translate. The repeated-word-to-edge inequality is part of the proved event output. The two-unit reserve slack remains required in the future proof, not silently removed by the zero-based representation.

### Mathematical freeze approval

**APPROVED for LB-00 mathematical contract freeze**, subject to routine successful Lean elaboration/build and the coordinator's source/provenance checks. No unresolved false target or missing endpoint hypothesis was found. All mathematical targets remain unproved at this setup stage. This approval does not certify E, M, an actual graph-law bridge, or any downstream lane as already proved.

The following SHA-256 values identify the inspected pre-freeze snapshot. If content changes, record the change and recheck the affected statement; do not treat this list as a historical contract hash to regenerate.

```text
ee995fe56f4815ec78d6d2bd0d76ed4aecb357883417a57958d0dd3ae19df0c0  Contracts/v1/Endpoints.lean
b94a1cb35d7204e4e6f0c8dbb277ebc471ec16307a38d2351ef290de6da20869  Contracts/v1/AdditionalFinite.lean
bdb0c4c3af301658c9798d191b3dfef1ac34d9df02fb988b1c10214d6b039288  Contracts/v1/ModelThinning.lean
80be112ec4fe3b811738bcb75a0aa29b26ef31d7bafd5d264fbee8ba21f7253d  Contracts/v1/FactorialOccupancy.lean
3816a1346b6f770837169835f93abc02a85f14c5f6c4d1d9a748f9d17602ab2b  Contracts/v1/Ascent.lean
bbd3f28678e95ace37f07c0d993992f20fd4dc4d565ccbc11d0b8a4f1ba822bc  Contracts/v1/WitnessGeometry.lean
cceadf1b4a5be2f412fe15a9b52b7b7f3c67bfa6d19270955f7c338f01e90930  RiffleLowerV2/Shared/Model.lean
84ea013c6f9c64073700be1dced470f11fa30a9b3d0b79a59dde63a099cf817e  RiffleLowerV2/Shared/Empirical.lean
513afea203a5ad1a3b851fdb8317b4f6473d2c54e1c0466139b349530563acbf  RiffleLowerV2/Shared/Path.lean
dd57ff2f4bbac3e26176809ee15081b58510b041e6dee418f65d31d4fc26fb69  RiffleLowerV2/Shared/Statistics.lean
73d896e31e387a515e58a166ff8e6c2a5eadda9fc952e3974dc9bbc6becc2e6c  RiffleLowerV2/Shared/Geometry.lean
2a53576620795bd338548419c23193473cc0829b4a0f88dc5cbd074ba03c5b84  ../../lean-lower-bound/FREEZE.md
1e911c5b729f677b62dc4c6517c0c79a11683baee9a5aad5c4e8978bcefebcfa  ../time_profile/FROZEN_CONTRACT.md
672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d  ../../time_inhomogeneous_riffle_shuffle_unified_article.tex
```

## Final additive-interface review before immutable freeze

I read `Contracts/v1/TransferFinite.lean` and `Contracts/v1/AssemblyInputs.lean` and compared their expanded target bodies with the compiled entries in `audit/LB00/public-exports.json`. This covers `GenericQuadrature`, `JointPsiContinuity`, `residualWordMean`, `ResidualRelativeFactorial`, `ResidualMeanComparison`, `ConditionalCollisionStability`, `ComponentConcentrationTwoSided`, `MaximalMeanIdentity`, `CollisionChebyshev`, and `ManyEdgesTarget`. No build was run and no file outside this report was edited during this review.

**All additive interfaces are mathematically approved.** They address the earlier export-ledger note without changing either endpoint's hypotheses.

* `GenericQuadrature` explicitly supplies spatial continuity, bounded nonnegative f, cell oscillation, integrability of the SAME partition's cell masses, and temporal integrability of this particular scalar observable. Thus it does not improperly apply the a/psi predicate to arbitrary f. Its finite error is the source's `2T omega + M m phi T + 4M rho + [4Mm(T/rho+2)+6M]/L`; the final 6M includes the 2M/L conversion from column sums to step interpolation. It allows nonnegative phi/omega/M, including zero, while requiring T,rho>0 and N≥2. No time-kernel assumption is introduced. `JointPsiContinuity` is only continuity on the compact simplex×[2,4], including zero coordinates, and is valid.
* The compiled `residualWordMean` is a REAL product with population factor N-b and real divisions by N-b, while each count subtraction is natural subtraction. The positive-probability prescription and distinct-label assumptions ensure these subtractions describe actual remaining counts. `ResidualMeanComparison` has relative error `D*(K+1)*b/N`, with fixed c,C,b0 preceding D,N0 and all cuts/prescriptions/words following N0. At b=0 it asks for exact equality, which is correct. K=0 gives means N and N-b, also consistent with that error.
* `ResidualRelativeFactorial` permits total order R≤N^(1/5), rather than `(N-b)^(1/5)`. This is valid, not an unnoticed domain error: fixed b≤b0 and sufficiently large N give N-b≥N/2, R≤N-b, and residual requested piles≥cN/2. The same log falling-factorial argument therefore gives error `D*(K+1)*R²/N`, with D depending on c,C,b0. It must be proved using those quantitative estimates rather than mechanically invoking a residual theorem restricted to R≤(N-b)^(1/5).
* `ConditionalCollisionStability` tests the **deleted-row occupancy**, subtracting every prescribed occurrence of the tested full word. This makes it correct even when the prescription itself contains that word. It compares against f(original mean) with a relative N^(-1/100) error. The residual occupancy theorem applies with modified fixed c,C, and the residual mean comparison plus `0≤t f'(t)/f(t)≤2` transfers to the original mean, uniformly even for rare words. Positive conditional-event probability is explicit; there is no hidden event-independence premise.
* `ComponentConcentrationTwoSided` has exactly `2 exp(-t²/M)` and the same concrete component ascent statistic. It follows by union of the already frozen one-sided events without a boundary assumption. `MaximalMeanIdentity` explicitly constructs a canonical maximal full word and states both exact mean equalities, for arbitrary finite K and N≥2. It assumes no local-good/profile regularity.
* `CollisionChebyshev` is the variance bound divided by `(t EZ)^2`: `1/(t² EZ)+D*N^(-1/100)/t²`. It correctly requires t>0 and EZ>0, but no unnecessary t≤1. D,N0 precede every cut array, family and t, giving the promised family-uniform concentration.
* The final source form of `ManyEdgesTarget` uses the **exact translate** `q*=lowerRank (prefixAt W.ms G.ambient) omega`, matching `lem:many-edges`. I separately inspected the last refinement from an existential successful q to this exact q*. Its edge exponent is `1/2+κ/5`; M≤N and the available `sqrt(M)*N^(κ/4)` collision bound provide the necessary positive slack. Witness/GeometrySpec are legitimate proved inputs to this intermediate theorem; neither endpoint acquires them as external assumptions. The constants and accuracy precede N0, and all cuts/witnesses/geometry follow it.

The public compiled snapshot inspected initially still displayed the preceding existential-q variant of `ManyEdgesTarget`; all other listed compiled values matched the new source. The exact-q* refinement is mathematically approved and requires only the coordinator's normal final rebuild/export refresh. The report does not treat the stale exported q statement as evidence of that final elaboration.

I also rechecked the current shared Geometry definitions and the unchanged endpoint/empirical definitions. The change in Geometry's hash is documentation-comment normalization around its definitions, with no changed mathematical clauses. The current E/M type approval and explicit M integrability qualification remain in force.

**Final verdict: ready for immutable LB-00 contract freeze after the normal final build/export refresh. No mathematical blocker remains. All downstream target proofs remain pending, and no endpoint proof is claimed.**

Exact SHA-256 snapshot for this final additive review:

```text
fd67fc92015806b8cc78d6b1f4a558ed512a41f818c732435e7e59e664e8b933  Contracts/v1/TransferFinite.lean
fd005b12cc24ebab117cf08b244d28cef07c31ce02a4d429625a7e92c1e874ea  Contracts/v1/AssemblyInputs.lean
cb992d0297bcf75ada15ff6154a146caadfa3d984629aafd70f74feef6bfbb09  RiffleLowerV2/Shared/Geometry.lean
ee995fe56f4815ec78d6d2bd0d76ed4aecb357883417a57958d0dd3ae19df0c0  Contracts/v1/Endpoints.lean
84ea013c6f9c64073700be1dced470f11fa30a9b3d0b79a59dde63a099cf817e  RiffleLowerV2/Shared/Empirical.lean
```

The earlier compiled-export snapshot read for this review had hashes `e711446612cdf0a8ca0420d4da10492597fd3b20ded8bd228b122f50edc6bca8` (`audit/LB00/public-exports.json`) and `263d30c6407c5eef7f306c192bccc3c4dae3a3cd68e0849c85e740203a329875` (`Contracts/v1/EXPORTS.md`). These identify the reviewed snapshot; they are not asserted to be the final refreshed export hashes.

## Refreshed-export confirmation

The coordinator reports the final full build and axiom audit `BUILD_OK` with zero errors. I independently reread the refreshed compiled `ManyEdgesTarget` value: it now explicitly clips at `lowerRank (prefixAt W.ms G.ambient) omega`, with the exact κ/5 excess exponent. This resolves the stale-export note above. The source hashes remain unchanged from the approved final additive review.

```text
fd005b12cc24ebab117cf08b244d28cef07c31ce02a4d429625a7e92c1e874ea  Contracts/v1/AssemblyInputs.lean
fd67fc92015806b8cc78d6b1f4a558ed512a41f818c732435e7e59e664e8b933  Contracts/v1/TransferFinite.lean
2c3aec14d56e7eab2d175e9e1fb12d9bab3f65ce7bbb3d7e02aa3880932f64e4  audit/LB00/public-exports.json
ccdc854ed8b5a545de6ac3f719ac6367706dfd85f73f29f8620f0df20cbd9da1  Contracts/v1/EXPORTS.md
```

**Final mathematical contract approval confirmed for this hash-bound snapshot.** No unresolved mathematical or stale-export qualification remains. This certifies the shared foundation and the correctness of the pending target statements, not proofs of E, M, or other downstream targets.
