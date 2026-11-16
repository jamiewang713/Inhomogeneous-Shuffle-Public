# Independent revalidation of the newly present FirstMoment input

## Finding

The inspected Lean declarations do **not yet supply the manuscript's ambient shuffle-graph first-moment proposition**. They supply proved-form scalar inequalities, counting and entropy lemmas, and generic finite-graph aggregation theorems whose localization/class estimates remain explicit premises. They can be useful dependencies for that proposition, but importing them does not establish it under the manuscript's original cut/profile hypotheses.

This is a scope distinction, not a claim that these generic lemmas are mathematically invalid. The module comments accurately describe the limitation: Assembly says its results do not assert shuffle-graph localization or density estimates; Numerical says the model-to-scalar estimates remain explicit premises.

I read the source proposition independently at manuscript lines 1817-1916 and inspected only the new Lean declarations as implementation evidence. I did not edit code or another project's frozen contracts. Build/trust checks are being performed separately by the root agent; this report addresses statement strength.

## Snapshot inspected

All declarations below are in namespace `InhomogeneousShuffle.FirstMoment`.

* `FirstMoment.lean`: imports `FirstMoment.Numerical`, `.Counting`, `.Entropy`, and `.Assembly`; it declares no additional model theorem.
* `Assembly.lean` SHA-256: `40affb8d2498afa4915b99d49ccc28118e3d787ac1419ee94c4b105ad5f23d19`.
* `Numerical.lean` SHA-256: `b070f5a87d951c753e1bf2cc5974ca5423d04a66d2cb14174a3715d516a99bbf`.
* `Counting.lean` SHA-256: `1d0e6f283a4da437d615ae577f1b08ecd96bfa76aa11a1f8294e6bf3dd86a2cb`.
* `Entropy.lean` SHA-256: `066e6498b8f7e004050e99a72b32721d89cee78c49b4d732ca057735ef880aa3`.

These hashes identify the read snapshot; later declarations may change the assessment and should be revalidated.

## Intended input from the manuscript

`prop:ub-first-moment` fixes a positive eta and chooses the finite regular partition and parameters in the source hierarchy. For a fixed legal ambient prefix B_w with absolute birth time r and expected-size exponent b, it assumes:

1. The actual deterministic tail pile sequence is almost-mu-profile-like on the absolute time interval [r,T] for the selected partition.
2. It satisfies the stated local good-shuffle condition.
3. The source numerical margin FM(r,b,T,eta) holds.

It concludes for two independent shuffle graphs restricted to that ambient block that

E |E(G) intersect E(G')| <= N^(-delta_*),

where delta_*>0 depends only on the specified macroscopic parameters, with the required eventual/uniform quantifiers. The actual graph law is induced by independently sampled uniform fixed-count columns, sorted row strings, and adjacent equal strings. None of those model assumptions may be replaced by assumptions that localization or edge-density estimates already hold.

## What Assembly actually provides

### 1. `FiniteGraphLaw`

At line 19, this structure has:

* arbitrary finite sample space Omega;
* arbitrary finite edge universe M;
* nonnegative real weights summing to one;
* an arbitrary map `graph : Omega -> Finset M`.

It is a genuine finite probability-law representation. It does not specify fixed column counts, words, lexicographic sorting, path edges, an ambient prefix, a deck size, or a profile. It could represent the desired law after a separate construction and semantic proof.

### 2. `FiniteGraphLaw.expectedCommonEdges` and `expectedCommonEdges_eq_sum_sq`

`expectedCommonEdges` is the explicit product-weight sum of the intersection cardinality for two independent copies. `expectedCommonEdges_eq_sum_sq` (line 36) proves the correct identity

law.expectedCommonEdges = sum_m law.edgeMarginal(m)^2.

This formalizes the first displayed identity in the manuscript proposition's proof for arbitrary finite graph laws. It supplies no smallness estimate by itself.

### 3. `localized_sum_sq`, `localized_sum_sq_bound`

At lines 72 and 114, these are finite inequalities for arbitrary real arrays p,d,q and an arbitrary active-index function. They assume the per-edge localization inequality, nonnegativity, an active-index cardinality bound, and (for the bounded version) an error square-sum and each class square-sum bound.

They prove the algebra needed to aggregate already-established localized graph estimates. They do not define actual stable blocks or prove their localization property.

### 4. `expectedCommonEdges_bound`

At line 137 this specializes aggregation to `FiniteGraphLaw` and proves

law.expectedCommonEdges <= 2 D + 2 L * card(C) * U.

Its substantive premises include:

* `hactive`: card(active m)<=L for every edge m;
* `hloc`: actual edge marginal <= d(m)+sum_{i in active(m)}q(i,m);
* `hD`: sum_m d(m)^2<=D;
* `hU`: every class sum of sum_m q(i,m)^2 is <=U.

Thus `hloc` and `hU` contain precisely the localization and density aggregation that the source proposition needs to prove from the shuffle model.

### 5. `profileClass_sum_bound`

At line 157 this proves a class sum bound from three explicit assumptions:

* `hcard`: class cardinality <= N^(H+countLoss);
* `hf`: each class member's contribution f(x)<=N^(z(x)+loss);
* `hz`: each z(x)+H<=-margin.

It is useful once actual class cardinality, probabilistic density bounds, and numerical negativity have been proved. No actual class or probabilistic contribution is instantiated here.

### 6. `expectedCommonEdges_power_bound`

At line 177 this is the strongest named graph bound in the inspected module. In addition to all the preceding localization/class premises, it assumes

* `hDpow`: D<=N^(-d);
* `hLpow`: L<=N^ell;
* `hCpow`: card(C)<=N^c;
* `hUpow`: U<=N^(-a).

Its conclusion is

law.expectedCommonEdges <= 2 N^(-d)+2 N^(ell+c-a).

Here `N` is an independent real parameter; the theorem imposes no equation relating it to card(Omega), card(M), or an actual deck size. Its hypotheses also do not force d>0 or a>ell+c. This is correct for a general aggregation lemma, but it is not the source first-moment result merely because its name contains `power_bound`.

### 7. `two_power_terms_eventually`

At line 212 this proves that the preceding two powers are eventually bounded by N^(-delta) when supplied delta>0, delta<d, and delta<a-ell-c. It proves the final asymptotic arithmetic absorption, not the existence of such exponents from eta or the source parameter hierarchy.

## What the other modules provide

### Numerical

`largeIntegrand`, `smallIntegrand`, and `thetaInf` define scalar expressions and an infimum on theta in [3,4]. They are not definitions of the time profile, the actual integrals B_theta, or FM(r,b,T,eta).

`large_exponent_pointwise`, `large_exponent_variational`, and `large_exponent_negative` prove the large-block numerical inequality from explicitly supplied real inequalities named `hlen`, `hstable`, `hfluc`, `hmax`, `hentropy`, `htail`, and, where appropriate, `hmargin` and `hbudget`.

`small_exponent_pointwise`, `small_exponent_variational`, and `small_exponent_negative` analogously require `hparent`, `hfluc`, `hmax`, `hentropy`, `htail`, `hmargin`, and the error budget.

`singleton_exponent` and `singleton_exponent_negative` require `hmax`, `htail`, and the relevant scalar margin/error bound.

These are useful formalizations of the numerical part of the source proof. There is no declaration instantiating their real parameters by the actual c_L,c_F,c_E,H,S,Q of stable shuffle blocks or deriving their premises from actual regular-cell estimates and the source FM assumption.

### Counting

`SparseAssignment`, `BoundaryCode`, `ProfileKey`, `sparseCount`, and `profileCountBound` are explicit finite coding objects and counts.

`card_sparseAssignment`, `sparseCount_weighted`, `sparseCount_le`, `card_profileKey`, `sparseCount_exp_bound`, `profileCount_exp_bound`, and `profileCount_eventually` establish their cardinality/asymptotic estimates.

The bridge theorem `profile_card_le_of_injective` (line 133) still takes `encode : C -> ProfileKey ...` and `hinj : Function.Injective encode` as premises. No actual retained boundary/profile class C or its injective encoding is constructed in these declarations. `profileCount_eventually` assumes bounds on K(N), qb(N), and qe(N); those must be derived for the source's exceptional locations and retained profiles.

### Entropy

`word_mass_sum`, `card_mul_mass_le_one`, and `card_le_exp_of_mass` are finite product-law/constant-mass counting results.

`typeClass`, `typeEntropy`, and `type_class_card_le_exp_entropy` give a genuine exact finite type-class cardinality bound, including empty/incompatible requested classes. The latter theorem does not require extra compatibility assumptions.

The missing application is identifying each actual retained stable-block class as an injective/subset image of such an exact type class (including exceptional positions and singleton branches), and proving that `typeEntropy/log N` agrees with the source H exponent within the chosen error budget. The entropy theorem does not establish shuffle-graph density or localization.

## Exact missing model-to-theorem implications

The following are obligations to prove under the original source assumptions, not proposed new assumptions or extra fields in a replacement 'first-moment input'. Existing declaration names are given to make the gap precise.

1. **Actual law construction.** Construct the finite fixed-count shuffle matrix law, prefix restrictions/recentering, and the adjacent-equal-string path graph as an instance of `FiniteGraphLaw`. Prove that its `expectedCommonEdges` is the ambient expectation in `prop:ub-first-moment`.

2. **Actual stable decomposition.** Define the legal prefix tree, admissible boundary pairs, stable families, active block indices I, retained classes C, and class map. Prove the partition/localization properties rather than supplying arbitrary arrays.

3. **Localization implication.** From bad-profile reduction and per-edge stable localization, prove `expectedCommonEdges_bound.hloc` / `expectedCommonEdges_power_bound.hloc`, with q equal to actual block-edge probabilities and err an actual exceptional-probability bound. Prove `hactive` from the source's per-edge stable-block multiplicity control.

4. **Exceptional contribution.** Prove `hD` and `hDpow` from actual bad-event probability estimates uniformly over the edge universe; the number of edges must be included when converting a pointwise error to a square-sum.

5. **Actual profile encoding.** Construct the `encode` and `hinj` premises of `profile_card_le_of_injective`; prove the source exceptional-count/time-length bounds used by `profileCount_eventually`; derive `hCpow` and `hLpow` with an explicit loss budget.

6. **Block probability estimates.** Prove the source large-block, small nonsingleton, small singleton, and terminal singleton density estimates. These provide `profileClass_sum_bound.hf`; they are not consequences of its generic aggregation proof. They need the source hypergeometric concentration/anti-concentration and endpoint/localization arguments.

7. **Actual entropy application.** Connect retained classes to `type_class_card_le_exp_entropy` and establish `profileClass_sum_bound.hcard`, including zero-entropy singleton classes and the separate exceptional-profile encoding loss.

8. **Model-to-scalar inequalities.** Derive the `hlen/hstable/hfluc/hmax/hentropy/htail/hparent` premises of Numerical's `large_exponent_negative`, `small_exponent_negative`, and `singleton_exponent_negative` from the source model quantities. Define the actual profile integrals and prove the `hmargin` premises from FM(r,b,T,eta). The existing Numerical declarations keep these links as explicit premises.

9. **Per-class negative bound.** Combine items 6-8 through `profileClass_sum_bound` to prove `hU` and `hUpow`, treating all four source block cases rather than assuming one common U works.

10. **Parameter selection and ambient uniformity.** Derive positive d,a and sufficiently small ell,c from eta and the parameter hierarchy, obtain a positive delta satisfying `two_power_terms_eventually`'s strict inequalities, and state the eventual estimate uniformly over the admissible deterministic tails and ambient blocks. This must preserve absolute times and the source expected-size convention.

11. **Final source proposition.** State and prove a declaration whose hypotheses are the original actual-model almost-like, local-good, and FM hypotheses, and whose conclusion is the ambient polynomial first moment. It may call the existing generic lemmas after discharging items 1-10. No such declaration was present in the inspected modules.

After that, the upper-bound task still has its previously identified conditional self-reduction and partition-robustness obligations. A proved unconditional source proposition would be an input to those arguments, not an automatic conditional first-moment bound during exploration.

## Consequence for the upper-bound integration ledger

Update 'no FirstMoment Lean files found' to acknowledge the new modules and their reusable finite algebra/counting content. Do not mark the full source first-moment input available yet. A precise state is:

'FirstMoment scalar, coding, entropy, and generic aggregation declarations are present; their compilation/trust status is checked separately. A theorem identifying the ambient fixed-count shuffle graph and deriving the required localization/class estimates from the source hypotheses has not been found in this snapshot.'

Do not instantiate `expectedCommonEdges_power_bound` by adding its `hloc`, `hU`, or power estimates as new assumptions of the assigned upper theorem. That would replace the intended first-moment theorem by its unproved model-specific consequences and violate the no-assumption-change constraint.
