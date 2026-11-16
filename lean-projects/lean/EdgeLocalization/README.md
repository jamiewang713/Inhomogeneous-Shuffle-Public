# Edge localization: verified finite shuffle model and collision estimates

This project contains 137 verified finite theorems: the original 33 and separately frozen addenda for collisions (58), occupancy conditioning (7), independent-copy overlap (6), exact source exponents (15), and ambient-relative coordinates (18). It constructs the actual independent uniform fixed-column shuffle law, sorts its rows, and proves exact internal-edge and density bounds. The complete requested asymptotic theorem collection remains unfinished.

The whole-source reread identifies the small-branch quantity needed by the upper proof as an entropy-weighted shared-edge contribution. Exact collision counting supplies a route to that contribution under the existing model. This does not prove the printed stronger spatial factor involving `c_F`; the endpoint, large-block, and sharper small non-singleton issues are documented separately.

The original mathematical sources are unchanged. No missing analytic estimate is stored as an assumed field or an unproved project theorem.

## Lean contents

- `EdgeLocalization/FiniteLaw.lean`: F01–F13, exact finite probabilities, expectations, and squared-probability sums.
- `EdgeLocalization/Deck.lean`: F14–F21, prefix edge containment, occupancy domination, and injection of internal edges into collision pairs. Empty and one-card decks are explicit.
- `EdgeLocalization/Density.lean`: F22–F25, squared edge probabilities bounded by expected internal edges, occupancy, and collision pairs. The occupancy bound is the finite core of the terminal singleton estimate.
- `EdgeLocalization/FirstColumn.lean`: F26–F28 and F31–F32, existence of balanced fixed-count columns, exact endpoints, positive side masses with zero residual sampling slack, and a zero variance numerator.
- `EdgeLocalization/EndpointObstruction.lean`: F29–F30 and F33, fixed endpoints have atom one under every finite law; intersecting an endpoint event with a good event gives exactly that good event's probability.
- `EdgeLocalization/Collision/FiniteLaw.lean`: constructed uniform/product laws and finite event factorization.
- `EdgeLocalization/Collision/Column.lean`: feasible fixed-count columns, row exchangeability, and exact one-/two-label probabilities with the without-replacement correction.
- `EdgeLocalization/Collision/Model.lean`: the actual matrix law, raw rows, prefix and tail factors.
- `EdgeLocalization/Collision/Rows.lean`: actual lexicographic sorting, vector/list bridges, and occupancy/collision-count invariance under row permutations.
- `EdgeLocalization/Collision/Matrix.lean`: exact prefix probabilities, expected occupancy, expected unordered collision counts, and factor comparisons.
- `EdgeLocalization/Collision/Estimates.lean`: the final exact internal-edge and density bounds, including every deck size.
- `EdgeLocalization/Conditional/Model.lean`: the actual prefix/suffix matrix equivalence, retaining all N original labels in both column groups.
- `EdgeLocalization/Conditional/Split.lean`: finite expectation splitting, exact suffix factors, and deterministic prefix occupancy.
- `EdgeLocalization/Conditional/Counts.lean`: counting pairs in arbitrary occupied-label sets and the exact collision expectation after fixing a prefix array.
- `EdgeLocalization/Conditional/Estimates.lean`: exact occupancy-slice collision identities and internal-edge inequalities, including null and impossible slices.
- `EdgeLocalization/Overlap/FiniteLaw.lean`: a constructed independent product law, finite Fubini, rectangle probabilities, and expected intersection counts.
- `EdgeLocalization/Overlap/Edges.lean`: density equals expected same-position overlap in two independent copies; the proved matrix bounds apply to that overlap.
- `EdgeLocalization/Exponent/Model.lean`: source-defined ambient size and tail exponents, selected-prefix legality, and the computed signed ambient normalization error.
- `EdgeLocalization/Exponent/Mean.lean`: exact logarithmic mean identities and `μ_x = N^(c_L + ε_w)`, deriving positivity from legality.
- `EdgeLocalization/Exponent/Tail.lean`: the square-proportion tail product equals `N^c_E`, and bounds the exact collision factor; full-length empty-tail identity.
- `EdgeLocalization/Exponent/Estimates.lean`: fourth-power, small-case, direct mean, and terminal density bounds with their exact ambient error terms.
- `EdgeLocalization/Relative/Model.lean`: relative internal edges, squared relative density, and the actual zero-based ambient cut.
- `EdgeLocalization/Relative/Deck.lean`: arbitrary-shift cardinal domination, zero-shift checks, and a proved bijective recentering of every actual child-block internal edge.
- `EdgeLocalization/Relative/Density.lean`: bounds valid for sample-dependent shifts, the exact independently recentered overlap identity, and actual-matrix mean/tail bounds.
- `EdgeLocalization/Relative/Estimates.lean`: the same exact source-exponent consequences in the paper's ambient-relative coordinates.

The finite law contains only nonnegative weights with total one. The uniform-column and independent-column properties are constructed and proved, rather than supplied as assumptions. For prefix mean `μ` and exact tail coincidence factor `q`, the implementation proves

```
E[collision pairs] = choose(N,2) * prefixPairFactor * q
E[internal edges] ≤ μ²q/2
edgeDensity ≤ μ⁴q²/4
edgeDensity ≤ μ.
```

The last inequality includes terminal full-word prefixes. The sharper coefficient `(N−1)/(2N)` is also proved. Zero and one-card decks, empty columns/prefixes/tails, empty alphabets where feasible, zero piles, and ties in sorting are included. These density bounds are separately proved for absolute coordinates and ambient-relative coordinates in the actual shuffle model.

Writing Z for sorted prefix occupancy, C for collision count, E for internal-edge count, and Q for the exact tail factor, the additional occupancy identities are

```
E[C * 1_{Z=q}] = choose(q,2) * Q * P(Z=q)
E[E * 1_{Z=q}] ≤ choose(q,2) * Q * P(Z=q).
```

They hold for every natural q, without a positive-probability premise. The proof fixes all prefix columns, integrates over the original-population tail law, and then averages the indicator. It does not substitute q for the sampling population N. Stable-profile summation, spatial localization, and the exploration-conditioned residual model remain outstanding.

For N≥2 and a legal extension of the ambient prefix, the exact exponent conversion gives

```
μ_x = N^(c_L + ε_w), where ε_w = log_N μ_w - b
edgeDensity ≤ N^(4(c_L+ε_w)+2c_E)/4
edgeDensity ≤ N^(2c_E+8δ+4ε_w)/4                 when c_L<2δ
edgeDensity ≤ N^(2c_L+2c_E+4δ+4ε_w)/4          when c_L<2δ
edgeDensity ≤ N^(c_L+ε_w).
```

The error is computed, not assumed small. These bounds are now separately verified for both absolute and ambient-relative density. They do not assert the printed negative-`c_F` saving. Deriving their uniform asymptotic forms from the source's expected ambient-size assumption is under independent review.

The source's density interpretation is itself verified:

```
edgeDensity = E[card(edges of first copy ∩ edges of second copy)].
```

Both copies use the same law and edge coordinates under a constructed product law. This requires no independence among positions within one deck. Independently recentering the two copies is a different observable, with its own verified intersection identity and density bounds.

The relative shift is the number of rows lexicographically below the ambient prefix, namely the source's one-based left endpoint minus one. The implementation proves that every internal edge of an extension lies at or after this cut, and that subtracting it preserves every such edge. This count preservation does not assert density invariance under a random translation.

## Proof audit and immutable contract

- `audit/whole_proof.md` maps all 70 active declarations, the 11 inactive lower-blueprint declarations, upper/lower proof chains, random-pile extensions, and required concentration/stable-block inputs.
- `audit/reconstruction.md`, `audit/statements.md`, and `audit/hidden_cases.md` are the three independent source reports. Each reviewer also checked every finite statement before implementation.
- `audit/comparison.md` records the comparison and disagreements resolved before freeze.
- `audit/frozen_contract.md` contains D1–D8 and F01–F33; `audit/freeze.json` records its hash and the hashes of the three permitted sources.
- `audit/theorem_index.json` maps each frozen statement to its Lean declaration.
- `audit/implementation_review.md` records independent comparison of the implementation with the frozen contract.
- `audit/verification.json`, `audit/build.log`, and `audit/logical_dependencies.log` record build and logical-dependency checks.
- `audit/whole_tex_reread.md` records the root's full-file reread and comparison with three independent rereads, including the interpretation and the alternative small-class argument.
- `audit/collision_contract_{reconstruction,statements,assumptions}.md` and `audit/collision_contract_comparison.md` record independent review of every new statement before code.
- `audit/frozen_collision_contract.md` and `audit/collision_freeze.json` preserve the additive definitions, all 58 statements, and their pre-implementation hashes. Optional occupancy-conditioning statements are expressly excluded from that freeze.
- `audit/collision_theorem_index.json`, `audit/collision_signatures.log`, and `audit/collision_verification.json` record the new declaration inventory, actual compiled types, and verification.
- `audit/collision_implementation_reconstruction.md` and `audit/collision_implementation_assumptions.md` independently review the implemented sorting, estimates, and probability model.
- `audit/conditional_contract_{reconstruction,statements,assumptions}.md` and `audit/conditional_contract_comparison.md` record the independent pre-code review of all seven occupancy statements and three definitions.
- `audit/frozen_conditional_contract.md` and `audit/conditional_freeze.json` freeze their exact signatures and all source, review, parent-contract, and parent-implementation hashes.
- `audit/conditional_theorem_index.json`, `audit/conditional_signatures.log`, and `audit/conditional_verification.json` record the compiled inventory and verification.
- `audit/conditional_implementation_review.md` compares the final implementation and independent reviews, including the proof-only elaboration correction.
- `audit/overlap_contract_{reconstruction,statements,assumptions}.md`, `audit/overlap_contract_comparison.md`, and `audit/frozen_overlap_contract.md` record the independently reviewed and frozen exact overlap meaning.
- `audit/overlap_freeze.json`, `audit/overlap_signatures.log`, `audit/overlap_verification.json`, and `audit/overlap_implementation_review.md` record preservation checks, compiled signatures, kernel verification, and review.
- `audit/exponent_contract_{reconstruction,statements,assumptions}.md`, `audit/exponent_contract_comparison.md`, and `audit/frozen_exponent_contract.md` record the independent pre-code review and frozen source-defined exponent statements.
- `audit/exponent_freeze.json`, `audit/exponent_signatures.log`, `audit/exponent_verification.json`, and `audit/exponent_implementation_review.md` record preservation, signature, kernel, and implementation checks.
- `audit/relative_contract_{reconstruction,statements,assumptions}.md`, `audit/relative_contract_comparison.md`, and `audit/frozen_relative_contract.md` record independent source-coordinate review and the exact eighteen-statement freeze.
- `audit/relative_freeze.json`, `audit/relative_signatures.log`, `audit/relative_verification.json`, and `audit/relative_implementation_review.md` record preservation, signature, kernel, and implementation checks for the recentered model.

## Outstanding analytic scope

For first-column counts `(a,b,a)`, the one-digit middle prefix has deterministic zero-based endpoints `a` and `a+b`. The new fluctuation definition nevertheless assigns the positive scale `sqrt(a)`. The proposed hypergeometric reveal samples the whole residual population, so the required complementary fraction is zero. The Lean endpoint module certifies these finite identities; the reports explain the asymptotic contradiction.

The reconstruction report also gives a direct small non-singleton counterexample. Take first-column counts `(N/4,N/2,N/4)`, second-column counts `(2,(N−2)/2,(N−2)/2)`, then uniform thirds. For the stable prefix `(1,0)`, occupancy is at most two and its left endpoint is deterministic. The probability of occupancy two tends to `1/4`, so the squared edge density lacks the claimed `N^(−1/2)` factor. This disproves an assigned conclusion, rather than only its proof route. Full model-specific certification of this second example remains outside the finite Lean subset.

Per-edge coverage also omits the polynomial truncation loss and the possibility that the edge index is outside the ambient block. The relevant-parent count needs a stronger, quantitatively stated endpoint tail than the source supplies. The active random lower extension is not proved in the source; its old blueprint is commented out.

The older deterministic-cut paper separates the deterministic initial-column contribution and preserves unused population when resampling. The whole-file reread explains this intended smoothing mechanism. Changing the new manuscript's fluctuation or stopping definitions would require an explicit contract decision and a new independent review and freeze. Nothing in this project silently makes that change. The exact collision addendum instead proves a previously unimplemented dependency under the existing model.

## Reproduce verification

Lean and mathlib are pinned to v4.24.0, with all dependency revisions recorded in `lake-manifest.json`. With that Lean toolchain installed:

```sh
lake exe cache get
python3 verify.py
python3 verify_collision.py
python3 verify_conditional.py
python3 verify_overlap.py
python3 verify_exponent.py
python3 verify_relative.py
```

The six verifiers build the project, check all frozen contracts and original source hashes, check the exact 33-, 58-, 7-, 6-, 15-, and 18-declaration inventories, reject prohibited proof placeholders, and print theorem dependencies. The addenda also audit their constructors and save actual compiled signatures. Only Lean/mathlib's standard foundational dependencies `propext`, `Classical.choice`, and `Quot.sound` are permitted. The local verification uses the official compiler under `/private/tmp/edge-localization-tools`; the verifiers recognize that installation while it exists.
