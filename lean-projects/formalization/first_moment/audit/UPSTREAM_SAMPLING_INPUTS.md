# Upstream sampling inputs: bounded read-only inventory

Snapshot: 2026-09-17, approximately 20:47 UTC. The upstream probability task was still active. This inventory read the arriving `lean/Shuffle` sources and their supplied audit/build scripts; it did not run the package build or change any Lean source or frozen contract.

## Executive finding

The upstream package supplies genuine finite probability laws, exact residual sampling laws, canonical hypergeometric moments, and valid conditional concentration/point-mass transfer. It does **not**, in the inspected modules, already prove the model-specific labelled-row probabilities, prefix occupancy moments, or equal-row-pair bound needed by the alternative small-block proof. Nor does it identify a shuffle endpoint with a residual count having positive variance. The distinction between these missing applications and the available general probability theorems must remain explicit.

## 1. Fixed columns and matrices

All names below have prefix `Shuffle.` unless otherwise indicated.

`Histogram V k` is a **structure** carrying natural pile counts summing to `Fintype.card V`. `FixedColumn h` is the subtype of actual row assignments `V → Fin k` with exactly those digit counts. `columnLaw h` is the uniform finite law on that subtype. This is an actual model, with nonemptiness proved by `fixedColumn_nonempty`; it is not a hypothesis asserting that some abstract variables have the desired law.

Relevant proved exports:

| Exact name | Actual premises and conclusion |
|---|---|
| `sum_digitCount` | For any finite row type and assignment, the sum of its digit-fibre cardinalities is the number of rows. |
| `Histogram.digitCount_split` | For any row subset R, full digit counts split into R and its complement. |
| `Histogram.prescribed_admissible` | An actual legal column satisfying the prescription implies each prescribed digit count is at most its pile count. |
| `Histogram.prescriptionFiberEquiv` | Given `h.Admissible R b`, the complete prescription fibre is explicitly equivalent to legal assignments of the residual histogram on `Rᶜ`. |
| `Histogram.prescription_prob_pos_iff` | The prescribed-row event has positive probability under `columnLaw h` iff `h.Admissible R b`. |
| `Histogram.conditional_residual_point` | Given admissibility and an actual legal residual assignment g, its conditional restriction probability equals its uniform residual mass. |
| `Histogram.conditional_residual_law` | Given admissibility, the positive-event conditioned law, mapped by literal row restriction, equals the uniform residual-column law mapped to raw assignments. This is equality of full finite laws. |
| `conditional_fixedMatrix_residual_law` | For finite column/row types, a feasible histogram per column, prescribed row sets/values per column, and admissibility in every column, conditioning the independent product on those separate prescriptions preserves the product of exact uniform residual-column laws. |

`fixedMatrixLaw` is the **definition** of the product of `columnLaw` across the column index. The product rectangle theorem used to justify its independence is `Shuffle.FiniteLaw.product_prob_rectangle`. General conditioning on a non-rectangular exploration event is not covered by `conditional_fixedMatrix_residual_law`.

No inspected theorem in `FixedColumns.lean` supplies the explicit one-row formula `P[f(v)=a]=n_a/N`, the distinct-row formula `P[f(v)=a,f(w)=a]=(n_a)_2/(N)_2`, or the pushforward saying that the set of rows with digit a is uniform among all `n_a`-subsets. The uniform-column definition makes those facts provable, but the proof bridge is still required.

## 2. Uniform labelled subsets and residual sampling

`Sample V m` is the actual subtype of m-element subsets of a finite labelled set V. `sampleLaw V m hm` is its uniform law, with `hm : m ≤ V.card`. `samplingParams V A m hA hm` has population `|V|`, marked size `|A|`, draws m. These are definitions; the law equality is proved separately.

| Exact name | Actual premises and conclusion |
|---|---|
| `intersection_fibre_card` | `A ⊆ V`, `q ≤ m`; counts m-subsets with intersection size q as `choose(|A|,q)*choose(|V|-|A|,m-q)`. |
| `sample_intersection_mass` | `A ⊆ V`, `m ≤ |V|`, and q in `Fin(m+1)`; actual subset-intersection probability equals canonical hypergeometric weight. |
| `sample_intersection_pointMass` | The same set/sample feasibility, every natural q; actual intersection probability equals `pointMass q`, including points outside the support. |
| `sample_intersection_law` | The same bridge written as canonical-law probability, for every natural q. |
| `sample_prescription_pos_iff` | `B ⊆ R ⊆ V`, `m ≤ |V|`; positivity of `S∩R=B` is equivalent to `|B|≤m` and `m-|B|≤|V\R|`. |
| `sample_conditional_residual_mass` | The same inclusions plus both residual feasibility inequalities; every legal residual sample has its exact uniform conditional mass. |
| `sample_conditional_intersection_prob` | Additionally `A ⊆ V\R`; the conditional count `|A∩S|` has the law of intersection with a uniform `(m-|B|)`-subset of `V\R`. |
| `sample_conditional_hypergeom_mass` | The same premises; canonical hypergeometric mass with population `|V\R|`, marked size `|A|`, and draws `m-|B|`. |
| `sample_conditional_hypergeom_law` | The same full law equality at every natural count. |
| `conditional_uniform_sample_intersection_law` | A finite law p, reveal Z, a **positive** atom `Z=z`, an actual sample variable `S:Ω→Sample V m`, atom-dependent marked set A with `A z⊆V`, and the explicit premise `(p.condition (Z=z) hz).map S = sampleLaw V m hm`; concludes the exact conditional hypergeometric intersection law. |

The last theorem does not derive conditional uniformity for an arbitrary shuffle reveal: `hlaw` is a real proof obligation. It also correctly retains the full sampling population V, rather than replacing it by the marked/surviving set A.

## 3. Canonical moments and conditional transfer

`HypergeomParams` carries natural `population`, `marked`, `draws`, and both feasibility inequalities against the population. Its `law` is the normalized binomial-coefficient law. Its mean and variance formulas use real casts before subtraction; populations zero and one are included.

The following facts are proved for this actual canonical law, not merely defined:

- `Shuffle.HypergeomParams.expect_descFactorial`: for every natural r, expectation of `(Y)_r` equals `(marked)_r*(draws)_r/(population)_r`, including zero and overlarge orders.
- `Shuffle.HypergeomParams.expect_val`: expectation equals `mean`.
- `Shuffle.HypergeomParams.expect_choose`: the binomial-coefficient moment form.
- `Shuffle.HypergeomParams.expect_mul_pred`: the second factorial moment with real subtraction.
- `Shuffle.HypergeomParams.variance_val`: variance equals the exact `varianceFormula`.
- `Shuffle.HypergeomParams.variance_eq_zero_iff`: variance vanishes exactly when marked=0, draws=0, marked=population, or draws=population.
- `Shuffle.HypergeomParams.exists_concentration_constant`: a single positive c works for all feasible parameters and all `t≥0`, with bound `2 exp(-c min(t²/(mean+t),t))`; the proof supplies c=1/4.

`Shuffle.FiniteLaw.HasConditionalHypergeometric p E Y h` is only a **definition**: it says every conditional count probability agrees with `h.pointMass`. The following theorems require both a strictly positive event E and a proof of that exact law predicate:

- `conditional_hypergeom_expect`
- `conditional_hypergeom_descFactorial` (all natural r)
- `conditional_hypergeom_variance`
- `conditional_hypergeom_centered_second`
- `conditional_hypergeom_variance_eq_zero_iff`
- `conditional_hypergeom_pow_le` (also `0<s≤1`)
- `exists_conditional_hypergeom_concentration_constant`

Thus these exports may transfer an established shuffle count law. They cannot substitute for establishing it. Generic helpers `conditional_expect_eq_of_count_law`, `conditional_prob_eq_of_count_law`, and `conditional_variance_eq_of_count_law` prove the finite-law transport, with no extra pointwise support assumption: zero mass outside the target support is derived.

## 4. Positive residual variance versus the invalid side-mass inference

The available valid anti-concentration theorem is

`Shuffle.HypergeomParams.pointMass_le_four_div_sqrt (p) (hv : 0 < p.varianceFormula) (q)`.

It proves `p.pointMass q ≤ 4/sqrt(p.varianceFormula)`. The corresponding exact conditional result is

`Shuffle.FiniteLaw.conditional_hypergeom_pointMass_le p E hE Y h hlaw hv q`.

Its premises include all three distinct obligations:

1. positive conditioning-event probability;
2. exact conditional hypergeometric count law;
3. positive **residual** variance.

`Shuffle.HypergeomParams.varianceFormula_lower` and `variance_lower` require `population≥2`, nonnegative lower bounds u,a,b, `u≤mean`, `a≤1-marked/population`, and `b≤1-draws/population`. Only then do they prove variance at least uab. They do not infer either complementary fraction from two positive side masses.

`Shuffle.sample_complement_of_reserve` likewise requires an explicit reserve inequality `m+r≤N-h` as well as positive N, `0≤r<N`, and nonnegative m,h. `Shuffle.residual_fraction_error` requires `r<N` and a stated deviation bound. These are sound algebraic tools, not an ambient reserve theorem.

The fine-to-coarse theorem `Shuffle.FiniteLaw.shifted_anticoncentration_transfer` is also sound but conditional: it requires a fine reveal Z determining the coarse reveal U, an integer shift fixed on each fine atom, a selected event contained in the good reveal set, a nonnegative bound b, and the fine conditional count point-mass bound on every positive good atom. It transfers that bound to positive coarse atoms. It supplies no missing variance lower bound.

The upstream package explicitly proves the obstruction in `Shuffle.positive_sides_do_not_prevent_exhaustion`: parameters `(population,marked,draws)=(2L,L,2L)` with `L≥1` have positive mean and marked/unmarked populations, but variance zero, atom L of mass one, and zero sample complement. `fixed_column_middle_endpoints` additionally proves the deterministic histogram endpoint counts. No false source side-mass-to-variance implication was found among the exports.

## 5. Random pile arrays and mixtures

The names in this paragraph are fully qualified to avoid confusing the two finite-law interfaces.

- `Shuffle.FiniteLaw.mixture` and `joint` define actual normalized finite laws.
- `Shuffle.FiniteLaw.mixture_prob` and `mixture_expect` prove averaging identities.
- `Shuffle.FiniteLaw.joint_first_prob` identifies latent atom probabilities; `joint_conditional_second` and `joint_condition_second_map` recover the selected component law only under `0<p.mass theta`.
- `Shuffle.FiniteLaw.joint_second_map` proves that forgetting the latent index yields the mixture.
- `Shuffle.rawMatrixLaw` defines the independent product of uniform fixed-column laws mapped to one common raw matrix space.
- `Shuffle.rawMatrixLaw_rectangle` proves its column rectangle probabilities factor.
- `Shuffle.randomMatrixLaw` and `histogramMatrixJoint` allow an arbitrary finite law on complete feasible histogram arrays. No independence of pile sizes is imposed.
- `Shuffle.randomMatrixLaw_prob`, `histogramMatrixJoint_marginal`, `conditional_randomMatrixLaw`, and `conditional_randomMatrix_rectangle` prove the mixture and positive-environment-atom law identities.

These are the correct finite conditioning/mixture inputs. They do not themselves prove a random-cut mixing theorem or a polynomial expected-common-edge bound on exceptional environments. In particular, an `o(1)` probability of an exceptional environment can contribute order `N*o(1)` to an unnormalized edge count.

## 6. Exact remaining model bridge for our small-block route

The following statements were **not found as proved exports** in the inspected `lean/Shuffle` modules:

1. The digit-a row set under `columnLaw h` has the uniform `h.count a`-subset law.
2. Consequently, the one-row and two-distinct-row digit probabilities have the usual fixed-column formulas.
3. The prefix-survivor count in the actual fixed-matrix model has the appropriate successive conditional hypergeometric transitions.
4. Its first and second factorial moments equal the corresponding products, or the second factorial moment is bounded by the square of its mean.
5. The actual shuffle graph's internal edges are bounded by its equal-row pairs, with the appropriate tail collision factor.

There are two viable assembly paths after proving these bridges. The direct labelled-row route combines one-/two-row probabilities with `product_prob_rectangle` (or `rawMatrixLaw_rectangle`) and finite expectation linearity. The survivor-count route first proves the conditional uniform digit-subset law, invokes `conditional_uniform_sample_intersection_law`, transfers its r=1 and r=2 moments through `conditional_hypergeom_descFactorial`, and uses `FiniteLaw.total_expectation`. Neither path needs anti-concentration for small blocks.

For the latter route, keep the correct population at every stage: a new independent column samples its digit set from the full current column population; the previously surviving rows form the marked set. For a residual column conditioned on prescribed labels, the population is the explicit unrevealed complement from `Histogram.residual`, which need not equal the ambient prefix size.

The first-moment package's `FiniteGraphLaw` can consume these finite masses once an actual graph-valued map and its bridges are supplied. An adapter between `Shuffle.FiniteLaw` and that structure is straightforward but is not, by itself, the missing shuffle graph theorem.

## 7. Supplied native-build and trust evidence

- `lean/lean-toolchain` pins Lean 4.19.0; `lean/lakefile.lean` pins mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `lean/check.sh` uses the local native Darwin/aarch64 Lean 4.19 toolchain and that cached mathlib, producing `.olean` files beside the sources. I did not execute it.
- Native `.olean` files were present for all ten sampled dependency modules. Initially `FixedColumns.olean` preceded an in-progress source edit; at the last snapshot it was no older than the current source. This is filesystem evidence only, not a replacement for a source-digest-matched build record.
- The latest observed `FixedColumns.lean` SHA-256 was `5d0a7f87ba58d7533044f2081fd5b2be636cb3d784a578cfe6366eb82f3ec6b5`.
- Read-only hashing confirmed that `lean/audit/freeze_manifest.json` matches the frozen probability contract and all three permitted mathematical source files.
- A read-only token scan of all current `lean/Shuffle/*.lean` found no `axiom`, `sorry`, `admit`, or `native_decide` tokens.
- `lean/audit/moments_and_pointmass_verification.md` records successful native checks of the moment and anti-concentration modules and reports only `[propext, Classical.choice, Quot.sound]` for the named key exports.
- `lean/audit/conditioning_implementation_audit.md` records successful checks/reviews for conditioning, residual sampling, and the finite-mixture/random-column interface; it explicitly preserves the conditional-law and variance obligations.
- At 20:46:55 UTC, `lean/audit/verification.json` and `lean/audit/axiom-report.txt` were **not yet present**, despite the README describing their eventual locations. The active upstream task may produce them subsequently. No completed whole-package trust claim should be inferred from their future-facing README references.
- `check-all.sh` is configured to compile the modules and then run `PrintAxioms.lean`; `verify_axioms.py` checks exact report coverage and permits only the three standard foundational dependencies before writing a source-hashed verification record. Await that record, or perform a narrowly scoped integration check after the upstream task finishes, rather than treating the current README as the final build result.

The available proofs provide a substantial, properly scoped probability core. They do not certify the manuscript's false ambient non-exhaustion statement, the whole shuffle theorem, or the currently missing model-specific first-moment bridges.

## Later verification record inspected by the primary agent

The upstream task subsequently produced `lean/audit/verification.json`, timestamped `2026-09-17T20:48:17.311287+00:00`, and its complete trust report. That record covers 16 modules and 185 public declarations on the shared Lean4.19.0/mathlib toolchain, permitting only `propext`, `Classical.choice`, and `Quot.sound`. The primary agent checked that all 16 recorded source hashes still match the supplied files. This is inspected upstream build evidence, not a claim that the primary agent rebuilt all 16 modules. The record explicitly leaves full-manuscript certification and ambient non-exhaustion false. The exact law, moment, conditioning, and mixture inputs above can therefore be used as proved project dependencies; their stated model application obligations remain.
