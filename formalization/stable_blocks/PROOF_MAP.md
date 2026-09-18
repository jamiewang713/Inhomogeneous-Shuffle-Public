# Whole-article proof map and formalization boundary

This map covers every active named definition, lemma, theorem, proposition, and corollary in `time_inhomogeneous_riffle_shuffle_unified_article.tex`: **70 declarations**. The obsolete lower-bound overview inside `comment` at lines 2564–2786 is not active and is not counted. Line numbers below refer to the unchanged article. The two permitted predecessor sources are `2103.05068v3.pdf` and `2510.22783v1.pdf`.

The literal-reference index is [dependency-index.md](spec/dependency-index.md). This document supplies the mathematical inputs that are needed even where the article does not use an explicit `\ref`. Its dependency edges describe the argument in the supplied sources; they do not certify that every analytic argument is correct or complete.

Only the assigned exact finite boundary/stable decomposition has been implemented in Lean. No total-variation upper bound, lower bound, hypergeometric concentration theorem, or random-pile cutoff theorem is claimed formally proved. The finite expected-count expression is defined and analyzed as a finite sum of one-row product weights. A probability-space theorem identifying that expression with an integral over uniformly permuted fixed-count columns remains a separate foundation.

## Status key

- **K**: assigned finite statement has a kernel-checked Lean implementation. This does not include the article's asymptotic or probabilistic identifications unless explicitly stated.
- **I**: implementation is present; final aggregate build/audit determines completion.
- **D**: article definition or unnumbered construction; an analytic definition alone is not a proved estimate.
- **P**: paper argument supplied, awaiting its own statement freeze, proof audit, and formalization.
- **S**: sketch or imported external foundation remains to be reconstructed and proved/imported from trusted Lean mathematics.
- **X**: a counterexample invalidates the displayed claim with the current definitions.
- **P↓ / S↓**: the displayed proof route uses an invalid or unavailable upstream quantitative result. This marks the route as unavailable; it does not assert that the final conclusion is itself false.

The freeze contract is [FROZEN_SPEC.md](spec/FROZEN_SPEC.md). Source-level asymptotic assertions were not added as assumptions to the finite Lean results.

## Unnumbered data, definitions, and prerequisite groups

These groups are direct inputs to the declaration tables below. The distinction between a definition and a theorem about it is deliberate.

| Group | Definitions and construction | Mathematical prerequisites and current boundary |
|---|---|---|
| **A0 — finite shuffle data** | Article 88–124: alphabet `[k]₀`; pile counts summing to N; p=n/N; K=⌊T log N⌋; shuffle law P(n,K), uniform permutation law, TV, mixing time; path internal/boundary edges; falling factorials; base-N logs. | Finite pile normalization and legal-word data are implemented. The full random shuffle law, uniform permutation probability model, TV and mixing-time definitions are not part of the assigned Lean result. N>1 is explicit in the frozen finite log model. |
| **A1 — profile costs and margins** | 125–170, 176–233: p_max, a_p, ψ_p(θ), tilted p^[θ], I_p,H_p; expectations under μ_t; integrated A,Bθ,Jθ; β; Λ0,…,Λ3,ΛUB and both critical thresholds. 2198–2240: coefficients c_i(θ), F_i^T(s,u). | Require support-aware log conventions, finite probability vectors, measurable time profile, integrability of cost functions, integration/additivity, compact-parameter infima/suprema, endpoint continuity, and a precise extended-value convention for an empty negativity set. These are future analytic foundations. |
| **A2 — random matrix and shuffle graph** | 388–400, 446–472: independent uniform fixed-count columns S,S′; sorted row strings; equality edges; component sorting π↦π_G; graph density f_(G,σ), two-graph density f_(G,G′), common edges. | Must construct finite uniform multiset assignments, prove column independence and exchangeability, define sorting with ties, path components and componentwise sorting, prove the representation law and density formulas. The assigned row-interval results apply deterministically to any full legal row map and do not construct this probability model. |
| **A3 — legal tree and exact finite masses** | 446–458: legal words, prefix tree, parent, B_x, family cylinders; row-rank inverse images. 490–518: w,r,b,t_x,c_L,c_E, recentered ranks. | Word/prefix, legal extension, lexicographic convexity, finite product weights, positivity, c_L antitonicity, and samplewise partition transport are implemented. `b` remains an arbitrary proxy: `c_L=log_N E(count)+o(1)` is not an exact Lean hypothesis or theorem. Absolute-time floor errors and tail c_E/profile identifications remain analytic. |
| **A4 — boundary/stable construction** | Entire Definition 521–697: large-pile endpoints; left/right first-crossing families; admissibility counts; compatible pairs and joins; P/Q side pieces; both maxima cut at the join length; square roots, bottom-valued logarithm; terminal and retained pairs; Γ,Λ; stable family. | Implemented finite definitions and proofs derive first-crossing minimality, retention of every compatible pair, continuation invariance, persistent stopping, and disjoint interval partitions. “Fluctuation-regular” is an asymptotic inequality to be proved later; the side masses are not thereby certified as actual endpoint standard deviations. |
| **A5 — profiles, classes, and scales** | 474–488, 699–747, 1039–1119: nested parameter choices; time/simplex cells; good/exceptional digits; c-counts, exceptional positions, S_x,Q_x,R_x,H_x; boundary/profile classes and their counts. | Need a formal sequence-indexed meaning for all o(1), O(·), uniformity, floors and parameter selection. Class cardinalities, entropy bounds, rare-event costs, and moment contributions are quantitative results, not consequences of finite coverage alone. |
| **A6 — exploration and typical events** | 366–372, 1916–1983: accessible ambient blocks; forward/backward revelations; explored sigma-fields; 2k directional shared-edge sets; regular event, local sparsity, S₁; “large” versus “small” remaining blocks. 2045–2139: b_r=1−A(0,r), uniform accessible error ε_N. | The article sketches these notions rather than giving a complete formal exploration object. Need an exact reveal algorithm/filtration, conditional residual laws, a uniform accessible-size bound, all-tail goodness transfer, deterministic block decomposition, and an explicit regular-event definition before the conditional lemmas can be stated rigorously. |
| **A7 — lower prefix counts and thinning** | 2915–3016: λ_w, t_w, J_w,H_w; sorted interval I(B_w), endpoints L_w,U_w and count C(w); labelled survivor sets S_t, selected piles, counts X_t and conditional hypergeometric transitions. 3018–3084: admissible prescribed rows, residual population/piles and mean. 3362–3373: true variance-defined location exponent c_loc,M_loc. | Require A2's labelled probability model, exact product first moments, conditional exchangeability and independence after admissible prescriptions, and one-column hypergeometric transitions. The variance-defined c_loc differs from A4's side-mass c_F; do not identify them. |
| **A8 — lower witness and truncated types** | 3432–3495: Fθ(s,u;T), maximal prefix a_r, tilted entropy ℋθ, h and Γ; 2897–2913: bridge-width hierarchy and all-tail local goodness. 3800–3845: regular cells R, G_R, Z^χ_(α,R), truncated law q^χ, J^χ,ℋ^χ,B^χ, εχ and hχ. | Need deterministic maximum selection, A1's entropy/derivative calculus and profile continuity, controlled truncation error, rounded type counts, and a uniform hierarchy of witness/bridge buffers. The lower cold family is not an upper stable family. |
| **A9 — bridge, full cold family, occupancy** | 4004–4078: two good columns g_L<g_R; bridge b and reserved b⁻<lex b<lex b⁺; bridge/tail index sets ℬ,ℛ; λ_b,ℓ_b; restricted/truncated tail functionals; tail type family T₂; Γℛ and Γχ,ℛ. 4080–4093: full cold words, multiplicities N_y, events A_y={N_y≥2}, Zθ. 4740–4745: near-critical mean exponent mχ,ℛ. | Need legal bridge construction, exact product factors, type counting, factorial-moment identities for several labelled rows, conditional residual laws, and quantitative occupancy approximations over the entire family. |
| **A10 — permutation tests** | 4899–5163: translates H_q, odd/even ascent counts, scan event; uniform component value sets/reservoir; component-sorted ascent functional X; run lengths L_j, shared/internal edge count r. | Need independence of relative orders on disjoint pairs, Hoeffding/Azuma inequalities with verified hypotheses, a rigorous without-replacement block-exposure coupling, component boundary expectation formulas and path-boundary accounting. These are future foundations; a named martingale inequality alone does not prove the required conditional-range bound. |
| **A11 — random pile mixtures** | 265–274 and 1999–2011; predecessor 2510.22783v1 §3.3 and §6.2: random count sequence, typical deterministic realizations, mixture P(X,K), and union of deterministic rejection tests. | Need the mixture identity/conditioning, uniform deterministic estimates, finite count-sequence cardinality ≤(N+1)^(kK), and a common measurable test for the lower bound. Upper TV convexity and lower common-test separation are different principles. |

## Every active upper-bound declaration and its direct inputs

Names in the input column identify already listed definitions/results or one of A0–A11. A forward reference reflects the order of exposition, not a logical cycle.

| Article line and declaration | Direct mathematical inputs | Status |
|---|---|---|
| 235 — Upper critical-time theorem, reduced form (`thm:upper-critical-reduced`) | Four-margin critical-time corollary; dominance reduction identifying the two negativity sets/thresholds; A0 mixing-time infimum and floor/limsup passage. The proof is at 2521–2550. | **P↓** |
| 249 — Almost time-profile-like cuts (`def:almost-time-profile-like-cuts`) | A0 normalized columns/time scaling; A1 time profile; finite measurable simplex partition; grid width ρ and error φ. | **D** |
| 265 — Randomized time-profile-like cuts (`def:randomized-time-profile-like-cuts`) | Almost-profile-like definition applied realization by realization; A11 random cut sequence and mixture; probability 1−o(1) with fixed application parameters. | **D** |
| 276 — χ-regular partitions (`def:chi-regular-partitions`) | A1 simplex costs and logarithms; finite Borel partition with representatives; support thresholds χ,2χ,3χ. The claimed partition construction additionally needs uniform continuity on controlled support and threshold-cut bookkeeping. | **D/P** |
| 305 — Good columns (`def:good-columns`) | A0 column probabilities; two coordinates ≥χ; macroscopic interval counts, γ and ρ. No existence of enough good columns follows merely from normalization. | **D** |
| 331 — First-moment margin (`def:first-moment-margin`) | A1 integrated costs, β_(r,b), compact θ-range [3,4]; A3 ambient birth time/exponent and terminal time; definitions of N₁,N₂,N₃ and uniform negative buffer η. | **D** |
| 366 — Recursive first-moment margin (`def:recursive-first-moment-margin`) | First-moment margin on every accessible block; A6 precise notion of accessibility. Its sufficient condition also uses the independent bound b≤1−A(0,r)+o(1), which must be proved uniformly. | **D/S** |
| 377 — Deterministic time-inhomogeneous upper bound (`thm:deterministic-upper-bound`) | Truncated χ² bound; sparse factorial bound; shared-edge exponential moment; regularity/sparsity. Those inputs require almost-profile likeness, all-tail local goodness and RFM. Uniformity over deterministic sequences must be preserved. | **S↓** |
| 402 — Graph representation (`lem:ub-graph-representation`) | A2 uniform fixed-column assignments, conditional uniform interleaving, lex sorting and independent uniform permutation; identification of equal-string blocks with graph components. The predecessor fixed-column representation argument is transferable, but is not a Lean theorem here. | **S** |
| 410 — Truncated chi-square bound (`lem:ub-truncated-chi-square`) | Graph representation; A2 graph densities and independent copy; finite density/TV identities, Cauchy–Schwarz and truncation by a typical matrix event. | **S** |
| 424 — Local sparsity (`def:local-sparsity`) | A0 finite path and integer intervals; A2 shuffle graph; integer L≥10 and local edge count ≤L/3. | **D** |
| 429 — Sparse factorial bound (`lem:ub-sparse-factorial`) | Local sparsity of G,G′; path-union component size bound; exact component factorial expression/upper bound for the two-density moment f_(G,G′); factor assignment to common edges. | **S** |
| 490 — Ambient block and size exponent (`def:ambient-block-size-exponent`) | A3 legal ambient w and prefix cylinders; A2 expected rank counts; asymptotic parameters r,b; normalized c_L costs and tail collision exponent c_E. | **K** for finite c_L/data; **D/P** for asymptotic realization and c_E |
| 521 — Stable blocks (`def:boundary-pairs-stable-blocks`) | A0 pile normalization and χ<1/k; A3 legal words, prefix relation, exact finite masses, arbitrary b; A4 side-piece/c_F and terminal-first stopping definitions. | **K** for assigned finite construction; fluctuation-regularity remains **D/P** |
| 699 — Space-time digit profile (`def:space-time-digit-profile`) | Stable block/pair times; χ-regular representatives; almost-profile partition; time mesh; good/exceptional classification; finite counts and entropy conventions. | **D** |
| 749 — Numerical first-moment margin (`def:numerical-first-moment-margin`) | Same A1/A3 data as the first-moment margin at 331. The calligraphic N₁,N₂,N₃ are the repeated local-margin formulas, not additional independent hypotheses. | **D** |
| 788 — Stable partition (`lem:ub-stable-partition`) | Boundary compatibility/join; concrete c_L antitonicity; c_F continuation invariance; generic persistent first-hit cut with terminal fallback; legal full extensions; cylinder antichain/convexity and rank inverse-image transport. No FM/goodness/profile assumption. | **K** in `SourceStable.lean` and its dependencies |
| 828 — Global boundary decomposition (`lem:ub-global-boundary-decomposition`) | Unique left/right boundary prefix; fiber=join cylinder; positive left/right side masses for every compatible nonterminal pair, hence retention; stable partition; disjoint pair fibers and admissibility iff coverage. | **K** in `Riffle/Global.lean` and its dependencies |
| 857 — Regular partition and interval blocking (`lem:ub-regular-partition-interval-blocking`) | χ-regular definition; almost-profile grid counts; decomposition of arbitrary time intervals into full grid cells plus ≤2ρ boundary width; representative log bounds and floor-error sums. | **P** |
| 898 — Profile estimates (`lem:ub-profile-estimates`) | Exact c_L splitting; regular partition/interval blocking; A5 profiles; maximum-pile comparison; crossing side-mass lower bound; active Γ parent condition; finite relative-entropy inequality applied to tilted weights; exceptional-count truncation. Positivity/continuation pieces are compiled, but all displayed quantitative asymptotics remain separate. | **P** |
| 1039 — Bad-profile reduction (`lem:ub-bad-profile-reduction`) | Boundary/admissibility and profile definitions; digits outside large endpoints have mass <χ; exceptional digits have mass ≤3χ; exact prefix first-moment factors; entropy/binomial counting of locations/digits and class counts; expectation/edge contribution bounds and union estimates. | **P** |
| 1121 — Hypergeometric estimates (`lem:ub-hypergeometric-estimates`) | Uniform subset intersection law, PMF, mean and variance; without-replacement concentration; Stirling estimates and log-concavity for maximum point mass; explicit degenerate population/variance cases. | **S** |
| 1154 — Ambient conditioning transfer (`lem:ub-ambient-conditioning-transfer`) | Hypergeometric estimates; conditional residual column law; a precisely enumerated endpoint-piece family; admissibility/profile class counts; repeated thinning; side-mass lower bounds. Its final variance-complement assertion needs the actual revealing construction and is not established by positive side mass alone. | **S**, associated with the failed anti-concentration route |
| 1202 — Ambient concentration and anti-concentration (`lem:ub-ambient-concentration-anti-concentration`) | Hypergeometric estimates; ambient transfer; exact endpoint first-difference decomposition; profile/fluctuation comparison; valid conditional resampling variable after fixing internal information; variance lower bounds and interval concentration. | **X** for the atom/anti-concentration claim; concentration portions require separate statements/proofs |
| 1436 — Per-edge stable localization (`lem:ub-per-edge-stable-localization`) | Stable/global partition; bad-profile reduction with a precisely specified retained location/event; endpoint concentration windows; parent map and ordered intervals; finite union bound over prefixes. Its proof cites the concentration portion of the combined lemma, so that portion could be isolated without inheriting the false atom estimate. | **S↓** as currently packaged; not declared false merely from the atom counterexample |
| 1486 — Edge-density bounds (`lem:ub-edge-density-bounds`) | Concrete stable threshold/parent alternatives, profile comparison and c_E; exact two-row tail-collision estimates; count moments; endpoint anti-concentration/conditional translation averaging; large/small/{join} cases. The anti-concentration input is substantive. | **P↓** |
| 1640 — Terminal singleton bound (`lem:ub-terminal-singleton-bound`) | Terminal implies full join and c_E=0; expected occupancy identification; shared-edge probability square ≤ probability and terminal internal-edge count ≤ occupancy. The source invokes a small-mean second-moment estimate, but a direct occupancy first-moment bound is the natural prerequisite. No endpoint anti-concentration is needed. | **P** |
| 1662 — Numerical lemma (`lem:ub-numerical-lemma`) | FM; profile cost/entropy/tail estimates; c_F lower mass comparison and continuation invariance; active Γ parent condition; exact singleton cases; tail-size margin excluding nonterminal Λ; uniform parameter-error absorption. This is deterministic exponent arithmetic and does not require the false endpoint atom estimate. | **P** |
| 1817 — First moment (`prop:ub-first-moment`) | Independent-copy identity E|common edges|=Σp_m²; bad-profile reduction; per-edge localization/class counts; edge-density bounds; numerical lemma; terminal singleton bound; entropy bounds and uniform error losses. | **P↓** |
| 1923 — Conditional preservation (`lem:ub-conditional-preservation`) | A6 explicit exploration and conditioning; exchangeable residual fixed-count columns; conditional hypergeometric concentration; local empirical-profile transfer; uniform accessible exponent bound. | **S** |
| 1931 — Conditional first moment during exploration (`lem:ub-conditional-first-moment`) | Conditional preservation; RFM; first-moment proposition for every large residual block; decomposition into N^o(1) suitable ambient blocks; direct small-block edge/size bounds and a common regular event. | **S↓** |
| 1949 — Portenko exponential moment (`lem:ub-portenko-exponential-moment`) | Directional exploration filtration and adapted success count; uniform conditional future first moment; proved iterated conditional Laplace/Portenko inequality with the regular-event treatment. | **S↓** |
| 1961 — Shared-edge exponential moment (`lem:ub-shared-edge-exponential-moment`) | Directional Portenko bounds; deterministic coverage of all shared edges by 2k directional sets; Hölder/convexity; typical/regular sparse event and t=2k log(L!). | **S↓** |
| 1974 — Regularity and sparsity (`lem:ub-regularity-sparsity`) | Explicit regular event in A6; simultaneous prefix-count concentration; quantitative stable-block collision estimates for short intervals; finite union bounds; large-L parameter choice. The sketch does not isolate which stable estimates suffice independently of anti-concentration. | **S↓** for the cited quantitative route |
| 1999 — Random time-profile upper bound (`cor:random-time-profile-upper-bound`) | Randomized-profile definition; high-probability local goodness; RFM; uniform deterministic upper bound; mixture TV upper inequality and typical/atypical split. | **S↓** |
| 2029 — Buffered pointwise upper bound (`lem:buffered-pointwise-upper-bound`) | A1 global negative margins; additivity giving β_(r,b_r)=β; monotonicity/Lipschitz dependence of each local margin on b; A6 uniform accessible exponent error; RFM definition; deterministic upper theorem. | **P↓**; the reduction to RFM is a separate deterministic argument |
| 2159 — Monotonicity of the upper margins (`lem:upper-margin-monotonicity`) | A1 nonnegative a,ψ and additive interval costs; monotonic β; positivity of θ-coefficients; splitting new time pairs into u≤T₁, s≤T₁<u, or T₁<s; order properties of inf/sup. | **P** |
| 2291 — Four-margin critical-time upper bound (`cor:full-margin-critical-upper-bound`) | Upper-margin monotonicity; infimum/upper-interval property of the negative-margin set with correct extended-threshold convention; buffered pointwise upper bound. | **P↓** |
| 2349 — Basic one-column inequality (`lem:basic-one-column-inequality`) | Probability-simplex normalization and maximum mass; termwise bound on Σp_ℓ^θ; logarithm order and integration over μ_t/time. No shuffle-graph probability input. | **P** |
| 2397 — Reduction to Λ0 and Λ1 (`thm:dominance-reduction`) | Basic one-column inequality, especially integrated B₂≥A and B₃≥2A; θ=3 admissible in [3,4]; additivity and β identity; infimum ≤ endpoint value, then supremum; maximum and negativity-set identities. | **P** |
| 2471 — Buffered consequence (`cor:buffered-consequence`) | Dominance reduction Λ2,Λ3≤Λ0 and definition of ΛUB as maximum. This corollary itself only transfers negative margins; it does not assert TV convergence. | **P** |

## Every active lower-bound declaration and its direct inputs

The lower proof's imports U1–U5 are stated at article 2844–2895. They are graph representation, regular partition/interval blocking and profile cost/entropy bookkeeping, one-step hypergeometric estimates, and the margin reduction for interpreting the target. **They do not import the upper endpoint anti-concentration lemma or the first-moment/mixing theorem.** Thus the counterexample below does not automatically invalidate the lower proof; the lower proof still needs its own full audit and formalization.

| Article line and declaration | Direct mathematical inputs | Status |
|---|---|---|
| 2812 — Buffered reduced lower bound (`thm:buffered-reduced-lower-bound`) | Largest-prefix proposition; cold-witness choice of κ₀(η); cold-spot proposition; split Λ0≥κ₀ versus Λ0<κ₀ and max(Λ0,Λ1)≥η. The actual completion is at 5197–5206. | **P** |
| 3018 — Successive thinning lower tail (`lem:successive-thinning-tail`) | A7 exact labelled hypergeometric transitions; Hoeffding convex-order comparison with binomial for s^H, 0<s≤1; iterated conditional Laplace inequality and Markov; residual-count exchangeability/column independence under bounded admissible row prescriptions. | **P/S** for the external convex-order foundation |
| 3169 — Iterated hypergeometric thinning (`cor:iterated-hypergeom`) | A7 exact conditional means and product means; one-step hypergeometric concentration; finite ancestor-closed polynomial-sized family and union bound; deterministic depth-error induction; K=O(log N); successive-thinning lower tail for the count<2 consequence. | **P** |
| 3377 — Largest-prefix lower bound (`prop:largest-prefix`) | A8 maximal-digit full word; regular-cell A(0,T) cost estimate; exact first moment Nλ; iterated hypergeometric concentration; graph representation/equal-string component; uniform-permutation increasing-run probability 1/m! and union bound; event characterization of TV. | **P** |
| 3498 — One-column entropy inequalities (`lem:entropy-ineq`) | A1 tilted finite probability law; nonnegative relative entropy for H≤I; derivative I′=−Var(log(1/p)) on support and controlled extension at zero masses; Σp⁴≤(Σp²)² and log monotonicity. | **P** |
| 3540 — Buffered bridge window (`lem:bridge-window`) | Local good-column condition uniformly on tails; bridge-width hierarchy; elementary shift u=min(v,T−ρ_b); interval rounding; bounded/truncated one-column costs controlling endpoint-shift losses. | **P** |
| 3583 — Cold-witness reduction from Λ1 (`lem:cold-witness`) | A1/A8 witness functionals and compact/continuous parameter dependence; entropy inequalities and θ-derivative/convexity; approximate supremum witness; θ endpoint/interior alternatives; controlled endpoint shortening; bridge-window lemma; Λ0<κ₀ and parameter-buffer choices. | **P** |
| 3847 — Collision-likely prefixes (`def:collision-likely-prefixes`) | Cold witness; A8 χ-truncated tilted laws, regular cells and precise type rounding; A7 product masses; deterministic lex cumulative intervals; maximal ambient mass; integer discretization and translations. | **D** |
| 3885 — Type estimates (`lem:type-estimates`) | Collision-likely prefix definition; regular partition/profile cost replacements; truncated/untruncated error bounds in A8; multinomial type enumeration and Stirling with rounding losses. | **P** |
| 3928 — Relative cold-set geometry (`lem:cold-geometry`) | Type estimates; disjoint lex product intervals; Nλ_(a_s) maximal-prefix scale; cold-witness inequalities controlling entropy versus block length; integer-interval O(1) rounding; at most twice the component count for the path boundary, including translate clipping. | **P** |
| 4080 — Full collision-likely strings (`def:full-collision-likely-strings`) | Collision-likely prefixes; A8 maximal prefix a_s; A9 chosen bridge word and remaining-tail truncated 2-type family; row multiplicities, collision indicators and their sum. | **D** |
| 4095 — Tail type estimates (`lem:tail-types`) | A9 tail type definition; same regular-cell/Stirling argument as type estimates with tilt 2; truncation error; separate O(ρ_b) loss from removing bridge columns. | **P** |
| 4123 — Relative endpoint theorem for cold prefix families (`lem:uniform-endpoint-theorem`) | A7 count/endpoints; exact first-disagreement side-cylinder decomposition relative to a_s; polynomial-sized family of all side prefixes and ancestors; iterated hypergeometric concentration; bounded total side means/Cauchy–Schwarz and O(log N) depth; ambient mass estimate. No absolute control of the random translate L_(a_s) is required. | **P** |
| 4226 — Cold-prefix endpoint control (`lem:endpoint-control`) | Relative endpoint theorem instantiated at the cold witness and its cold-prefix family. | **P** |
| 4242 — Bridge buffers (`lem:bridge-buffers`) | Cold-witness gap β(s)−Jθ≥β(s)/2+3κ; prefix type estimates; A9 ordered reserved bridge words with selected masses ≥χ or ≥1/k; exact product first moments; truncation and bridge losses below the buffer. | **P** |
| 4282 — Localization (`lem:localization`) | Cold-prefix endpoint control; bridge-buffer expected sizes; iterated concentration simultaneously over the reserved bridge prefix family; deterministic b⁻<lex b<lex b⁺ squeezing; sorted equal-string block geometry. Uniformity over all tail words follows from the common buffers. | **P** |
| 4340 — Fixed-column factorial moments (`lem:fixed-column-factorial`) | A2 independent fixed-count columns and exact labelled-request sampling probability ∏(n_a)_(m_a)/(N)_R; A0 falling factorials; distinct word occupancy interpretation; selected pile lower bounds; uniform falling-factorial/product expansion for R≤N^(1/5), K=O(log N). | **P** |
| 4400 — Conditional fixed-column factorial moments (`lem:conditional-factorial`) | Conditional residual-column uniform law after finitely many prescribed rows; fixed-column factorial-moment argument applied to residual counts; positive selected-pile margins; uniform ratio of conditional/unconditional means. | **P** |
| 4454 — Central-window factorial comparison (`lem:central-window`) | Its quantitative mixed factorial-moment hypothesis; independent Poisson factorial moments; binomial inversion for the collision indicator; absolute coefficient-error sums; factorial-moment tail/truncation control with the stated rates. The moment-to-probability passage must be audited as its own theorem, not assumed from “Poisson approximation.” | **P** |
| 4536 — Fixed-column two-category Poisson bound (`lem:two-category-poisson`) | Fixed-column and conditional factorial moments; central-window comparison; successive/iterated thinning lower tails; Bonferroni and Paley–Zygmund; rare/central/large mean split and uniform conditional mean stability; familywise summation of pairwise covariance errors. | **P** |
| 4738 — Fixed-column occupancy approximation (`lem:occupancy`) | Prefix and tail type estimates; exact bridge product; cold-witness mean cap; selected-pile lower bounds from regular partitions/bridge; two-category Poisson bound; exponent bookkeeping; diagonal variance ≤mean plus uniform off-diagonal covariance sum. | **P** |
| 4832 — Cold collision count (`lem:cold-collision-count`) | Relative cold-set geometry; cold witness Γ−h/2 buffer; bridge/truncation error bounds; occupancy lower expectation and relative variance; Chebyshev and exponent absorption. | **P** |
| 4866 — Many cold edges (`lem:many-edges`) | Cold collision count; localization; distinct full words occupy disjoint constant-string blocks and contribute distinct graph edges; |H_rel|≤N converts N-excess to an H-exponent. | **P** |
| 4899 — Uniform translate-scan ascent bound (`lem:uniform-ascent`) | A10 scan event; relative orders on disjoint pairs are independent Bernoulli(1/2) within each parity class; Hoeffding; |H_q|≤M, M≥N^a, and union over ≤N+1 translates. | **P/S** for permutation concentration foundations |
| 4951 — Block value-set bounded differences (`lem:block-bd`) | A10 uniform fixed-size partition with reservoir; asserted coordinate oscillations; an actual coupling of conditional future block allocations; Doob martingale range bound and Azuma–Hoeffding. The reservoir coupling/range claim is a proof obligation, not an independence assumption. | **P/S** |
| 4979 — Component-value bounded differences (`lem:permutation-bd`) | Block value-set bounded differences; path geometry bounds relevant component count by O(|H|+|∂H|); uniform unordered value sets from a uniform permutation; at most two affected adjacent component comparisons; ΣL_j²=O(M). | **P** |
| 5026 — Lalley component comparison (`lem:lalley-comparison`) | Graph component/run geometry and clipped-boundary accounting; component boundary ascent probability 1/binom(a+b,a); elementary deficit inequality; deterministic expected excess ≥r/6−O(|∂H|); component-value concentration. | **P** |
| 5115 — Lalley cold-spot test (`lem:lalley`) | Uniform translate-scan ascent bound; graph representation conditioned on G; Lalley component comparison at a translate with many graph edges; polynomial-size/boundary assumptions; one common scan event separates laws in TV. | **P** |
| 5167 — Cold-spot lower bound (`prop:cold-lower`) | Cold-witness reduction; relative cold-set geometry; many cold edges at the actual ambient translate; Lalley cold-spot test. | **P** |

## Exact assigned dependency chain

The semantic dependency graph of the compiled finite result is acyclic and independent of the analytic first-moment proof:

```text
pile normalization / legal columns
  -> positive legal digits -> legal full extensions
word prefixes / take / lex order
  -> cylinder compatibility and convexity
  -> first-crossing boundary antichains and unique selected prefixes
  -> compatible joins and pair fiber = join cylinder
finite nonnegative product weights + crossing replacement witnesses
  -> positive side-piece mass for nonterminal compatible pairs
  -> all compatible pairs retained (terminal pairs retained separately)
side-piece full-cylinder characterization
  -> exact continuation invariance of both maxima and c_F
legal log-cost nonnegativity
  -> c_L antitonicity -> concrete Stop persistence
generic finite persistent stopping with terminal fallback
  -> Γ/Λ minimality and antichain -> stable partition
pair fibers + retention + stable partition
  -> exact admissibility iff coverage -> global disjoint decomposition
cylinder convexity + inverse-image transport
  -> disjoint lexicographic rank intervals, allowing empty intervals
```

The corresponding project modules are `Definitions`, `Model`, `Words`, `Mass`, `Boundary`, `Pieces`, `Cost`, `Stopping`, `SourceStable`, `Retention`, and `Global`. `Global` combines the proved modules; it must not import the numerical or probabilistic sketches as axioms. See the aggregate audit for the final build result and theorem-axiom report.

The construction explicitly handles terminal pairs, K=|w| (including the empty horizon), immediate `{join}` stable families, a genuine crossing at K, no-crossing terminal fallback, score equality on the continue/fallback side, probability-one columns, zero piles, empty sampled intervals, and a cardinality-one stopping family that is not `{join}`. Its parent and out-of-domain arithmetic are totalized according to the frozen contract; parent ambient membership is proved whenever an active Γ argument uses it.

## Known quantitative obstruction and affected descendants

The adversarial report gives a concrete counterexample to the anti-concentration display at article 1228–1237. Take k=3, N divisible by 3, equal deterministic first-column piles, w empty, K≥2, χ<1/3, and y=z=x=[1]. Both boundary crossings occur immediately, the pair is admissible/nonterminal/retained, and

`c_F(x) = c_L(x)/2 = (1 − log_N 3)/2`.

The middle first-digit block nevertheless occupies exactly the deterministic middle N/3 ranks. Both endpoint atoms have probability one. Intersecting with an event of probability 1−exp(−N^(δ−o(1))) and conditioning on internal block information cannot yield the claimed N^(−1/2+O(δ)+o(1)) endpoint-atom bound. Tail shuffles do not move that first-digit block. The 2510.22783v1 predecessor excludes the deterministic first coordinate from its fluctuation maxima; the current article includes it. No source definition was changed in the assigned formalization.

The direct invalid node is `lem:ub-ambient-concentration-anti-concentration` **as a combined lemma with that atom assertion**. Its conditional resampling/variance-transfer route in `lem:ub-ambient-conditioning-transfer` also requires a fresh audit; positive expected side masses alone do not prove a nondegenerate conditional variance.

The article's affected route is:

```text
invalid endpoint anti-concentration
  -> edge-density bounds
  -> first moment
  -> conditional first moment
  -> directional Portenko moment
  -> shared-edge exponential moment
  -> deterministic TV upper theorem
  -> random-profile upper corollary
  -> buffered pointwise TV upper bound
  -> four-margin critical upper bound
  -> reduced critical upper theorem / mixing-time upper conclusion
```

Per-edge localization uses the endpoint-concentration portion of the combined lemma; its current source dependency is unavailable until that portion is stated and proved separately, but the atom counterexample alone does not refute the concentration claim. Regularity/sparsity cites quantitative stable estimates without enough separation to certify an independent route. Both are marked accordingly in the table.

The finite stable/global partitions, side-mass positivity, exact continuation invariance, deterministic profile arithmetic, numerical margin calculations, basic one-column inequality, margin dominance, and margin monotonicity are not logical descendants of the false endpoint atom assertion. Nor is the detailed lower proof: its relative endpoint theorem is rebuilt from prefix-count concentration and first-difference decomposition rather than importing this anti-concentration lemma.

No repair is silently assumed. Repairing a future quantitative statement requires a new independently reviewed contract; it cannot be achieved by inserting a nondegenerate-variance hypothesis into the already frozen finite theorem.

## Foundations still needed before extending the Lean proof

1. **Probability realization bridge.** Construct each uniform fixed-count column and their product law; prove admissible conditional residual column laws and independence; identify `ExpectedCount` with actual expected sorted occupancy. Extend to several prescribed labelled rows and exact factorial moments. Sorting preserves multiplicities but is not an independence operation.
2. **Graph law and finite TV.** Define inverse shuffling/interleaving and component sorting; prove the graph representation, component density identities, shared-graph second moment, truncated χ² inequality and sparse factorial estimate. These are prerequisites to either TV conclusion, not consequences of the stable partition.
3. **Conditional exploration.** Specify the exploration algorithm, filtration, directional coverage, accessible blocks, class counts, good-column placement, regular events and small-block treatment. Prove the uniform accessible-size and conditional-distribution statements before freezing the conditional first-moment/Portenko theorems.
4. **One-step and iterated sampling estimates.** Formalize hypergeometric PMF, variance, concentration, point masses and degenerate cases; provide the convex-order/Laplace result used by successive thinning; then prove the tree-wide concentration with its explicit polynomial family bound. Positivity of a side mass does not supply any of these estimates.
5. **Profile analysis and asymptotic uniformity.** Formalize the measurable time-profile data, support-aware costs, finite regular partition and representative bounds, integration and arbitrary-interval blocking, floors, and nested error choices. Turn every uniform o(1) into an explicit quantified bound over its actual block/pair/profile family. In particular r=|w|/log N+o(1) and terminal s=K/log N are not exact identities r=|w|/log N or s=T.
6. **Entropy, witness, and type machinery.** Prove tilted entropy identities/KL inequalities, derivatives and monotonicity, uniform truncation bounds, rounded multinomial type asymptotics, compact witness selection and bridge-buffer inequalities. Upper stable profiles and lower tilted cold families need separate interfaces.
7. **Occupancy and permutation tests.** Prove the factorial-moment-to-collision probability/covariance estimates with all truncation errors; audit central-window inversion and conditional rare-word arguments. Prove disjoint-pair ascent independence, without-replacement block exposure bounds, Lalley component expectation/concentration, and translate scanning.
8. **Random-environment passage.** Prove upper mixture convexity with uniform typical bounds, and separately build a common lower distinguishing event. A conditional lower TV bound cannot be averaged to obtain a mixture lower bound.

These are modules to implement or trusted theorems to identify, not additional axioms or hypotheses that the finite result assumes. This assignment has neither frozen nor certified all of their future theorem statements.

## Random pile-size extension: the two distinct arguments

For the upper bound, if `Good` is the typical set of deterministic cut sequences and the deterministic estimate is uniform there, then

`TV(P(X,K), Uniform) ≤ P(X ∉ Good) + sup_{n ∈ Good} TV(P(n,K), Uniform)`.

This is the argument behind the active random upper corollary at 1999. The deterministic upper route currently has the anti-concentration obstruction just described, so the mixture inequality alone does not complete that corollary.

For the lower bound, let `Test_n` be a deterministic rejection event for each typical cut sequence. Define the **single event** `Test = ⋃_{n ∈ Good} Test_n`. Under a typical realized cut sequence, the mixture accepts at least its own test, so uniform conditional success bounds imply `P(X,K)(Test)→1`. Under a uniform permutation,

`Uniform(Test) ≤ #Good × sup_{n ∈ Good} Uniform(Test_n)`.

There are at most `(N+1)^(kK) = exp(O((log N)^2))` count sequences for fixed k and K=O(log N). The predecessor's uniform false-positive estimate `exp(−N^c)` dominates this count; the extra scan over N+1 translations also fits within that bound. The largest-prefix test can already be chosen as one common increasing-run event; cold sets depend on the environment and require the union/scan construction. The buffered lower result needs uniform positive witness/test exponents over typical cuts.

The active article has a detailed deterministic lower theorem but no separately named active random lower theorem. The inactive overview describes this extension, and 2510.22783v1 §6.2, Lemmas 6.5–6.6, supplies the predecessor many-to-one strategy. It is included here as the requested extension plan, not presented as a completed Lean theorem.
