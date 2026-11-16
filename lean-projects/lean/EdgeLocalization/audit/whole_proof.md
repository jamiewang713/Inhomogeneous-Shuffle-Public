# Whole-proof structure and dependency ledger

Sources are exactly the three files in source_sha256.json. Source line numbers below refer to the untouched unified article. The PDF text extracts are derivative copies of the permitted PDFs. This is a dependency audit, not a declaration that the paper's claims have been proved in Lean.

## Global definitions

1. **Finite model:** N cards, k≥2 digits, K=⌊T log N⌋ independent columns with deterministic nonnegative integral counts summing to N. Legal words use only positive piles; lexicographic sorting gives prefix intervals and the path shuffle graph.
2. **Profile:** simplex D_k, measures μ_t, one-column a,ψθ,Iθ,Hθ, integrals A,Bθ,Jθ. Zero coordinates require explicit zero-term conventions. All finite costs for legal words are finite; zero side masses use a separate −∞ convention.
3. **Approximation:** χ-regular partition, almost-time-profile-like grid counts, all-tail local good columns. Parameter order is fixed before N→∞. The implicit O(δ), o(1), and N₀ dependencies need explicit quantifiers in any asymptotic Lean statements.
4. **Ambient and stable geometry:** prefix w; expected exponent b; cL and cE; left/right first-crossing boundary words; admissibility truncation; side means; min fluctuation cF; retained pair; first stable crossing or terminal fallback. Distinguish a singleton family from an interval containing one card.
5. **Numerics:** β(r,b), local FM and RFM, space-time digit profiles S,Q,R,H, Λ0…Λ3 and thresholds. The two local FM definitions are duplicate notation for one predicate.
6. **Lower witnesses:** product mass λ_w, product interval J_w, labelled survivor sets; largest-prefix word; buffered cold witness; tilted prefixes, bridge, tilted tails, cold set H; collision occupancy and ascent statistics.

## Upper bound

The stable tree partition and global boundary decomposition feed per-edge localization. Concentration supplies block-size and endpoint-window bounds; a separate conditional atom estimate supplies the random-translation bound. Internal collision estimates and these two inputs give the large, small non-singleton, small singleton, and terminal density cases. Truncation and profile counting, followed by the numerical FM inequalities, give the first moment of shared edges.

The exploration phase must independently prove conditional preservation and decompose unrevealed data into accessible ambient blocks. RFM then permits the first moment at each step. Directional Portenko estimates give the shared-edge exponential moment. Regularity and sparsity, the factorial graph-density estimate, and truncated chi-square imply total-variation convergence. The global-to-local margin comparison and one-column dominance reduce four margins to Λ0 and Λ1.

The source's first-column fluctuation definition makes its conditional atom claim and at least two assigned density conclusions false. This breaks the printed proof route before the first-moment theorem. No upper theorem is implemented by assuming those inputs.

**Whole-source reread update:** `whole_tex_reread.md` records a source-assumption-preserving alternative for the small-class contribution. Exact fixed-column unordered-pair counting gives `D_x <= mu_x^4 q_x^2 / 4`; for a small block this gives `D_x <= N^(2cE+8delta+o(1))`. The existing parent-crossing and entropy estimates at theta=3, followed by `B3 >= 2A`, `B2 >= A`, and the tail-size margin, make the entropy-weighted small non-singleton contribution decay. The same exact bound recovers the printed small-singleton exponent, and `D_x <= E e_x <= mu_x` handles terminal singletons. This alternative bypasses conditional atom/window estimates for these small-case density calculations and avoids the low-fluctuation singleton classification. It has been independently reviewed mathematically, not implemented in Lean. Large-block smoothing, per-edge localization, profile/cardinality inputs, and conditional exploration retain their separate proof obligations.

## Lower bound

The largest-prefix branch uses labelled hypergeometric thinning and profile cost A to exhibit a polynomial-size equal-word component; graph sorting creates a long increasing run, rare under uniform measure.

The cold branch extracts a buffered witness from Λ1 when Λ0 is small, counts tilted prefixes, proves relative cold-set geometry, inserts two good bridge columns, and uses a separate relative endpoint theorem to localize collision-likely strings. Fixed-column factorial moments, conditional residual counts, central-window estimates, two-category Poisson comparison, and a second moment yield many cold edges. The translate-scan ascent bound plus component-value bounded differences prove the Lalley test. The final theorem splits on Λ0 and invokes the appropriate branch.

The active lower proof explicitly imports graph representation, regular/profile estimates, and one-step hypergeometric estimates. It does **not** import the false upper ambient conditional atom theorem. Its dedicated endpoint theorem is a separate concentration result. This audit maps its obligations; it does not certify every lower proof.

## Random pile sizes

The active random upper corollary conditions on typical realized cuts and uses uniform deterministic convergence plus mixture convexity. No independence between the pile vectors is required for this conditioning step.

The old random lower blueprint is inside the comment environment at lines 2562–2785. It proposes a union of deterministic tests, with at most (N+1)^{kK}=exp(O((log N)^2)) pile sequences and exponentially small uniform false-positive probabilities. Conditional singularity alone would not imply mixture singularity. The active expanded lower theorem does not state/prove this random extension; the many-to-one test and its uniform rate remain an explicit obligation.

## All active definition/theorem dependencies

The table lists direct conceptual proof inputs, including semantic uses not written as TeX references. A source proof sketch remains an obligation. Statements inside the old comment environment are catalogued separately afterward. Source_declarations.json preserves every extracted statement; its reference lists are syntactic evidence, not certified proof dependencies.

| Line | Declaration | Direct inputs / status |
|---:|---|---|
| 235 | `thm:upper-critical-reduced` — Upper critical-time theorem, reduced form | dominance reduction; buffered consequence; monotonicity; deterministic upper [inherits unresolved upper inputs] |
| 249 | `def:almost-time-profile-like-cuts` — Almost time-profile-like cuts | simplex, time profile, finite Borel partition, grid intervals |
| 265 | `def:randomized-time-profile-like-cuts` — Randomized time-profile-like cuts | almost-time-profile-like cuts; mixture of deterministic shuffle laws |
| 276 | `def:chi-regular-partitions` — $\chi$-regular partitions | simplex; coordinate costs; ψ on [2,4] |
| 305 | `def:good-columns` — Good columns | deterministic column proportions; χ, γ, ρ; tail interval |
| 331 | `def:first-moment-margin` — First-moment margin | A, Bθ; ambient r,b; β(r,b); times r≤s≤u≤T |
| 366 | `def:recursive-first-moment-margin` — Recursive first-moment margin | first-moment margin; accessible ambient blocks from exploration |
| 377 | `thm:deterministic-upper-bound` — Deterministic time-inhomogeneous upper bound | graph representation; truncated chi-square; sparse factorial; shared-edge exponential moment; regularity/sparsity; almost-profile, local-good, RFM |
| 402 | `lem:ub-graph-representation` — Graph representation | fixed-column shuffle matrix; independent uniform permutation; graph components; 2510 Prop 2.2 |
| 410 | `lem:ub-truncated-chi-square` — Truncated chi-square bound | graph representation; density relative to uniform; independent graph copy; Cauchy–Schwarz |
| 424 | `def:local-sparsity` — Local sparsity | integer path; shuffle graph; interval length L |
| 429 | `lem:ub-sparse-factorial` — Sparse factorial bound | local sparsity; union components; graph density factorial formula |
| 490 | `def:ambient-block-size-exponent` — Ambient block and size exponent | legal prefix tree; fixed-column law; prefix cylinders; expectation; cL,cE |
| 521 | `def:boundary-pairs-stable-blocks` — Stable blocks | ambient prefix; legal words; large-pile boundaries; boundary antichains; side pieces; cL,cF; δ; terminal fallback |
| 699 | `def:space-time-digit-profile` — Space-time digit profile | stable block; regular partition; time cells; good/exceptional digits; entropy |
| 749 | `def:numerical-first-moment-margin` — Numerical first-moment margin | duplicates def:first-moment-margin under alternate notation N/mathcal N |
| 788 | `lem:ub-stable-partition` — Stable partition | stable stopping definition; cL monotonicity; first threshold crossing/terminal fallback; lexicographic contiguity |
| 828 | `lem:ub-global-boundary-decomposition` — Global boundary decomposition | first boundary crossing uniqueness; stable partition; admissibility truncation |
| 857 | `lem:ub-regular-partition-interval-blocking` — Regular partition and interval blocking | almost-profile condition; χ-regular partition; grid cover of arbitrary interval |
| 898 | `lem:ub-profile-estimates` — Profile estimates | ambient/stable/profile definitions; regular-partition blocking; actual crossing side mass; relative entropy; parent condition |
| 1039 | `lem:ub-bad-profile-reduction` — Bad-profile reduction | boundary/profile definitions; χ-small exceptional factors; binomial counting; internal edges≤occupancy |
| 1121 | `lem:ub-hypergeometric-estimates` — Hypergeometric estimates | uniform sampling without replacement; explicit one-column law; variance formula; concentration and point masses |
| 1154 | `lem:ub-ambient-conditioning-transfer` — Ambient conditioning transfer | hypergeometric estimates; successive thinning; revealing fields; boundary side masses; claimed non-exhaustion [FALSE as written] |
| 1202 | `lem:ub-ambient-concentration-anti-concentration` — Ambient concentration and anti-concentration | hypergeometric estimates; ambient transfer; prefix sizes; min-side endpoint decomposition; three reveal cases [ATOM CLAIM FALSE] |
| 1436 | `lem:ub-per-edge-stable-localization` — Per-edge stable localization | global boundary decomposition; stable partition; bad profiles; quantitative endpoint tails; ordered parent separation [GAPS] |
| 1486 | `lem:ub-edge-density-bounds` — Edge-density bounds | internal pair-collision first moment; conditional translation atom bound; endpoint windows; stability; size/second moment; large/small/singleton split [LARGE AND SMALL NON-SINGLETON FALSE] |
| 1640 | `lem:ub-terminal-singleton-bound` — Terminal singleton bound | M=K, empty tail product; probability-square≤probability; internal edges≤occupancy suffices exactly |
| 1662 | `lem:ub-numerical-lemma` — Numerical lemma | FM; profile estimates; θ∈[3,4] sign cases; stable/parent inequalities; fallback exclusion; singleton N3 |
| 1817 | `prop:ub-first-moment` — First moment | independent copies; edge-probability-square identity; bad-profile reduction; per-edge localization/cardinality; edge-density cases; numerical margin; profile entropy |
| 1923 | `lem:ub-conditional-preservation` — Conditional preservation | hypergeometric concentration; exploration σ-field; weak perturbations of column counts; accessible size bound [SKETCH] |
| 1931 | `lem:ub-conditional-first-moment` — Conditional first moment during exploration | conditional preservation; RFM; ambient decomposition; first moment; small ambient blocks [SKETCH] |
| 1949 | `lem:ub-portenko-exponential-moment` — Portenko exponential moment | conditional first moment; directional exploration filtration; iterated Laplace bound [SKETCH] |
| 1961 | `lem:ub-shared-edge-exponential-moment` — Shared-edge exponential moment | 2k directional edge cover; Portenko estimates; convexity/Hölder |
| 1974 | `lem:ub-regularity-sparsity` — Regularity and sparsity | prefix concentration; stable estimates; local graph occupancy; union bound [SKETCH] |
| 1999 | `cor:random-time-profile-upper-bound` — Random time-profile upper bound | uniform deterministic upper bound; typical realized cuts; law mixture/TV convexity |
| 2029 | `lem:buffered-pointwise-upper-bound` — Buffered pointwise upper bound | four global negative margins; local-global β identity; accessible exponent bound; deterministic upper theorem |
| 2159 | `lem:upper-margin-monotonicity` — Monotonicity of the upper margins | nonnegative one-column a,ψ; old/new time domains; coefficient signs |
| 2291 | `cor:full-margin-critical-upper-bound` — Four-margin critical-time upper bound | buffered pointwise bound; upper-margin monotonicity; threshold definition |
| 2349 | `lem:basic-one-column-inequality` — The basic one-column inequality | probability simplex; pmax; power sums; θ∈[3,4]; integration |
| 2397 | `thm:dominance-reduction` — Reduction to $\Lambda_0$ and $\Lambda_1$ | basic one-column inequality; β; definitions Λ0,Λ2,Λ3; interval decomposition |
| 2471 | `cor:buffered-consequence` — Buffered consequence | dominance reduction; four-margin critical bound; equality of thresholds |
| 2812 | `thm:buffered-reduced-lower-bound` — Buffered reduced lower bound | largest-prefix vs cold witness split; largest-prefix proposition; cold-spot lower proposition; imported graph/profile/one-step inputs only |
| 3018 | `lem:successive-thinning-tail` — Successive thinning lower tail | labelled survivor sets; independent uniform column subsets; one-step hypergeometric lower tail; residual-count conditioning |
| 3169 | `cor:iterated-hypergeom` — Iterated hypergeometric thinning | successive thinning; hypergeometric estimates; finite prefix tree; multi-level error/union count |
| 3377 | `prop:largest-prefix` — Largest-prefix lower bound | maximal-digit word; profile cost A; iterated thinning lower tail; graph representation; uniform long ascent bound |
| 3498 | `lem:entropy-ineq` — One-column entropy inequalities | tilted p-law; cost/entropy identities; θ derivative and convexity inequalities |
| 3540 | `lem:bridge-window` — Buffered bridge window | local good-shuffle on every tail; buffer parameters; bridge interval including terminal shift |
| 3583 | `lem:cold-witness` — Cold-witness reduction from \(\Lambda_1\) | Λ1 buffered positivity; Λ0 split; entropy inequalities; bridge window; variational endpoint/interior cases |
| 3847 | `def:collision-likely-prefixes` — Collision-likely prefixes | cold witness; prefix product intervals; space-time tilted types; exceptions |
| 3885 | `lem:type-estimates` — Type estimates | collision-likely prefix definition; Stirling multinomial counts; regular cells; exceptional truncation; cost integrals |
| 3928 | `lem:cold-geometry` — Relative cold-set geometry | type estimates; deterministic product intervals; cold witness; bridge buffer; ambient recentering |
| 4080 | `def:full-collision-likely-strings` — Full collision-likely strings | collision-likely prefixes; bridge; 2-tilted tail types |
| 4095 | `lem:tail-types` — Tail type estimates | full collision-likely strings; 2-tilted tail type counting; type-estimate method |
| 4123 | `lem:uniform-endpoint-theorem` — Relative endpoint theorem for cold prefix families | iterated hypergeometric concentration; relative side-piece endpoint decomposition; prefix-family union bounds |
| 4226 | `lem:endpoint-control` — Cold-prefix endpoint control | uniform endpoint theorem; cold witness |
| 4242 | `lem:bridge-buffers` — Bridge buffers | cold witness; chosen two good columns; positive side masses; remaining bridge product |
| 4282 | `lem:localization` — Localization | endpoint control; bridge buffers; iterated thinning; relative integer positions |
| 4340 | `lem:fixed-column-factorial` — Fixed-column factorial moments | uniform deterministic column permutations; ordered distinct row labels; falling factorial counts; column independence |
| 4400 | `lem:conditional-factorial` — Conditional fixed-column factorial moments | fixed-column factorial moments; residual population after conditioning rows |
| 4454 | `lem:central-window` — Central-window factorial comparison | falling-factorial logarithm expansion; explicit sample-size and population regimes |
| 4536 | `lem:two-category-poisson` — Fixed-column two-category Poisson bound | fixed/conditional factorial moments; central window; iterated thinning; two-category occupancy comparison |
| 4738 | `lem:occupancy` — Fixed-column occupancy approximation | two-category Poisson; cold witness; logarithmic bridge/tail restrictions |
| 4832 | `lem:cold-collision-count` — Cold collision count | occupancy; type cardinalities; cold geometry; cold witness; first/second moment |
| 4866 | `lem:many-edges` — Many cold edges | cold collision count; localization; distinct full strings give distinct edges |
| 4899 | `lem:uniform-ascent` — Uniform translate-scan ascent bound | odd/even edge independence under uniform permutation; tail inequality; deterministic translate scan count |
| 4951 | `lem:block-bd` — Block value-set bounded differences | permutation within component value sets; local adjacency-change count |
| 4979 | `lem:permutation-bd` — Component-value bounded differences for component sorting | block bounded differences; uniform component-value reassignment |
| 5026 | `lem:lalley-comparison` — Lalley component comparison | component-value bounded differences; graph sorting representation; boundary loss; expected ascent excess |
| 5115 | `lem:lalley` — Lalley cold-spot test | uniform ascent scan; Lalley comparison; cold edges/size/boundary assumptions |
| 5167 | `prop:cold-lower` — Cold-spot lower bound | cold witness; cold geometry; many edges; Lalley test |

## Inactive old lower blueprint

These 11 declarations occur in a TeX comment environment and are not additional active proof inputs:

- Line 2570: `def:lb-overview-largest-prefix-obstruction` — Largest-prefix obstruction.
- Line 2586: `prop:lb-overview-largest-prefix-lower-bound` — Largest-prefix lower bound.
- Line 2635: `def:lb-overview-cold-spot-obstruction` — Cold-spot obstruction.
- Line 2653: `def:lb-overview-collision-likely-prefixes-cold-set` — Collision-likely prefixes and cold set.
- Line 2663: `lem:lb-overview-cold-set-geometry` — Cold-set geometry.
- Line 2684: `def:lb-overview-collision-likely-full-strings` — Collision-likely full strings.
- Line 2690: `lem:lb-overview-localization` — Localization.
- Line 2698: `lem:lb-overview-cold-collision-count` — Cold collision count.
- Line 2714: `lem:lb-overview-lalley-cold-spot-test` — Lalley cold-spot test.
- Line 2726: `prop:lb-overview-cold-spot-lower-bound` — Cold-spot lower bound.
- Line 2737: `thm:lower-bound-blueprint` — Lower-bound blueprint.

## Inputs required by the assigned edge portion

| Input | Required strength | Audit status |
|---|---|---|
| Legal prefix/stable antichain | Every branch has exactly one stop, including root/singleton/leaf fallback; compatible pair cylinders disjoint | Combinatorial proof route valid; not yet Lean implemented |
| Truncation | Expected removed mass/edge contribution with counted patterns | Polynomial N^{-C₀} loss; cannot be renamed an exponential vertex-coverage loss |
| Prefix size concentration | Iterated fixed-column hypergeometric control, including μ<1, and uniform exceptional event | Requires separate formal probability development |
| Endpoint windows | Quantitative tails at adjustable exponent; min-side orientation; ambient recentering | Source proof needs correction; window claim is not conflated with atom claim |
| Conditional endpoint atoms | Conditional on exact internal information, fine reveal has positive variance/slack; a<b,a=b,a>b | False for first post-ambient column under source definitions |
| Relevant-parent packing | Ordered centers plus lower parent mass and tails smaller than exp(−N^δ) | Not supplied by the stated window bound; exponent comparison in sketch is reversed |
| Internal collision count | Adjacent equal rows inject into distinct colliding pairs; fixed-column pair probability and tail independence | Exact combinatorial portion can be proved without concentration; probability-product portion remains separate |
| Terminal density | Σ p_m²≤E edges≤E occupancy, empty tail product | Exact finite statement valid for all prefixes, including terminal ones |
| Small singleton density | Use factorial/occupancy moments directly and Σ p_m²≤(Σ p_m)² | Alternative proof avoids false endpoint input; needs fixed-column moment formalization |

No prerequisites in this table are postulated as Lean axioms or assumed theorem fields.
