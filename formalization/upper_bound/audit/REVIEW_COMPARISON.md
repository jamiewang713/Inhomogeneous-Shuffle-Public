# Pre-freeze comparison of independent reviews

Status: **not frozen; no upper-bound Lean proofs authored; no exponential-moment theorem checked**.

Three agents independently read the old proof sketch and the two permitted papers. Their initial source reviews were independent; subsequent proposed repairs were discussed explicitly. The raw reports are retained in `reviews/mathematical-reconstruction.md`, `reviews/lean-representation.md`, and `reviews/assumptions-audit.md`.

## Comparison by assigned family

| Family | Mathematical reconstruction | Lean representation | Assumptions audit | Primary decision |
|---|---|---|---|---|
| Shuffle graph | Induct on prefix refinement under fixed-count columns | Finite valid-matrix type; independently defined actual shuffle; prove sorting coupling | Chronology and independence of uniform permutation must be explicit | Suitable finite interface; composition convention still to be fixed in full manifest |
| Radon–Nikodym | Count component-sorting fibers; exact factorial-ratio overlap | Finite real density sums, with a PMF bridge if required | Pointwise overlap minus one can be negative | Prove exact density and mean-one identities before truncation |
| Truncated chi-square | Radicand is a squared norm | Generic normalized finite-density theorem | Typicality must be one-matrix event, used on both independent copies | Same statement agreed by all three |
| Sparse graphs | Union-component factorial combinatorics transfers | Edge positions as a finite set; interval components | High-probability sparsity is distinct from deterministic factorial bound | Separate the deterministic and probabilistic obligations |
| Directional covering | First-pile rank intervals and guarded left/right cutoffs | Explicit edge sets and integer endpoint bounds | Empty and tiny initial piles invalidate uniform strict mass claims | Include a proved small-pile branch and derive short guards from local density |
| Exploration | Constrained residual-matrix counting; prefix partition | History maps with refinement; condition additionally on tail count arrays | Sorted-history constraints invalidate an IID-row substitution | Preserve the exact finite residual counting law |
| Unrevealed shared edges | Repeats plus three block-size regimes | Conditional copies, finite Jensen, aligned block resampling | Keep both histories' self-intersection average; pay `N^(C rho)` block cost | No direct inference from the unconditional first moment |
| Exponential moments | Successful-history first-hit argument | Adapted killed count; geometric tail theorem | Future-event filtration step in 2025 Lemma 5.4 is invalid | Replace that proof, keeping its conclusion and source model assumptions |
| TV upper and random piles | Truncation + factorial excess + atypical probability | Uniform finite quantitative bound then averaging | A conditional framework with unproved moment input is not completion | Completion gated on actual proved conditional and exponential estimates |

The Lean review's provisional residual-row estimate R1 uses the global prefix mass. That statement is **not adopted**: subsequent comparison identifies the correct conditional mass `q_x = lambda_x / p_p` inside initial pile `p`. Its cancellation occurs only after summing over at most `n_p` rows. The corrected normalization belongs in the future freeze manifest.

The mathematical and assumptions reviewers give two versions of adapted killing. The preferred interface bounds the exponential **excess** on the good event directly through first-hit events. This avoids losing a bad-event term by subtracting one from an unnormalized truncated expectation. No version is presently asserted as a checked Lean theorem.

## Confirmed failure of literal conditional preservation

The manuscript's lemma at line 1923 claims preservation of exact almost-profile-likeness after conditioning. Its proposed justification uses coordinate concentration. That implication is false for the stated class of Borel partitions.

Take `k=2`, `N` divisible by four, and every column balanced: `p=(1/2,1/2)`. Use the constant profile concentrated at `p`, and a sufficiently fine regular partition containing a boundary at first coordinate `1/2`, assigning `p` to the upper-side cell. Further subdividing either side preserves the relevant separation and can make the partition regular. Original columns all lie in that same cell, so their cell counts agree with the profile.

Condition on the labeled rows of the first-prefix block, which has size `N/2`. In every independent later column, the count `Y` of zeros in this block has law

`P(Y=r) = choose(N/2,r) choose(N/2,N/2-r) / choose(N,N/2)`.

It is symmetric around `N/4`. Hence

`P(Y < N/4) = (1 - choose(N/2,N/4)^2 / choose(N,N/2)) / 2 -> 1/2`.

The normalized conditional pile vector lies below the coarse boundary in an asymptotic fraction `1/2` of the later columns. Its exact cell frequencies do not approximate the point-mass profile, although its coordinates converge to the original proportions. This is a failure of the proposed preservation mechanism, already before imposing additional lexicographic constraints. Recursive numerical margins cannot repair cell membership.

Two candidate repairs remain distinguished:

1. Derive a first-moment corollary stable under small coordinate perturbations from the completed checked theorem's actual prerequisites. The 2025 paper explicitly uses a weak-almost-like hypothesis for its Proposition 4.2.
2. Before the global freeze, choose a coarse regular partition with null boundary for the integrated profile measure, and make the original selected input partition a refinement resolving thin bands around those boundaries. Prove that only a small proportion of columns can cross a coarse boundary. This may permit application of an exact-cell first-moment theorem to the coarse partition, without a new final model hypothesis. Its quantifiers and all-tail uniformity require review; it is not yet established.

Neither candidate may be entered as an assumed theorem field.

The subsequent focused review was performed independently in all three roles. All three verified the finite guard-band construction, including accumulated rounding error. Their reports are in `reviews/robustness-mathematical-reconstruction.md`, `reviews/robustness-lean-representation.md`, and `reviews/robustness-assumptions-audit.md`. The usable formulation splits each coarse cell into its intersection with the band and its complement, keeping at most twice as many cells regardless of band width. The transfer is valid with the single fine partition selected before the cuts. It still does not authorize changing an arbitrary previously fixed partition. The actual first-moment input must resolve its partition quantifiers, fixed versus reset time grids, base-population normalization, and uniform constants. Coordinate perturbation also changes a good-column threshold from `g` to, for example, `g/2`; that derived loss must be specified before freeze.

## Other confirmed substitutions that must be avoided

| Issue | Required correction |
|---|---|
| 2025 Lemma 5.4, p.35: enlarge history by the terminal good event and use the tower identity in the wrong direction | Keep the natural history; use adapted survival up to finite first-hit times |
| 2025 Lemma 5.6, equation (5.10): select one of two fixed conditional histories by symmetry | Bound the average of both self-intersection terms, each uniformly |
| Good first column interpreted as all its piles being large | A good column supplies at least two large piles; use normalized conditional prefix masses and a small-pile case |
| 2025 equation (5.37): incorrect reciprocal bound on the outside-pile reservoir | From `p_p <= 1-chi` only `1/(1-p_p) <= 1/chi` follows |
| Prefix refinement described as having `N^o(1)` or only `O(log N)` blocks | Record `2kK * k^(O(rho log N))`; subtract its explicit exponent from the decay margin |
| All small blocks controlled by total size | Add a tail-collision estimate for the expected-size-near-one regime |
| Current repeated string omitted from future strict-prefix blocks | Count the extra copies separately and respect forced observed multiplicity |
| Arbitrary pair typical event substituted in truncation | Define one set of matrices and use its product under the independent pair law |
| Backward exploration interpreted as time reversal | Reverse the spatial/lexicographic direction and, if used, digit order; preserve chronological columns |
| Homogeneous shift applied without changing the profile | Keep absolute times and budget the deleted prefix's cost |
| A short vertex interval assumed to meet at most two initial piles | Tiny piles can invalidate this; use all fixed `2k` directions or prove a suitable exclusion |
| Truncated Laplace bound converted to exponential excess by subtracting one | Subtract the event probability, or prove the excess directly |

## Why the first moment cannot substitute for exponential moments

This is an abstract graph-law diagnostic, not a counterexample to the shuffle theorem. Let `H_N` have an edge every four vertices, and let `G=H_N` with probability `N^-q`, otherwise empty; take an independent copy `G'`. For fixed suitable `L`, all possible graphs are `L`-sparse. If `q>1/2`, then

`E|G intersect G'| = O(N^(1-2q)) -> 0`,

but

`E exp(t|G intersect G'|) >= N^(-2q) exp(c t N) -> infinity`.

Thus both the particular shuffle law and the conditional estimates must enter the exponential-moment proof. Kernel-checking a final theorem that simply assumes the desired exponential moment would leave the assigned central task undone.

## Checked environment facts and outstanding input

The initial workspace scan found no project Lean declarations, root module, Lake project file or toolchain file outside dependency/tooling caches. `formalization/.tools/lean/bin/lean --version` returned Lean 4.33.1, matching the cached mathlib toolchain. That is an environment check, not a proof build.

That initial inventory is superseded by the current input revalidation. New foundation and first-moment support sources are now present. Three independent reviewers compared their exact statements against `prop:ub-first-moment`; all found that the actual model theorem remains missing. The root freshly compiled and audited 74 foundation declarations and 29 first-moment support declarations in isolated, unchanged source snapshots. These successful builds establish those support results only. `expectedCommonEdges_power_bound` still takes localization, density/class control, and power estimates as premises. The full comparison, hashes, and build results are in `INPUT_REVALIDATION.md` and the three `reviews/input-revalidation-*.md` reports.

The user has been asked for the path and declaration name of the completed inhomogeneous first-moment Lean theorem. Its exact ambient law, alignment, parameter order, perturbation tolerance, constant dependence, large-`N` threshold and trust dependencies must be inspected before the input can be frozen. No replacement assumption has been introduced.

A small exact enumeration at `N=3`, cuts `(1,2)` followed by `(2,1)`, verified that chronological fixed-column lexicographic sorting has the same distribution as inverse physical shuffle composition in that example. This supports the proposed convention but does not replace the general representation proof.

No upper-bound global freeze manifest is marked approved. No upper-bound Lean proof has been authored. Existing input source files were copied unchanged into temporary directories for compilation; their original files and frozen contracts were not modified. The requested upper-bound theorem, in particular its model-specific exponential moments, remains unproved.
