# Whole-proof structure and formalization boundary

The mathematical sources are exactly the supplied TeX, `2103.05068v3.pdf`, and `2510.22783v1.pdf`. The source ledger inventories all 81 labeled declarations (70 active; 11 in the disabled early lower-bound blueprint). Its edges record source citations. This map adds standing definitions, semantic dependencies, and the distinction between a source claim and a kernel-checked theorem.

## Common objects and dependency order

1. Finite deck, alphabet, times, integer pile counts with column sum N → column proportions.
2. Independently uniform fixed-count columns → row words → stable lexicographic sorting → equal-word components of the path → inverse output permutation. Graph representation is a mathematical theorem; it must not become an extra axiom.
3. Column proportions → full/prefix word masses, lexicographic cumulative masses, deterministic cylinder intervals; sampled rows → random counts and interval endpoints.
4. Profile measures, one-column costs a, ψ, tilted laws, I and H → integrated A, B, J → β and global/ambient first-moment margins. Support and zero-coordinate conventions precede logarithms and entropy.
5. Regular partition, time cells, exceptional digits, local good columns, parameter order → empirical space-time digit profiles and their cost/entropy bounds.
6. Probability laws, uniform permutation law, observable events, total variation → hypothesis-test bounds and deterministic/random lower conclusions.

## Upper branch (mapped, not claimed formalized here)

Graph representation → truncated chi-square bound. Local sparsity → sparse factorial estimate. Their combination reduces mixing to a truncated exponential moment of common edges of two independent graphs.

Ambient prefixes and boundary-crossing families → stable stopping partition and boundary decomposition. Regular partition/interval blocking → digit-profile cost and entropy estimates → exceptional-profile reduction. One-step hypergeometric estimates → ambient conditioning transfer → concentration/anti-concentration → per-edge localization and density estimates. Terminal singleton estimates plus numerical first-moment margins complete all size cases. Summing the profile classes gives `prop:ub-first-moment`.

Accessible ambient blocks and recursive first-moment margins → preservation under forward/backward exploration → conditional first moment → directional Portenko exponential moments → shared-edge exponential moment. Typical regularity and sparsity then complete the deterministic upper bound. Averaging a **uniform** deterministic upper estimate over typical random cuts gives the random upper bound.

The separate margin branch is: one-column inequalities → domination of Λ₂ and Λ₃ by Λ₀; integrated costs and accessible-size bounds → recursive margins from buffered global margins; monotonicity plus the required strict negativity → critical-time formulation. None of these implications establishes the lower half of cutoff.

## Lower branch in the active TeX

Largest-word branch: independent column model → exact word mean → successive-thinning lower tail / iterated count concentration → maximal full-word occupancy → long contiguous increasing run → uniform run probability ≤N/m! → observable-event TV lower bound. The finite formalization replaces the concentration step by a directly proved second-moment bound and uses the sharper number N−m+1 of windows.

Cold witness branch: integrated costs + entropy inequalities + positivity of Λ₁ and small Λ₀ → buffered witness (s,u,θ) and bridge window. This requires time-dependent optimization; it does not follow by replacing a homogeneous constant with an integral.

Cold geometry branch: witness → truncated cellwise tilted prefix types → mass/cardinality estimates → relative deterministic cold intervals → boundary/cardinality estimates. The ambient prefix has a random location, so the final observable test scans its possible translations.

Localization branch: prefix-tree concentration + a uniform relative endpoint estimate + two suitable good bridge columns → buffer lengths dominate endpoint errors → every selected full-word occurrence lies in the translated cold set.

Occupancy branch: independent fixed columns → exact joint falling-factorial moments and their residual-count versions → quantitative factorial approximation → two-category occupancy and covariance bounds → concentrated collision-producing word count. Localization transfers those collisions to many cold edges.

Testing branch: uniform permutation comparison patterns → uniform ascent false-positive estimates. Sorted-component expectation and concentration → excess ascents under a shuffle with many cold edges. A union over possible translations gives a common scan event → deterministic TV lower bound. The buffered theorem divides into largest-word and cold branches.

Random lower branch: finite collection of typical environments → their deterministic observable tests → **union of those tests**, with a uniform false-positive bound strong enough to pay the number of environments → average true-positive probability → random-environment TV lower bound. Averaging conditional TV distances alone is invalid.

## Which homogeneous inputs need new time-dependent mathematics?

| Input from the homogeneous proofs | Time-inhomogeneous requirement | Initial formalization status |
|---|---|---|
| Stable equal-word ordering and increasing-run test | Full K-word equality, including stable tie breaking | Finite target |
| Uniform permutation run/ascent estimates | No time dependence; preserve the observable event and window count | Finite targets |
| Binomial word occupancy in 2103 §2.1 | Fixed-column rows are dependent; use exact column counts and independent columns, as in 2510 §6.1 | Finite first/two-row moments and variance target |
| Homogeneous digit type and θ choice in 2103 §6 | Separate time and profile cells; order-sensitive prefix/suffix costs; optimize s,u,θ | Only exact finite profile identities targeted |
| Cold-witness numerical reduction | Endpoint cases θ=3,4, integrated tail costs, quantitative buffer losses, s≤u after bridge shifts | Not certified by the initial finite core |
| Homogeneous deterministic cold set | Relative geometry inside an ambient prefix and a scan over its random location | Finite localization-to-edge transfer only |
| iid empirical-CDF localization in 2103 Lemma 6.6 | Fixed-column dependence and uniform conditional endpoint estimates | Unformalized obligation |
| Collision-likely tail and Poisson/second-moment estimate | Nonidentical columns, small digits, remaining bridge-free tail, bounded labeled-row conditioning, quantitative uniform errors | Exact finite moments only |
| Lalley ascent comparison | A valid component concentration argument and correct clipped-boundary accounting | Unformalized beyond finite ascent combinatorics |
| Random pile extension in 2510 Lemmas 6.5–6.6 | Common test, uniform good-environment estimates, and union cost | Finite union/mixture theorem targeted; no asymptotic cold claim |

## Audit findings that block the advertised matching theorem

* The old blueprint is enclosed in `comment` (TeX lines 2562–2785). Its claims are historical dependencies, not active established results. In particular its near-critical sufficient condition cannot literally imply the stated gap J≤1/2−η.
* Active `lem:block-bd` has a counterexample: with two singleton blocks and an empty reservoir, fixing all other blocks leaves no change available. The oscillation condition is then vacuous for a nonconstant statistic. Its proposed Doob bound is false. This blocks the proof of `lem:permutation-bd` as written, hence the claimed ascent-test chain.
* `lem:two-category-poisson` uses the false pointwise lower estimate (X)₂/2−(X)₃/6≤1_{X≥2}. At X=3 it reads 2≤1. A correct coefficient needs a separately proved argument; the displayed proof cannot be imported.
* A small tail probability in `lem:central-window` does not by itself bound the expectation of the unbounded truncated factorial polynomial on that tail. Its stated coefficient-error estimate also requires tracking logarithmic factors. The factorial-to-occupancy passage remains an obligation.
* For a fixed nonzero regularity mesh, representative replacement costs are generally O(χ), rather than o(1) as N→∞. They must be kept separate from the final N-limit and absorbed only by a declared buffer hierarchy.
* The homogeneous paper `2510.22783v1.pdf` §6.2 contains displayed K restrictions inconsistent with the surrounding cold regime. The finite hypothesis-test statements have no K threshold; these restrictions cannot be copied as formal assumptions.

These findings do not disprove every intended asymptotic conclusion. They prevent importing the supplied proof as a completed theorem. The finite target retains the actual column model, explicit word witnesses, observable permutation events, and quantitative error terms, with no assumptions standing in for the missing cold theorem.

## Independent-review and freeze protocol

The reconstruction, Lean-statement, and adversarial audit reports are retained under `review/`. Every named finite theorem is reviewed by all three roles before the freeze record is created. No Lean source is written before that record. Frozen statements may not be altered; stuck proofs are sent back to multiple agents. New independently reviewed extensions, if needed, receive a separate contract and do not replace an existing theorem silently.
