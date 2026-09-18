# Finite lower bounds for time-inhomogeneous riffle shuffles

This project contains **74 kernel-checked Lean theorems**, including deterministic and random-pile-environment lower bounds in the independent fixed-column matrix model. All statements were independently reconstructed, designed for Lean, and audited before the immutable [contract](FREEZE.md) was recorded. The full time-inhomogeneous cold-spot asymptotic theorem is deliberately not claimed.

## Main results

[LowerBounds.lean](RiffleLower/LowerBounds.lean) proves `deterministic_lower_bound`. Write

\[
\mu=N\prod_{t=1}^{K}\frac{n_t(w_t)}{N}
\]

for the expected number of copies of an arbitrary **complete** word. For
\(N\ge2\), \(1\le m\le N\), and \(m<\mu\),

\[
d_{\rm TV}(P_c,U_N)
\ge 1-\frac{\mu}{(\mu-m)^2}-\frac{N-m+1}{m!}.
\]

Choosing a maximal pile at each time maximizes this word mass, by the proved `maximal_digit_word_mass` product inequality. The conclusion uses a contiguous increasing run, not an arbitrary increasing subsequence.

The same file proves `random_pile_lower_bound`. If a typical environment set has probability at least \(1-\varepsilon\), and every typical environment has \(\mu_e>m\) and
\(\mu_e/(\mu_e-m)^2\le\delta\), then, for nonnegative \(\varepsilon,\delta\),

\[
d_{\rm TV}(P_{\rm mixture},U_N)
\ge 1-\varepsilon-\delta-\frac{N-m+1}{m!}.
\]

The run event is common to all environments. The proof averages its success probability; it never averages conditional TV distances. Random environments may have arbitrary dependence between their pile sizes at different times.

The concrete model starts from base column functions with the prescribed integer multiplicities. A uniform tuple of column permutations supplies independent uniform column randomizations. The output permutation maps sorted positions to original row labels and is defined by stable lexicographic sorting of complete row words. A separate equivalence with a separately defined physical cut/interleave process is outside this project.

## What is proved

| Module | Checked content |
|---|---|
| [FiniteProbability](RiffleLower/FiniteProbability.lean) | Finite laws, half-L1 TV, event bounds, union tests, common-event and random-environment transfer, variance and Chebyshev inequalities |
| [FixedColumns](RiffleLower/FixedColumns.lean) | Exact one-/two-row probabilities from finite permutation symmetry; independent-column product identity; exact occupancy moments; variance at most the mean; finite lower tail |
| [Sorting](RiffleLower/Sorting.lean) | Stable tie ordering, exact contiguous equal-word fiber, multiplicity forcing an increasing run |
| [UniformPermutation](RiffleLower/UniformPermutation.lean) | Exact \(1/m!\) order probability, \((N-m+1)/m!\) run bound, comparison probability \(1/2\), ascent expectation \(|E|/2\) |
| [Profiles](RiffleLower/Profiles.lean) | Exact time-cell digit counts and products, legal-word logarithmic cost, coordinatewise maximal-word inequality |
| [Cold](RiffleLower/Cold.lean) | Cold-exponent algebra; localized repeated words supply distinct adjacent equal-word edges; these edges are ascents |
| [LowerBounds](RiffleLower/LowerBounds.lean) | The two finite lower bounds displayed above |

Zero piles and deterministic columns are allowed. No hypothesis relating K to log N, positive lower bound on every pile, profile regularity, or replacement of a homogeneous cutoff constant by an integral occurs in either endpoint.

## Proof map and audit

* [Whole-proof map](audit/proof-map.md): upper branch, both lower obstructions, random extension, and the new time-dependent mathematics required by the cold branch.
* [Source declaration ledger](audit/source-dependencies.md): all 81 labeled declarations in the supplied TeX, distinguishing the 70 active declarations from its disabled earlier blueprint.
* [Elaborated Lean dependency graph](audit/lean-dependencies.md): exact direct dependencies for all 117 project definitions and theorem declarations, extracted from Lean types and proof terms. The [JSON](audit/lean-dependencies.json) also records trusted-library dependencies.
* [Theorem inventory](audit/theorems.md), [build log](audit/build.log), and [per-theorem axiom audit](audit/axioms.txt).
* Independent [reconstruction](review/reconstruction.md), [statement design](review/lean-statements.md), [adversarial audit](review/threshold-audit.md), and [endpoint audit](review/final-integration-audit.md).

The final source signatures match the frozen finite scope. Redundant exported decidability parameters noticed during review were replaced by local classical instances. The build retains a harmless unused-finite-instance warning to preserve the frozen statement rather than weaken its parameter list.

The axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`, the standard Lean foundations used by trusted mathlib. There are no custom axioms, unproved placeholders, or native evaluation oracle dependencies. The three mathematical source files and the frozen contract are unchanged; their checksums are retained under `audit/`.

## Remaining mathematical work

The supplied cold proof contains a false block bounded-difference lemma and an incorrect Bonferroni coefficient. Its critical-window factorial truncation and some uniform profile/endpoint estimates also need further proof. The project therefore does **not** claim:

* a cold witness from the positive integrated upper margin;
* probabilistic construction/localization and concentration of time-inhomogeneous cold spots;
* exponential ascent scan bounds or the full matching cutoff;
* the corresponding asymptotic random-pile cold-spot theorem.

The finite cold transfer theorem has its localization hypothesis stated explicitly. It is not presented as a proof of probabilistic localization. The upper bound is mapped but not formalized by this lower-bound deliverable.

## Rebuild

From this directory, run:

```sh
python3 build.py
```

The checked local setup uses Lean **4.19.0** and the compatible trusted mathlib source/cache already present in `../formalization/.tooling/`. The build reuses those read-only files and compiles missing trusted modules into this project's `.lake/dependency-cache`. It requires no new network access and does not modify the neighboring project.

For another local installation, set `RIFFLE_TOOLCHAIN` to the Lean 4.19.0 installation directory and `RIFFLE_MATHLIB` to its compatible mathlib checkout with dependency caches. The included Lake configuration uses the current workspace's mathlib path; `build.py` is the verified build entry point.

The build checks the freeze checksum, rejects prohibited proof constructs, compiles every module, audits every theorem's axiom closure, records source hashes, and regenerates the exact dependency graph. Review-stage candidate documents are historical; `FREEZE.md` is authoritative.
