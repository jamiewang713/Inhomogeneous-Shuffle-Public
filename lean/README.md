# Shuffle probability formalization

This directory formalizes the assigned finite probability and hypergeometric core in Lean. It does **not** certify the whole shuffle theorem. In particular, the manuscript's ambient non-exhaustion claim is false as written; no additional reserve assumption has been substituted for it.

## Contract and source review

The mathematical sources are exactly the three files specified by the user. The full upper-bound, lower-bound, and random-pile proof structure, all 70 active numbered declarations, and their semantic dependencies are recorded in [the proof ledger](audit/proof_structure.md). The nine probability-space interfaces are listed there as well.

Three independent agents reviewed the probability argument, Lean representation, and missing hypotheses. Their reports and per-target reviews are in `audit/`. The [comparison](audit/comparison.md) records the disagreements resolved **before** implementation. [FROZEN_CONTRACT.md](audit/FROZEN_CONTRACT.md) fixes all mathematical definitions and statements. Its immutable SHA-256 digest is recorded with the source digests in [freeze_manifest.json](audit/freeze_manifest.json).

The source manuscript has not been edited. No unfinished mathematical statement is represented by a Lean declaration.

[implementation_index.json](audit/implementation_index.json) lists every public declaration and module import. [lean-dependencies.json](audit/lean-dependencies.json) is extracted directly from the checked Lean environment: it records the project and trusted-library dependencies of all 606 project declarations and generated helpers. This complements the manuscript's semantic dependency ledger.

## Implemented core

| Frozen targets | Lean modules | Main results |
|---|---|---|
| F1–F2 | `FiniteLaw`, `FiniteLawExtras` | Normalized finite laws; finite union bound; linearity; variance identity; Markov and Chebyshev; mathlib PMF and measure bridges |
| F3–F5 | `Conditioning` | Positive-event conditioning; uniform fibres; null-atom identities; conditional tower bounds; fine-to-coarse restricted-event point-mass transfer; product conditioning |
| H0 | `Hypergeometric`, `SubsetSampling` | Binomial-coefficient law normalization, exact support, and uniform labelled-subset sampling semantics |
| H1–H3 | `HypergeometricMoments` | Expectation, all factorial moments, exact variance, and the complete zero-variance characterization |
| H4 | `HypergeometricBoundary` | Explicit degenerate point laws and zero positive centered-deviation tails |
| H5, H7 | `HypergeometricConcentration` | Exponential concentration with absolute constant `c = 1/4`; the without-replacement transform inequality |
| H6 | `HypergeometricAntiConcentration` | Every point mass is at most `4 / sqrt variance` when variance is positive |
| C1, C3 | `ResidualSampling` | Exact fixed-row residual law and hypergeometric transitions on positive reveal atoms, retaining the full population where required |
| C2, D6 | `FixedColumns` | Uniform legal fixed-histogram columns; prescription admissibility; uniform residual columns and preserved conditional independence |
| C4 | `ConditionalHypergeometric` | Named conditional moment, variance, concentration, transform, and point-mass theorems, with the original premises |
| D2, D6 | `FiniteMixture`, `RandomColumns` | Arbitrary finite laws on complete feasible pile arrays; exact conditional independent-column laws at positive pile-array atoms |
| N1–N2 | `NonExhaustion` | Variance lower bound from explicit reserves; residual complement and fraction-error arithmetic |
| X1 | `AmbientCounterexample` | The full-sample residual law has positive mean and positive marked/unmarked populations but zero variance and an atom of mass one; fixed histogram endpoints are deterministic |
| X1 realization, F3–F4 | `AmbientMatrixCounterexample` | Explicit matrices for both frozen examples; actual marked/sample intersection; conditional deterministic laws on positive events and reveal atoms; a conditional endpoint bound forces `2*P(S) ≤ b` |

The finite law handles empty populations without an artificial positive-size hypothesis. Hypergeometric feasibility is part of the parameter type. Real casts precede subtraction in the mean and variance formulas. Conditional laws require positive events; the literal quotient on a null event is never claimed to be a normalized law. No within-column row independence is assumed.

## Obstruction in the manuscript

For residual parameters `N = 2L`, `K = L`, `m = 2L`, with `L ≥ 1`, the sample is the whole residual population. Consequently `Y = L` with probability one and the sample complement is zero. The source's root-ambient first-column examples with piles `(L,L,L)` or `(L,1,L)` realize this mechanism. Their middle-block endpoints are fixed by the histogram.

`AmbientCounterexample.lean` certifies these exact finite probability and counting facts. `AmbientMatrixCounterexample.lean` realizes both examples in the actual uniform fixed-column product experiment with at least two columns. Its residual variable is the marked/sample intersection, and the sample is the entire residual population. The conditional count law, mean, variance, and unit endpoint atoms are checked on every positive event; the actual middle-row reveal is a named specialization. No residual-assignment uniformity is claimed under arbitrary conditioning.

The new realization was independently reviewed and frozen in [FROZEN_X1_REALIZATION.md](audit/FROZEN_X1_REALIZATION.md) before its code. It preserves the original frozen contract. The finite tower theorem `retained_bound_forces_small_probability` shows that a uniform bound `b` on the sum of the two restricted endpoint point probabilities would imply `2*P(S) ≤ b`.

The manuscript's crossing, admissibility, fluctuation and stability premises are checked explicitly in [the source-premise recheck](audit/x1_source_premise_recheck.md). Those source-level checks are not a Lean formalization of the entire prefix tree or asymptotic notation. The manuscript's claimed ambient non-exhaustion and endpoint anti-concentration theorems have therefore **not** been implemented as true theorems. The general valid conditioning transfer F5 remains available. A corrected shuffle application requires an explicitly reviewed replacement statement and an actual reserve proof.

## Toolchain and checking

The sources are pinned to Lean `4.19.0` and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The local cached compiler and dependencies are in ignored `.tooling/`; individual modules are checked with, for example:

```sh
./check-all.sh
./check.sh Shuffle/HypergeometricConcentration.lean
```

`check-all.sh` also verifies the frozen source digests, checks the proof sources for prohibited declarations and tactics, and audits Lean's transitive foundational dependencies. `audit/verification.json` and `audit/axiom-report.txt` record the successful check and the exact source digests.

The final build checked all 17 implementation modules and audited 207 public definitions and theorems. The only foundational dependencies reported were `propext`, `Classical.choice`, and `Quot.sound`. Harmless linter warnings about unused frozen premises were left in place; no premise was removed to silence a warning. See [the verification summary](audit/final_verification.md).

`lean-toolchain` and `lakefile.lean` provide the same pins for a standard Lake setup. Verification reports distinguish successful kernel checks from source-level integration obligations.
