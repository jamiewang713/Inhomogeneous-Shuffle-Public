# Inhomogeneous riffle-shuffle finite foundations

This Lean library proves all **74 frozen foundational results**: 73 theorems and one finite-type instance. The complete library builds with Lean **4.33.1**, using mathlib commit **0df444a360eaa60ab8c11dca51a86af692955474**.

The mathematical sources are exactly:

- `time_inhomogeneous_riffle_shuffle_unified_article.tex`
- `2103.05068v3.pdf`
- `2510.22783v1.pdf`

Trusted Lean and mathlib files supply implementation APIs and proved library results. No other project paper or project theorem is imported.

## Build and verification

From this directory, run:

```sh
./scripts/check.sh
```

The script builds the full library, checks the logical dependencies of every frozen result, verifies the unchanged contract hash and exact declaration inventory, rejects placeholder proofs or extra axioms, and exports the kernel-reported dependency graph. In this workspace it uses the existing local Lean runtime and cached dependencies. With the pinned toolchain installed normally, the project also supports:

```sh
lake build
lake env lean Audit.lean
lake env lean Dependencies.lean
python3 scripts/verify.py
```

The local `.tools` and `.lake` caches are not source deliverables. `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the reproducible build.

## Proved interfaces

| Module | Frozen IDs | Content |
| --- | --- | --- |
| `RiffleShuffle/Basic.lean` | definitions | Profiles, words, legality, prefix relations, finite tree nodes, cylinders |
| `RiffleShuffle/Profiles.lean` | P01–P14 | Normalization, positive support, existence of a positive pile, product masses and total mass |
| `RiffleShuffle/Words.lean` | W01–W14 | Prefix calculus, lexicographic truncation, convexity, legal full extensions |
| `RiffleShuffle/PrefixTree.lean` | T01–T15 | Root and parent, finite legal tree, children, cylinder overlap, antichain partition |
| `RiffleShuffle/Matrices.lean` | M01–M12 | Existence of fixed-count matrices, labelled rows, sorting permutation, occupancy preservation, exact rank endpoints |
| `RiffleShuffle/Graphs.lean` | G01–G07 | Path subgraphs, restricted/shared edges, connected components exactly equal full-word classes |
| `RiffleShuffle/Intervals.lean` | I01–I12 | Weighted half-open intervals, disjointness and coverage, legal support, open lexicographic interval convexity |

Import `RiffleShuffle` for the complete library. `theorem-manifest.json` maps each frozen ID to its fully qualified Lean declaration. `dependencies.json` records dependencies between all public project declarations and their directly used trusted constants, expanding generated proof helpers. `kernel-dependencies.json` retains the underlying raw kernel data, including generated constants.

## Frozen assumptions and independent review

`CONTRACT.md` is the unmodified pre-implementation contract. `FREEZE.md` records its hash and freeze time. Each of three independent agents read the source sketch and supplied both an independent report and a per-ID review: mathematical reconstruction, Lean representation, and adversarial assumption/counterexample checking. Their reports and the post-implementation audits are in `reviews/`.

The source profile assumptions are N>0, k≥2, natural counts summing to N in each column, and a finite natural horizon K. Zero counts and K=0 are supported. Matrix existence and sortedness are proved rather than assumed. Prefix legality does not imply positive realized occupancy. The library adds no probability, independence, regularity, concentration, or asymptotic assumptions.

Every audited result uses at most the standard trusted Lean foundations `propext`, `Classical.choice`, and `Quot.sound`. There are no additional axioms, `sorry`, `admit`, or unproved placeholder declarations. Results and evidence are recorded in `axiom-audit.json` and `logs/`.

## Explicit endpoint correction

For a prefix of length m, empirical endpoints compare **length-m truncations of the sorted rows**. Ranks are zero based, so the occupied positions are `[L,U)` and the count is `U−L`, including empty blocks. The sketch's direct full-row comparison `sᵢ ≤lex w` excludes strict extensions of a proper prefix. The frozen definition corrects that notation using the older paper's §4.1.1 convention. The off-by-one expectation notation in 2510.22783v1 (2.15) is also explicitly excluded; deterministic interval endpoints use cumulative word masses.

## Whole proof and scope boundary

`PROOF_MAP.md` gives the upper-bound, matching lower-bound, and random-pile-size dependency structure. `article-reference-dependencies.json` indexes all 70 active labelled result/definition environments in the sketch, excluding its commented obsolete overview. That JSON is a lexical reference index; the reviewed tables supply the mathematical dependencies, including delayed proofs.

The probabilistic graph representation, concentration and analytic estimates, final mixing bounds, and random-mixture limit theorems are not formalized by this finite assignment. The random upper extension uses uniform deterministic bounds and total-variation convexity. A random lower extension needs a common separating event and uniformly small false-positive estimates; averaging deterministic lower bounds does not suffice. The stronger `2Kk` prefix decomposition of an open lexicographic interval and integer boundary estimates are recorded as later finite dependencies, with no Lean placeholders.
