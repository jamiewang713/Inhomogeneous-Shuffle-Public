# Current input verification and freeze decision

The completed model-specific inhomogeneous first-moment theorem has not been found in the current workspace. The newly available `FirstMoment` package contains proved support results. Its strongest graph estimate retains the missing localization and class-density estimates as hypotheses, so it cannot replace manuscript `prop:ub-first-moment`.

## Independent comparison

All three reviewers reread the intended source proposition and inspected the actual current Lean interfaces independently. Their complete reports are archived in `reviews/`.

| Role | Main evidence | Decision |
| --- | --- | --- |
| Mathematical reconstruction | `expectedCommonEdges_power_bound` operates on an arbitrary `FiniteGraphLaw` and assumes `hloc`, `hU`, error bounds, active multiplicity, and power estimates | Generic assembly is available; the actual shuffle-law applications and uniform source theorem are missing |
| Lean representation | Concrete fixed-count matrices and equality-adjacency graphs are defined; finite probability support exists separately; no declaration connects the source profile hypotheses to common-edge decay | Preserve those representations and prove explicit adapters; do not identify an abstract graph law with the shuffle model by definition |
| Hidden-assumption audit | Adding the aggregation theorem's analytical premises to the upper theorem would assume the missing argument | No certificate, typeclass, or added conditional estimate may substitute for the source theorem |

The source target is unchanged: under its selected-partition almost-likeness, local good-shuffle condition, legal ambient setup, and `FM(r,b,T,eta)`, derive a uniform positive power decay of expected common edges for two independent actual ambient shuffle graphs. The conditional and exponential estimates required by this task remain subsequent proof obligations.

## Fresh Lean checks

Existing source files were copied byte-for-byte into isolated temporary directories, compiled in import order against the matching cached mathlib, and audited using their existing `Audit.lean` files. No original input source or frozen contract was edited. Source hashes were checked again at the end.

| Existing package | Toolchain | Result | Axioms audit |
| --- | --- | --- | --- |
| `formalization/first_moment` | Lean 4.19.0 | All four support modules, root import, and audit compiled | All 29 requested declarations audited; only `propext`, `Classical.choice`, `Quot.sound` |
| `formalization/foundations` | Lean 4.33.1 | All seven foundation modules, root import, and audit compiled | All 74 requested declarations audited; only `propext`, `Classical.choice`, `Quot.sound` |

Thus 103 existing support declarations were freshly checked. This count is not a count of newly formalized upper-bound results and does not include any actual shuffle exponential-moment estimate.

Machine-readable evidence and full compiler output:

- `first_moment-revalidation-build.json` and `.log`
- `foundations-revalidation-build.json` and `.log`
- `verify_existing_inputs.py`, which performs only unchanged-source snapshot checks

## Compatibility check

The unchanged first-moment package was also tested against the foundations' Lean 4.33.1/mathlib environment. Compilation stopped in `FirstMoment/Assembly.lean:202`: the newer `add_le_add_left` has the opposite addition-side convention from the proof's use. The current 4.19.0 proof is valid in its pinned environment. A proof-script port is needed before these sources can be imported into a single 4.33.1 project. No statement was changed or port authored during this pre-freeze check. The test stopped at the first module failure, so compatibility of the remaining modules under 4.33.1 is not claimed.

The independently inspected `lean/EdgeLocalization` artifacts use a third version, Lean 4.24.0; they were not part of the fresh 103-declaration audit. Its density inequalities also retain expected collision counts and do not supply the missing asymptotic estimate.

Compatibility evidence is in `first_moment_4_33_1-revalidation-build.json` and `.log`. Toolchain integration is an implementation issue separate from the missing model theorem.

## Exact handoff gap

`InhomogeneousShuffle.FirstMoment.expectedCommonEdges_power_bound`, at `formalization/first_moment/FirstMoment/Assembly.lean:177`, proves

    E(common edges) <= 2*N^(-d) + 2*N^(ell+c-a)

only after receiving the actual edge-localization bound (`hloc`), per-class squared-density bound (`hU`), error bound, active-set bound, and all four power bounds. The source profile, cuts, good columns, numerical `FM`, and ambient construction do not appear in its hypotheses. `two_power_terms_eventually` proves the final arithmetic absorption under strict exponent inequalities; it does not prove that the model yields those inequalities.

The missing input must give the actual file and declaration deriving the source first moment from its original model assumptions, with its exact ambient law, normalization, time grid, partition quantifiers, threshold hierarchy, and uniform constants. Those details determine the valid conditional-robustness application during exploration. If the completed declaration is outside this workspace, its source and project dependencies are required for a checked import.

## Freeze and completion status

The upper-bound global freeze remains pending. No new Lean proof has been authored by this task, no missing estimate has been introduced as an assumption, and no additional axiom or placeholder has been introduced. The complete proof/dependency map and reviewed alternatives remain available, but the requested exponential moments and total-variation upper bound are unproved.

The original three mathematical source hashes still match the source inventory. Unrelated workspace edits were preserved.
