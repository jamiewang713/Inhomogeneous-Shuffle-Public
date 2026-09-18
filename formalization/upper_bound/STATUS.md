# Formalization checkpoint

The requested upper bound is **not complete**. The goal is blocked pending the completed actual-model first-moment theorem; the same missing-input condition was revalidated across three consecutive goal turns (see `audit/BLOCKED_AUDIT.json`). The upper-bound global freeze remains pending, and this task has authored no Lean proofs. In particular, the shuffle's exponential-moment estimates remain unproved.

Completed preparatory work:

- Read the three authorized mathematical sources and recorded their hashes.
- Mapped the whole upper, active lower, and random-pile proof structure.
- Inventoried 70 active named declarations and 11 declarations in the commented old lower overview.
- Built an acyclic intended dependency map for all 70 active declarations, including corrections from an independent review.
- Obtained and compared independent mathematical, Lean-representation, and hidden-assumption reports for every assigned upper-bound family.
- Obtained and compared a second round of three independent reviews of a possible partition-robustness repair.
- Reconstructed an exact finite first-hit proof of the truncated exponential-excess implication without the invalid terminal-event filtration step.
- Revalidated newly available Lean inputs in another round of three independent reviews.
- Freshly compiled unchanged source snapshots and audited 29 existing first-moment support declarations under Lean 4.19.0 and 74 existing foundation declarations under Lean 4.33.1. All 103 audits use only standard Lean axioms.
- Tested the unchanged first-moment sources under Lean 4.33.1; a proof-script compatibility error occurs in `Assembly.lean:202`. No input source or frozen contract was modified.

The required **completed model-specific inhomogeneous first-moment Lean theorem** is still missing from the inspected workspace. The earlier statement that no project Lean files were present is superseded: substantial support files now exist and have been checked. However, `InhomogeneousShuffle.FirstMoment.expectedCommonEdges_power_bound` still assumes localization, per-class density, and power estimates. It does not derive the source first-moment proposition from its cut/profile assumptions. All three reviewers agree on this distinction. The user has been asked for the exact completed theorem's file and declaration; missing analytical estimates cannot be inserted as new assumptions.

The exact input must settle the ambient law and alignment, original-deck versus subdeck normalization, absolute time grid, partition quantifiers, good-column thresholds, parameter hierarchy, decay constants and uniform large-`N` threshold. These determine whether the reviewed coarse/fine partition construction is a valid application of the existing theorem.

Next required actions after obtaining that input:

1. Inspect the actual theorem and its trust dependencies; match the first-moment boundary without altering it.
2. Finish the concrete conditional-state, count, guard, time-grid and error interfaces, using the reviewed alternatives where the sketch fails; select and check a coherent toolchain.
3. Compare exact final statements in all three review roles and record the global immutable freeze manifest.
4. Only then implement the finite model, graph and density lemmas, followed by conditional exploration and the actual exponential moments; compile each completed lemma.
5. Assemble the deterministic and random-pile upper bounds and verify that every required estimate, including exponential moments, has a proof from the frozen inputs.

Files:

- `PROOF_STRUCTURE.md`: whole-proof structure, definitions, and implementation families.
- `audit/DECLARATION_DEPENDENCIES.md`: all active source declarations and their dependencies.
- `audit/REVIEW_COMPARISON.md`: agreement, corrections, counterexamples, and unresolved interfaces.
- `audit/INPUT_REVALIDATION.md`: current input comparison, exact missing theorem boundary, and fresh build evidence.
- `audit/PORTENKO_CANDIDATE.md`: exact abstract exponential-excess statement and mathematical proof, not a Lean theorem.
- `audit/reviews/`: nine independent reports.
- `audit/source_inventory.json`: exact source statements, active/commented status and source hashes.
- `audit/declaration_dependencies.json`: machine-readable dependency map.

The three mathematical source files and all inspected input Lean files were left unchanged. Existing unrelated workspace changes were preserved.
