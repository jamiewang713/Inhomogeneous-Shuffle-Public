# Independent adversarial implementation audit: S01–S03

Approved against `FROZEN_SOURCE_ADAPTERS.md`, version 1. No statement change or
additional hypothesis is needed. This is a read-only audit of Lean code;
compilation is being performed separately by the implementing agent.

Audited `RiffleProfiles/SourceReplacement.lean` SHA-256:
`4e53f1b74e161d7d3c5144d7ac60aea12fd8fb7832265826321dd12ccb99ed09`.
Frozen contract SHA-256:
`33de1f7762aae8ce60136965cf4d37d4028f33a4d9cc5dfbc348f95d8f21e006`.

- **Cost identity, lines 15–16:** `source_digitCost_eq_cost` is the exact
  all-real identity between the existing definitions, proved using
  `Real.log_inv`. It includes zero under Lean's totalized logarithm and does
  not assert a physical logarithmic cost for an illegal zero-mass digit.
- **S01, lines 18–29:** `source_regularDigits` retains exactly `0 < χ` and
  `P.IsRegular χ C`, and works on an arbitrary finite position set. Both
  actual and representative masses use the same selected digit `x j` and
  the cell `P.classify (p j)`. The good threshold remains strict
  `2 * χ < q`; the exceptional threshold remains `q ≤ 2 * χ`. The error is
  exactly `C * χ`. The source regularity fields supply the needed statements
  directly; no full-support or further positivity premise is introduced.
- **S02, lines 31–52:** `source_cE_replacement` retains exactly `N ≥ 2`,
  regularity, and the frozen per-cell count errors. It applies F08 at
  `θ = 2`, which belongs to `[2,4]`. The algebraic equality at lines 45–50
  preserves the minus sign in `cE`. The final error is exactly
  `card(J) * C * χ / logScale N + Σ |psi(rep i,2)| * δ i`, with
  `J = positions K M K`; no cell-cardinality factor is lost. Target weights
  `m` and error parameters `δ` remain arbitrary real functions subject only
  to `hcount`. In particular no integral interpretation, positivity, or
  normalization premise has been added. Empty or clipped tails are covered.
- **S03, lines 54–79:** `source_cL_maximal_target` retains exactly the frozen
  four hypotheses. For every selected `j`, membership in
  `positions K w M` supplies `j.val < M`, so the existing `LegalPrefix`
  assumption supplies positive actual selected mass, even when `M > K`.
  `prob_le_pileMax` supplies domination, which is sufficient for F09;
  representative selected digits may be zero. The second step applies F06
  to `maxCost` with the exact frozen count errors and then the proved
  `maximal_pile_target` inequality. The sign and parentheses of the target
  and error match S03. No `w ≤ M`, `M ≤ K`, ambient approximation, or
  full-support assumption is introduced. When `w ≥ M`, the empty sum is
  handled by the same finite lemmas.

The file contains only the four advertised theorem declarations and no
`axiom`, `sorry`, `admit`, or placeholder declaration. Its proof steps use
the frozen finite estimates and existing source-interface theorems. This
approval establishes only S01–S03 as finite source adapters. It supplies no
time-integral comparison, probability/expectation identification,
asymptotic estimate, or completion of the original assigned source lemmas.
