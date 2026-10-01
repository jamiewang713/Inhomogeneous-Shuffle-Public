# LB09 pre-proof review comparison v1

The independent mathematical, Lean representation, and missing-hypothesis reports agree: retain every frozen v1 LB09 target, definition, constant, and quantifier order. No shared-contract amendment is proposed. This comparison records pre-proof decisions, not completed Lean results.

| Issue | Independent findings | Resolution to implement |
|---|---|---|
| Type errors versus entropy slack | All three reject perturbing only the potentially saturated displayed witness inequality | Derive H<=J from actual LB05, then six-kappa slack from J<=b/2-3κ |
| Right endpoint | All three require the ambient fluctuation; hypotheses reviewer gives an explicit two-row empty-suffix counterexample to omission | Preserve the frozen exact identity and handle N=0/empty suffix explicitly |
| Probability event | All three approve the same allPrefixEvent κ/4 for endpoints and reserves | Prove finite mean/error thresholds and use the concrete LB02 polynomial failure bound |
| Rank and interval conventions | All three agree on manuscriptRank=i.val+1 and literal integer half-open Hrel | Preserve the two-unit slack; derive rank inequalities before clipping membership |
| Bridge products | All three retain chiGood² and the two specified one-column reserve changes | Prove strict lex order and fixed-factor absorption with uniform thresholds |
| Integer boundary | All three prohibit treating every selected interval as a separate component | Use boundary subadditivity and at most two extra clipping edges |
| Full family and edges | All three require actual injections | Prove concatenation injective and choose first two sorted copies only after localization |
| Uniformity | All three approve frozen quantifier order | Choose xi/P before N0; N0 precedes cuts, witness, geometry, and words |
| Inputs and cache | Source hashes match completed upstream receipts; shared LB05 registration was absent | Obtain coordinator dependency receipts and use the lane's assigned output only |

The representation review's 3,864 exact small-case checks support the endpoint convention but are not proof evidence. The hypotheses review's counterexamples concern false simplifications, not the frozen targets. No unresolved mathematical objection remains in these reviews; all implementation, build, and final independent verification obligations remain open in OBLIGATIONS_v1.md.

LB00 is asked to acknowledge INTERFACE_PROPOSAL_v1.md and these three reports, confirm optional reuse of already integrated Model.Sorting, and integrate completed Thinning.Main and Witness.Main. Only LB00 may change shared registrations or issue a contract receipt.
