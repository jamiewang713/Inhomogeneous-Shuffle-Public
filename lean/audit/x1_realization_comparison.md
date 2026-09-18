# Comparison before concrete X1 implementation

The root compared all three independent reviews before writing any realization Lean code. All three reviewers reread the permitted source material and approved R1–R4, including the final cumulative-count, actual-intersection, Boolean-convention, and finite-tower details.

- **Probability reconstruction:** exact histogram counts make both cumulative endpoint counts constant for every legal matrix. Every positive conditioning event therefore preserves their count laws, moments, and unit atoms. Arbitrary further conditioning does not necessarily preserve residual assignment uniformity; no such claim is made.
- **Lean representation:** use the existing D6 `FixedColumn`/`fixedMatrixLaw` constructions on `Fin (2*L+middleSize)` and `Fin (d+2)`; restrict the Boolean to the two frozen cases. Link the residual random variable explicitly to the cardinality of the marked/sample intersection. Retain the frozen `1≤L` premise. The exact natural count-law interface then transfers moments without new support assumptions.
- **Missing-hypothesis audit:** all positive-event assertions use the existing F3 normalization convention; null atoms are not laws. Restricted point probabilities equal `P(S|E)`, and only the finite tower is used to deduce `2P(S)≤b`. Unconditional likelihood is not misused as an atomwise lower bound. No reserve or arbitrary exploration-preservation premise is introduced.

Resolved before freezing: name the variables `leftCount` and `throughCount` to distinguish zero-based cumulative counts from a one-based endpoint convention; define `singleton=true` as middle pile `1` and `false` as middle pile `L`; record `sampleRows=residualRows` and the marked/sample intersection identity. All three approved the final finite-tower consequence for every real `b`, without adding `b≥0`.

The finite experiments are instances of frozen X1. They do not change, repair, strengthen, or weaken the manuscript's ambient theorem. Source crossing, admissibility, and fluctuation comparisons remain distinguished from a complete formalization of the manuscript's asymptotic vocabulary.
