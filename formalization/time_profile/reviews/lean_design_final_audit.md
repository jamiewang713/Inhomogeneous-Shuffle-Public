# Independent final statement audit

Reviewed `Numerical.lean` and `SideMass.lean` against the frozen contract after implementation. No source changes were made in this audit.

## Numerical.lean: N01–N10

- The large and small objectives have the frozen coefficients `(theta+3)/2` and `(theta-1)/2`, with the correct `-B(theta)-2D` signs.
- The large explicit loss is `4eL+eF+(7/2)eBeta+delta+eH+2eE`; the small loss is `(3/2)eBeta+5eF+4eS+eH+2eE`.
- N01 carries precisely the required finite mass, nonnegative exceptional cost, stability, fluctuation, maximal-pile, entropy and tail inequalities. It adds no large-size hypothesis.
- N02 carries the parent-derived S bound and adds no small-size hypothesis.
- N03 keeps the frozen nonnegative-error domains even though the elementary arithmetic does not need them.
- N04 has no sign condition on its additive error and no extra bounded-below assumption. The proof derives a common lower bound from the pointwise inequalities and uses the nonempty theta interval.
- N05–N07 use the source-style real infimum, require positive eta as frozen, and return the exact `-eta/2` margin. No minimizer or continuity assumption appears.
- N08 allows arbitrary eta and uses the frozen nonnegative eT/eF and positive delta; it does not identify the terminal scaled time with T.
- N09's coefficient sums are exactly `25/2` and `27/2`, with the common `14 epsilon` envelope and `epsilon<=eta/28` choice. Singleton loss is `2 epsilon`.
- N10 retains the same N0 and quantifies uniformly over every allowed member of each indexed family. It does not assert convergence of any profile input.

## SideMass.lean: B01–B04

- B01 side masses use the actual deterministic product-mass definition from Ambient; nonnegativity is proved from simplex coordinates. Prefix compatibility is exactly equality before v, with w<=v, and no unnecessary legality assumption is added.
- B02 is an equality in `WithBot ℝ` and therefore includes zero-side cases.
- B03 proves bottom iff either side maximum is zero. The self-join case is bottom, and the finite real formula is only used after both maxima are proved positive.
- B04 derives sideMaximum >= chi*prefixMass from the actual crossing witnesses and monotonicity of prefix products. Both maxima are then proved positive.
- The logarithmic comparison keeps the ambient birth-exponent discrepancy and the explicit `log(1/chi)/log N` term with the correct factor one half.
- No nonnegative-b, full-support, variance, anti-concentration or probability-interpretation assumption is introduced.

There is no substantive mismatch in these declarations' mathematical assumptions or conclusions. Compilation is reported separately by the build/audit workflow; this review checks semantic fidelity, not merely type-checking.

The independent analytic investigation is in `analytic_alternatives.md`: literal AlmostLike does not imply the source's two-sided integral estimates. A possible one-sided route remains an unfrozen proposal and has not been used by these Lean proofs.
