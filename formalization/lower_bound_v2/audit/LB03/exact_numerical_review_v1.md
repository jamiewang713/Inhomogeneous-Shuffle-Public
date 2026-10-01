# Independent numerical interface review, v1

The exact-moment implementer reviewed `Relative.lean`, `ResidualEstimates.lean`, `MomentScales.lean`, and the draft `RelativeTargets.lean` independently of their author. This is a source-level mathematical and interface review; compilation is tracked separately by their author.

No substantive mathematical or quantifier defect was found. The finite numerical theorem separates the ambient size `N` from the falling-factorial population `M`, which resolves both the residual cutoff `R≤N^(1/5)` and the depth bound `K≤C log N`. In the residual wrapper, `a=min(c/2,1/2)` and the threshold lower bounds `N≥2b0+2`, `N≥ceil(2b0/c)` provide `M=N-b≥aN` and selected residual pile sizes at least `aN` uniformly over every `b≤b0`. These hypotheses permit the same ambient numerical smallness budgets without silently replacing the frozen order range by `(N-b)^(1/5)`.

The scalar product bound logs only factors proved positive. In `column_log_factorial_bound`, the case of a zero requested order is separated before any pile positivity is used, so zero unrequested piles cause no problem. The finite inequality keeps the true `(K+1)R²/N` error and is valid when `K=0` or `R=0`. The mean comparison keeps the factor `b`; its finite log estimate therefore gives exact equality for `b=0`.

The wrapper thresholds and constants are chosen after only the frozen fixed parameters `c,C` (and `b0` for residual statements), before `N,k,K,d`, cuts, prescriptions, words, or orders. The residual numerical mean comparison is stronger than its frozen conditional model use: it does not use injectivity or positive conditioning probability once the deterministic count-removal budgets are available. This is harmless because those premises remain on the frozen export.

The concrete probability identities still need the separately implemented `Exact.lean` and `Residual.lean`. The numerical lemmas themselves make no asserted-moment assumption and do not claim to prove the concrete law.
