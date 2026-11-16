# Comparison before implementation

Three agents independently read the old proof and the inhomogeneous sketch:
`reconstruct` reconstructed the argument; `representation` designed the Lean
representation; `counterexamples` searched for hidden assumptions and failures.
All reviewed every F01–F20 target and the definitions in the candidate contract.
The coordinator read and compared all three reports before the finite freeze.

| Target group | Reconstruction | Representation | Adversarial review | Resolution before freeze |
|---|---|---|---|---|
| F01–F06 representative/cost split | Direct finite proof | Positive support; raw counts | Zero and threshold cases valid | Approved unchanged |
| F07 interval blocking | Triangle inequality with endpoint masses | Finite additive decomposition | A length bound alone is insufficient | Explicit nonnegative target remainder bound and additive totals added |
| F08–F09 tail/maximal cost | Negation and log monotonicity | Retain cell factors | No full-support or FM premise needed | Approved unchanged |
| F10–F12 fluctuation/parent algebra | Product contraction then log | Restrict real logs to proven positivity | Include crossing factor; no variance inference | Nonnegative earlier mass and all remaining factors explicit |
| F13–F15 entropy/KL | Elementary log inequality | Zero-total case; positive count support only | Full tilted normalizer required | Approved unchanged |
| F16–F18 tails | Weighted binomial/MGF proof | Product weights, no row independence | All zero/empty endpoints valid | N times word mass kept separate from shuffle expectation |
| F19 class descriptors | Exact sparse counts and injection | Final digit encodes terminal case | Empty alphabet caveat | Source k≥2 for boundary encoding; coarse object is forgetful image |
| F20 coarse fibre | Sum over labels | Retain missing k^q | Empty maximum needs convention | Uniform bound B on every fibre |

All three approved the corrected contract before the first `.lean` file.
No source assumption was strengthened after freezing. The contract is hashed
in FREEZE_SHA256.json; source hashes are in SOURCE_SHA256.json.

The following were deliberately not converted to premises: time measurability,
actual variance/anti-concentration from side means, exact ambient time, exact
constancy of c_L on a profile, and the false unweighted high-tail enumeration.
No paper statement is treated as a previously checked Lean theorem.
