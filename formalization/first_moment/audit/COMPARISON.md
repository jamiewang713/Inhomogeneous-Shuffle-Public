# Independent review comparison before implementation

All three reviewers independently read the original permitted sources before comparing reports. Each approved all 29 interfaces in FROZEN_CONTRACT.md.

| Component | Algebra reconstruction | Lean statement design | Inequality audit | Frozen resolution |
|---|---|---|---|---|
| Large exponent | signed convex combination | no beta positivity | raw error23e/2+delta | 12e+delta |
| Small exponent | parent bound essential | no Q premise needed after parent bound | raw error27e/2 | 14e |
| Singleton | size plus tail | terminal F need not be real | floor time is not exactly T | use scalar beta-D+2e |
| Theta | direct lower-bound argument | le_csInf, nonempty interval | no extra continuity | pointwise-to-infimum theorem |
| Class count | mark exceptions by value | exact sparse sum and finite encoding | coarse c_L not constant | explicit refined key; pointwise class sums |
| First moment | product-law sum of squares | finite probabilities | both localization and class counts needed | 2D+2L*card(C)*U |

The proposed model assumptions were not strengthened. The refinement adds exceptional digit values to counting keys without altering the original profile. Uniform finite error bounds are the numerical theorem inputs, not asserted new facts about the shuffle model. Exact low-level upstream Lean constants remain to be identified from other agents' proved files.

All three reviewers independently verified the deterministic-first-column anti-concentration counterexample. The statement reviewer also supplied a direct small-density counterexample. No false upstream assertion is imported or made an axiom. They suggested restarting after a good first-column split while keeping an outside population reservoir, but no such unproved repair is part of the frozen theorem inputs.

## Review after implementation

The algebra reviewer independently checked Counting11–18 and Entropy19–22 against the frozen contract; all matched, including zero/empty cases. The inequality reviewer independently checked Numerical1–10 and Assembly23–29; all mathematical theorem interfaces matched. The reviewer noticed FiniteGraphLaw initially allowed a nonfinite ambient edge type; the implementation was restricted to `[Fintype M]` as frozen. No contract change was made. Frozen nonnegativity/positivity premises that are stronger than needed by a particular proof term were retained, with underscore binder names to avoid lint warnings.
