# LB08 concrete model inputs v1

The two bounded adapter modules are complete and checked under the unchanged interface acknowledgement `audit/LB00/LB08_INTERFACE_ACK_v1.md`. Import `RiffleLowerV2.Occupancy.ConditionalInputs` to receive both modules. This delivery proves concrete inputs, not the three final occupancy targets.

All public names below are in `RiffleLowerV2.Occupancy`:

| Declaration | Proved content |
|---|---|
| `wordMean_pos` | Positive c, positive N, and selected piles >=cN imply positive actual full-word mean, including K=0. |
| `original_one_factorial_inputs` | LB03 specialized to one word: uniform D,N0 and exact `D*(K+1)*r^2/N` relative factorial cost. |
| `original_two_factorial_inputs` | LB03 specialized to two distinct words: exact total-order square cost and product benchmark. |
| `fullWord_empty_singleton_tail` | Actual LB02 empty/singleton tail at the original full-word mean. |
| `prescribedPrefixCount_fullPrefix` | Full-prefix prescriptions are precisely prescribed copies of the full word. |
| `residualPrefixCount_fullPrefix` | Residual full-prefix count equals word count minus all prescribed copies. |
| `residualPrefixMean_fullPrefix` | Residual full-prefix mean equals frozen `Targets.residualWordMean`. |
| `residualWordMean_pos` | Positive residual population and unexhausted selected piles imply positive residual mean. |
| `conditionalProbability_eq_expect_indicator` | Exact canonical probability/expectation bridge for a conditional indicator. |
| `exists_residual_word_law` | A single actual residual fixed-column law has exact residual counts, transports every real deleted-count test, transports every deleted-count event, and identifies its mean. |
| `conditional_one_factorial_inputs` | LB03 specialized to the deleted one-word count; keeps ambient N in the order cutoff and error. |
| `conditional_fullWord_empty_singleton_tail` | Actual conditional LB02 tail at the exact residual mean. |

The complete types and all axiom closures are printed by `audit/LB08/model_check_v1.lean` in `model_check_v1.log`. Every closure uses only `propext`, `Classical.choice`, and `Quot.sound`. All conditional bridges retain injective labels, positive conditioning probability and b<N where required; no conditioning law is assumed. The moment declarations retain positive c,C and choose constants/thresholds before varying arrays, words, moment orders, and prescriptions.

Successful lane build from `formalization/lower_bound_v2`:

```text
python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.ConditionalInputs
```

`model_build_dev02.log` ends in `LB08 BUILD_OK`, with no warnings or errors. The statement/axiom audit used the same pinned Lean 4.33.1 compiler and `.build/lanes/LB08/lib/lean`, exiting zero. The v1 development log is retained and records an initial function-eta simplification issue resolved with explicit function equalities. No upstream, contract, build configuration, manuscript or sibling proof file was modified.

Provenance: moment adapters call checked `Factorial.relativeJointFactorial` / `Factorial.residualRelativeFactorial`; positivity calls the checked numerical-mean lemmas; tails call checked `Thinning.prefixTails` / `Thinning.residualPrefixTails`; the residual-law witness and expectation transport come from `Thinning.residualPrefixExpect` and its proved complement enumeration. The probability bridge is proved directly from canonical finite expectations. No private upstream declarations are accessed.
