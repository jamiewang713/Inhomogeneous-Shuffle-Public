# LB08 labelled-row forcing inputs v1

`RiffleLowerV2/Occupancy/Forcing.lean` is complete and compiled. Import `RiffleLowerV2.Occupancy.Forcing`; this also imports the completed original and residual input adapters. It does not assert any final occupancy target.

The public `Occupancy.sameWordPrescription w e` uses an embedding `e : Fin b ↪ Fin N`, so its row labels are distinct. The following declarations are proved:

- `sameWordPrescription_row_injective`: the precise injection premise required by residual conditioning.
- `sameWord_forcing_probability`: exact product over columns of `falling selectedPile b / falling N b`, specialized from the actual LB03 fixed-column request probability.
- `sameWord_forcing_pos`: positivity from b<=N and b<=each selected pile, including b=0 and K=0.
- `falling_eq_forcing_sum`: pointwise equality of the bth falling factorial to the sum of same-word forcing indicators over ordered embeddings.
- `falling_expect_eq_forcing_sum`: its exact finite-expectation identity.
- `falling_weighted_event_eq_forcing_sum`: the expectation weighted by an arbitrary event indicator equals the sum of exact joint probabilities.
- `forcing_weighted_relative_error`: if every positive forcing event changes an arbitrary event probability by at most delta times its marginal, then its factorial-weighted expectation changes by at most delta times the factorial mean times that marginal.
- `sameWord_prescribed_other_count`: when w differs from v, the prescribed-v count among same-w prescriptions is exactly zero.

The weighted relative lemma has an explicit conditional-error premise. It is a finite algebraic transfer helper; downstream must discharge that premise with the completed actual conditional collision theorem. No independence is assumed, and this delivery does not treat the helper as completion of the rare pair estimate.

The pointwise counting identity is proved by an explicit equivalence between embeddings into the word fiber and forcing embeddings. The probability formula uses checked `Factorial.request_probability`; expectation sums use checked finite expectation linearity. The weighted error proof uses the positive denominator identity for each forcing event, a finite triangle inequality, and nonnegative probability weights.

Successful command, from the package root:

```text
python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Forcing
```

`audit/LB08/model_forcing_build_dev06.log` ends with `LB08 BUILD_OK`, with no warnings or errors. `model_forcing_check_v1.lean` prints complete public theorem types and transitive axiom closures; its log records only `propext`, `Classical.choice`, and `Quot.sound`. The audit ran with Lean 4.33.1 and the assigned LB08 overlay. Earlier logs preserve development simplification/Decidable-instance issues and two harmless build-lock contentions. No shared cache, upstream source, frozen contract, or sibling-owned source was edited.
