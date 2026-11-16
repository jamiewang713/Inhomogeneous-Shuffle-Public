# LB-02 exact residual law receipt, v1

Date: 2026-10-01. Import `RiffleLowerV2.Thinning.Residual`.

The exact frozen export is proved:

```lean
RiffleLowerV2.Thinning.residualLaw : RiffleLowerV2.Targets.ResidualLaw
```

Two additional proved exports transport arbitrary real tests and events of the
residual row array:

- `RiffleLowerV2.Thinning.residualConditionalExpect`
- `RiffleLowerV2.Thinning.residualConditionalProbability`

Their full elaborated types and the exact target type are recorded in
`residual_build_v1.log`. Both additional statements construct residual counts
`cuts.count j a - usedCount r j a`, use the population `N-b`, require injective
prescribed row indices and positive prescription probability, and quantify over
every injective enumeration whose range is the unused labels. The extra
transport statements also hold when all rows are prescribed; the frozen
`residualLaw` retains its exact original `b<N` domain.

The proof constructs a finite bijection between compatible original samples and
residual samples. Restriction and gluing are proved inverse for an arbitrary
allowed complement enumeration. Positive probability supplies a realizing
matrix, which establishes feasibility and exact subtraction of prescribed
counts. Uniform conditional expectations then follow from finite sum and
cardinality transport. The map-to-row-array atom is proved for arbitrary PMFs by
the finite `PMF.map_apply` formula. This is a proof in the current shared PMF
model; no historical law is substituted for the concrete shuffle law.

Source correspondence: the final conditional paragraph and residual-count
clause of manuscript `lem:successive-thinning-tail`. This receipt does not claim
that the unconditional transforms, prefix concentration, or permutation TV
conclusion are proved. Explicit residual-prefix count and mean adapters are
being developed separately in `Residual/Prefix.lean` and are outside this v1
receipt.

Successful command from `formalization/lower_bound_v2`:

```text
python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Residual.Check
```

The log ends with `LB02 BUILD_OK`. All three public theorem closures are exactly
`propext`, `Classical.choice`, and `Quot.sound`; no additional assumptions enter
the closure. The build used the registered LB-02 overlay and serialized lane
lock. No coordinator build, shared contract edit, manuscript edit, or old source
edit was performed.

Verified source/log identities:

| Artifact | SHA-256 |
| --- | --- |
| `RiffleLowerV2/Thinning/Residual.lean` | `c2ab734fc2a452b6ae2d8541d982ad5589fbf99d2b7e8850e0f2bf6b6eb64d62` |
| `RiffleLowerV2/Thinning/Residual/Check.lean` | `b5b0526595a8a1e64b875e4fd5f860aa38dac3f99c1e462ae1e6d37397a2009e` |
| `audit/LB02/residual_build_v1.log` | `a4e1f1a88e076cc73deddeb8fff108e5a08ec833755a306e0b0f5cce81ff082b` |

There is no unresolved mathematical or API blocker for these three exports.
