# Existing project interfaces

No Lean project was present at the initial inventory. Several other tasks
subsequently created mathematical interfaces in the shared workspace. They
have been read independently to identify reusable definitions; a proof body
in a file is not by itself evidence that it compiles in this library's
toolchain.

| Library | Relevant definitions and results | Qualification |
|---|---|---|
| `RiffleShuffle` in `formalization/foundations` | `PileProfile`, `NormalizedProfile`, length-indexed `Word`, `Legal`, `mass`, `PileProfile.prob_sum`, `mass_sum`, `mass_append`, prefix trees, sorted matrices, path graphs | The inspected matrix interface is deterministic. It does not define a uniform sampling law or prove row marginals. Its bundled deck condition is `N>0`, which alone does not imply `log N>0`. |
| `Riffle` in `formalization/stable_blocks/Riffle` | `Model`, `Setup`, list words, `Boundary`, `Admissible`, `Stable`, `cL`, extended `cF`, `prob`, `weight`, `expectedCount`, boundary selection, strict stopping, source partitions | `expectedCount` is defined as `N` times a finite product-word sum. Its identification with an actual random-matrix expectation is not proved in the inspected modules. |
| `TimeProfile` in `formalization/time_profile` | `Simplex`, `Cuts`, `BorelPartition.IsRegular`, literal coarse digit profiles, exact ambient position sets, `cL`, `cE`, `Crossings`, product `prefixMass`, side maxima, extended `cF` | These give useful finite source specializations. The declared package targets Lean 4.33.1, whereas this library is checked with Lean 4.19.0; imports require a separate compatibility check. |
| `TimeProfile.TimeLaw` | `Real -> ProbabilityMeasure (Simplex k)`, cell masses and integrated costs | This type carries no time measurability. Totalized integral definitions do not supply the missing analytic proofs. |

The three detailed, independent inventories are:

- `reviews/model_interface_reconstruction.md`
- `reviews/model_interface_representation.md`
- `reviews/model_interface_adversarial.md`

The representations are distinct. `RiffleShuffle.Word` uses length-indexed
vectors, `Riffle.Word` uses natural-number lists with legality, and
`TimeProfile` uses full functions together with a prefix length. Their
equivalences need proofs. Counting full functions with a fixed prefix also
counts unconstrained suffixes and cannot directly give the number of prefix
words.

`TimeProfile.StableAt` has a weak stopping inequality. `Riffle.Stop` has the
strict inequality in the source. The former is not substituted for the
latter.

`FINITE_SOURCE_ADAPTERS_CANDIDATE.md` describes five applications of the
unchanged F01–F11 contract to the `TimeProfile` definitions. Their mathematical
reviews were compared and the statements frozen in `FROZEN_SOURCE_ADAPTERS.md`
before implementation. All five are now implemented and independently audited.
The complete compatibility changes and checks for the two imported dependency
copies are in `reviews/source_dependency_compatibility.md` and
`vendor/time_profile`. All source definition bodies and theorem headers were
preserved. The finite core remains independently usable without these imports.

## Verified matrix-law connection

T01–T09 now import checked verbatim copies of `Riffle.Definitions`, `Model`,
`Words`, `Boundary`, and `Shuffle.FiniteLaw`, `Conditioning`, `FixedColumns`.
The inspected `Riffle` directory has moved to `formalization/stable_blocks`.
The finite-law library is under `lean/Shuffle` and targets Lean 4.19.0.

`RiffleProfiles.model_expected_row_count` now proves the previously missing
identity between the product functional and actual expected row cardinality.
Its sampling law is exactly the existing product of uniform fixed-histogram
columns. `columnLaw_row_marginal` derives, rather than assumes, the single-row
histogram marginal. Row independence is not asserted. Sorting is a separate
permutation/count or graph obligation.
