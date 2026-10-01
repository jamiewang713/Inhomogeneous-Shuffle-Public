# LB06 source provenance v1

All proof modules were checked with the pinned Lean 4.33.1 runtime and the v1 canonical foundation. No old-version output or dependency cache was mixed in. Every owned output hash appears in SOURCES_v1.json. The manuscript is read-only.

| Read-only source | SHA-256 | Use and signature comparison |
|---|---|---|
| `formalization/time_profile/RiffleTimeProfile/Analysis.lean` | `6cb844a02817905bc2e87f57277b23e68c2040dd2b1be6509d4b4320eeb3ac30` | Canonical compatible import only in Partition.lean; exact exists_regular_partition supplies constant 1. No source port. |
| `lean_formalization/RiffleProfiles/Entropy.lean` | `25c1351a62e4eaa5622597846ca48f9fc09ade34ac3d4fd18a8798d87fbfce0a` | Inspected Gibbs/upper-entropy helpers. No theorem imported or ported; new entropy proof is elementary finite factorial/rounding analysis. |
| `lean_formalization/RiffleProfiles/Estimates.lean` | `7c0f131c9c56a89c6fc2a2bb65b25ebc4636cd7b1a931bae2534a57970166824` | Inspected finite replacement/regrouping interfaces. New WordEstimates proves the concrete selected-column variants directly. |
| `formalization/first_moment/FirstMoment/Entropy.lean` | `7989028dd7addb46b87a9176e85560d9c9f5edb3497ede44b7b0ded9964563b2` | Upper type theorem is not used. Its local finite fiber regrouping pattern is adapted in WordEstimates.word_sum_identity from Fin K to the actual subtype I and frozen wordCellCount; cardinality and lower entropy are proved independently. |
| `lean-lower-bound/RiffleLower/Profiles.lean` | `94b691d97f6f30147e147c6ab6ba1676249876d85942cb063408c3f8b375322d` | Inspected count regrouping and logarithmic product arguments; their finite-sum/product pattern is adapted to canonical Cuts/massOn in MassBins and WordEstimates. No old namespace or compiled output imported. |
| `formalization/time_profile/RiffleTimeProfile/FixedCountModel.lean` | `d5c7cd27f01d77063de5a5dee6f0764e36620cfa997f1660f27c3982e71fde4e` | Canonical foundation import. Its labelled finite-assignment idea informs the new generic Counting construction; exact class cardinality uses a new equivalence-fiber count. |

The adapted grouping proof is now `word_sum_identity cuts hN P I D x hx v`, relating sums over actual selected positions to the prescribed per-cell digit counts. The old upper-cardinality conclusion is neither imported nor assumed. Exact natural quotient/cardinality is proved in Counting.lean; the lower and upper logarithmic estimates are proved in EntropyBounds.lean and specialized in ClassEntropy.lean.

Adapted output SHA-256 values:
- `RiffleLowerV2/Types/Counting.lean`: `c9447f614ac6458dd4b7a8d2512258a012a736ad8c8b62cf00520e87db05226c`.
- `RiffleLowerV2/Types/MassBins.lean`: `990b31c1b9850ec0374cc1a1ef41c3c21cfbfc97262296d7945732a01fc748fb`.
- `RiffleLowerV2/Types/WordEstimates.lean`: `6c4be391d4b49a6182512b7478c9594fbced94a83e327b3f131085a161487e1a`.
- `RiffleLowerV2/Types/EntropyBounds.lean`: `a4075ff676bdcf7fcadbe2bf7ee2575675d43a0e29bfcc89ad6356b8794b8239`.
- `RiffleLowerV2/Types/ClassEntropy.lean`: `8cbc701b627ede6e0ffac138e72a04d8e92aa2af92b218304c16fa13ba220074`.
