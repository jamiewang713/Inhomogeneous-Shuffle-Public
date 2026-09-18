# Time-inhomogeneous first-moment Lean package

There are now 71 proved Lean theorems: the original 29 frozen core interfaces, seven boundary-model bridges, four actual profile-class results, four exact within-class entropy results, sixteen stable-word/time-profile adapters, eight source-profile normalization results, and three ordered profile-count limits. The final shuffle-model theorem is still pending valid localization and density results and the remaining model identifications; this package does not assume those results or claim their model instantiation.

## Contents

| Module | Frozen interfaces | Proved result |
|---|---:|---|
| `FirstMoment/Numerical.lean` | 1–10 | Large-block, small nonsingleton and singleton exponents; theta-infimum optimization; explicit negative margins |
| `FirstMoment/Counting.lean` | 11–18 | Exact sparse marked-data count, exact refined profile-key count, weighted/exponential bounds, eventual real-power bound |
| `FirstMoment/Entropy.lean` | 19–22 | Product-word normalization, cardinality from common mass, exact type-class entropy bound including inconsistent/empty classes |
| `FirstMoment/Assembly.lean` | 23–29 | Independent common-edge expectation identity, localization and class aggregation, entropy cancellation, polynomial decay absorption |
| `FirstMomentModel/BoundaryEncoding.lean` | B1–B7 | Actual admissible boundary and pair encodings, decoder reconstruction, injectivity, finite cardinality bounds from the source budget |
| `FirstMomentModel/ProfileClasses.lean` | P1–P4 | Actual admissible stable-word domain, labeled refined descriptors, exact data recovery from equal keys, realized class count |
| `FirstMomentModel/ProfileFibreEntropy.lean` | PF1–PF4 | Actual class-fibre finiteness and exact entropy cardinality bounds, including unrealized keys and zero counts |
| `FirstMomentModel/StableNumericalBridge.lean` | SN1–SN16 | Literal fixed-count expectations, cost and fluctuation identities, boundary crossings, stopping and parent-crossing implications, ambient-error equivalence |
| `FirstMomentModel/ProfileNormalization.lean` | PN1–PN8 | Literal exceptional sets and digit counts, source entropy normalization, actual-profile cutoff, realized fibre bound by the source entropy |
| `FirstMomentModel/ProfileCountLimit.lean` | CL1–CL3 | Uniform finite-depth count, small-chi subpower bound, actual class count with chi chosen before dimension and N |

Import `FirstMoment` to load all four modules. The namespace is `InhomogeneousShuffle.FirstMoment`.

Import `FirstMomentModel.BoundaryEncoding` for the supplemental bridge, in namespace `InhomogeneousShuffle.FirstMoment.Model`. It uses the completed stable-block package's literal definitions.

Import `FirstMomentModel.ProfileClasses` for the realized classes. They are the range of the actual encoder; individual stable words are not claimed to inject into a class key. The exceptional cutoff remains a real inequality in the domain and exceptional digit values are retained in the key.

Import `FirstMomentModel` for the three original model modules. For each actual class fibre, the exact word count is at most `exp(typeEntropy keyCounts)`, equivalently `N^(typeEntropy keyCounts/log N)`. The proof restricts words to the common good-position set; the fixed prefix and exceptional digits are not counted again.

Import `FirstMomentModel.StableNumericalBridge` on Lean 4.33.1 for the additional adapters. They identify the list-based weighted expected count with the literal fixed-count matrix expectation for every set of words. Cylinder and side events, finite side maxima and extended fluctuation exponents are then matched exactly. Terminal and zero-side cases remain included; boundary crossing and parent stopping implications retain their actual branch conditions. The arbitrary ambient exponent is preserved, and its mass approximation is expressed as an equivalence rather than assumed exact.

Import `FirstMomentModel.ProfileNormalization` on the same runtime to identify the source's good-digit frequencies and entropy with the actual refined class data. The exact identity is `profileH = typeEntropy / log N`, including zero counts and empty intervals. The real exceptional cutoff and the legality derived from stable membership give the source profile conditions without new premises. Each realized fibre has cardinality at most `N^profileH`.

`FirstMomentModel.ProfileCountLimit` proves the ordered count for these actual classes. Given any positive target exponent, chi is chosen before the finite count dimension, and the threshold for N comes afterward. The exact polynomial, both labeled boundary factors, exceptional values and four routing values remain included. The result applies uniformly to all later finite models with the stated horizon and fixed boundary constant.

Import `FirstMomentSource` on Lean4.33.1 for the complete 71-theorem package, including all source adapters and the ordered count.

The real-algebra margin theorems use the time-inhomogeneous objectives

- `((theta+3)/2)*beta - B(theta) - 2*D`;
- `((theta-1)/2)*beta - B(theta) - 2*D`;
- `beta-D` for singletons.

There is no homogeneous cutoff assumption. The theta argument uses the pointwise inequality itself as a lower bound for the nonempty image on `[3,4]`, so no optimizer, continuity, or extra boundedness assumption is introduced.

The finite expectation theorem proves

`expectedCommonEdges ≤ 2*D + 2*L*(card C)*U`.

Here `D` bounds discarded squared probabilities, `L` bounds per-edge localization multiplicity, and `U` bounds one profile class's squared-probability sum. Both counting factors are retained. The final theorem proves eventual absorption into `N^(-delta)` for `0<delta<min(d,a-ell-c)`. These are general proved aggregation results; the model-specific premises still need proofs.

## Frozen contract and review

`FROZEN_CONTRACT.md` lists every definition and theorem interface. `FREEZE_RECORD.json` records its hash and the hashes of the three permitted mathematical sources. Three independent reviewers reconstructed the algebra, designed the Lean statements, and searched for incorrect inequalities before the freeze. Their reports and comparison are in `audit/`. Independent review after implementation found no changed theorem assumptions or conclusions. A definition initially more general than the contract was restricted to the frozen finite edge type before final verification.

`PROOF_MAP.md` and `dependencies.json` record all 70 active source definition/theorem nodes and the upper, lower, and random-pile branches. The old lower overview inside the TeX comment environment is explicitly excluded.

`DependencyAudit.lean` extracts direct constants from elaborated types and proofs. Its machine-readable output is `audit/lean-dependencies.json`, including generated declarations as well as the named results. This complements the mathematical dependency map.

`SourceDependencyAudit.lean` performs the same extraction on the common-runtime package; `audit/source-lean-dependencies.json` currently contains 211 elaborated declarations, covering all 71 named results and their generated definitions/helpers.

## Reproduce checks

From the workspace root:

```sh
python3 formalization/first_moment/check.py
python3 formalization/first_moment/verify.py
python3 formalization/first_moment/verify_model.py
python3 formalization/first_moment/verify_profiles.py
python3 formalization/first_moment/verify_fibres.py
python3 formalization/first_moment/verify_stable_numerical.py
python3 formalization/first_moment/verify_normalization.py
python3 formalization/first_moment/verify_count_limit.py
```

The first five commands use the existing shared Lean 4.19.0 installation and mathlib in `formalization/.tooling/`; they do not download packages or use a global default toolchain. The verified mathlib checkout was `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The stable numerical, normalization and count-limit verifiers use the documented common Lean 4.33.1 runtime through `check_compat.py`, with mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

`verify.py` checks the frozen source/contract hashes, checks the exact 29-theorem inventory, scans the module sources for forbidden proof placeholders, and runs Lean's dependency inspection. The checked proofs depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The trust output is `audit/lean-trust.log`.

The same source files also compile with the incoming packages' Lean 4.33.1/mathlib toolchain, and all 29 declarations pass its trust audit. This was achieved by three proof-term API adjustments; no definition, theorem statement, or hypothesis changed. The compatibility record is `audit/compatibility-4.33.json`. The default reproducible build remains pinned to 4.19.0.

All 44 results also now pass a combined Lean4.33.1 check together with the time-profile numerical/expected-mass modules and the 153 stable-block theorems. The later model/stable compatibility copies make only documented proof/import API changes and preserve every original frozen file. Their complete diffs and provenance are under `compat/`; `audit/integration-compat-verification.json` records the combined check. Imports alone do not establish the mathematical adapter identities.

## Incoming proved inputs

Exact names, actual hypotheses, and model-connection obligations are recorded in:

- `audit/UPSTREAM_PROFILE_INPUTS.md`: finite cost/entropy/parent-crossing inputs and source variational predicates;
- `audit/UPSTREAM_STABLE_INPUTS.md`: completed deterministic decomposition, stopping, and boundary-crossing inputs;
- `audit/UPSTREAM_EDGE_INPUTS.md`: finite edge-density reductions and the formally proved fixed-endpoint obstruction;
- `audit/UPSTREAM_SAMPLING_INPUTS.md`: verified fixed-column, conditional hypergeometric, and mixture laws, with the remaining row/prefix/edge application obligations.

The incoming time-profile package has completed 158 theorems across 19 modules, including one-sided integral comparison, uniform source numerical margins and actual expected prefix/side-count identities. All recorded source hashes match. The sixteen finite adapters now prove their stated connection to the list-based stable-block package without a time-measurability assumption, and the eight normalization results identify the profile entropy exactly. Source parameter specialization remains a separate obligation. The incoming exact collision addendum also supplies the actual two-row and fourth-power density bounds needed by the alternate small-block argument; its native verification and toolchain compatibility limits are recorded in `audit/UPSTREAM_EDGE_INPUTS.md`.

Sixteen further ordered-limit results saved by the profile-estimate task have been independently rebuilt and checked, including actual discarded-row power bounds and ordered descriptor-count limits. Their eleven-module dependency build and transitive foundation audit are recorded in `audit/upstream-profile-limits-verification.json`; exact usable inputs and the distinction between the two descriptor polynomials are documented in `audit/UPSTREAM_PROFILE_INPUTS.md`.

A separately reviewed deterministic connection to the actual admissible boundary words is frozen in `MODEL_BRIDGE_CONTRACT.md`, with its recorded hash in `MODEL_BRIDGE_FREEZE.json`. All seven supplemental statements now compile on Lean4.19.0 and pass the trust audit, with no added model hypotheses. The encoder preserves genuine crossings at the final column and records outward final digits in fallback. Two independent implementation reviews confirmed exact agreement with the freeze; the implementation review and complete theorem-type/trust output are `audit/BOUNDARY_IMPLEMENTATION_REVIEW.md` and `audit/model-trust.log`.

The four actual profile-class results are separately frozen in `PROFILE_CLASS_CONTRACT.md` and `PROFILE_CLASS_FREEZE.json`. All four compile, pass the foundation audit, and have two independent implementation approvals. The full theorem types and dependencies are in `audit/profile-class-trust.log`.

The four within-class entropy results are frozen separately in `PROFILE_FIBRE_CONTRACT.md` and `PROFILE_FIBRE_FREEZE.json`, after three independent exact-document approvals. They compile, pass the foundation audit, and have two independent implementation approvals; complete theorem types are in `audit/profile-fibre-trust.log`. No finite-domain, realized-key, compatible-count or entropy-sign premise was added.

The sixteen stable numerical adapters and four definitions are frozen in `STABLE_NUMERICAL_BRIDGE_CONTRACT.md` and `STABLE_NUMERICAL_BRIDGE_FREEZE.json`, after three independent exact-interface approvals. All twenty declarations compile on Lean 4.33.1 and pass the transitive foundation audit; the source and contract hashes, complete theorem types and dependencies are recorded in `audit/stable-numerical-verification.json` and `audit/stable-numerical-trust.log`. Earlier frozen files and the three research sources remain unchanged.

The eight source-profile normalization results and two definitions are frozen in `PROFILE_NORMALIZATION_CONTRACT.md` and `PROFILE_NORMALIZATION_FREEZE.json`. All ten declarations passed the independent build and foundation check, recorded in `audit/profile-normalization-verification.json` and `audit/profile-normalization-trust.log`, and both independent implementation reviews approved them. No partition regularity, positive-count, compatibility, finite-domain or additional legality premise was inserted.

The three ordered profile-count limits are frozen in `PROFILE_COUNT_LIMIT_CONTRACT.md` and `PROFILE_COUNT_LIMIT_FREEZE.json`. All three passed the independent build and foundation check and both implementation reviews. `audit/profile-count-limit-verification.json` records the exact hashes; complete types and dependencies are in `audit/profile-count-limit-trust.log`.

## Integration blocker

The source's first deterministic column is included in the fluctuation scale. With equal fixed ternary piles and boundary pair `y=z=(1)`, that scale is about `N^(1/2)`, while the left endpoint of every prefix `(1,0,...,0)` is deterministic. This contradicts the proposed anti-concentration input. Independent later audits also give counterexamples to both the printed large and small density estimates under the macroscopic variational assumptions; see `audit/LARGE_BLOCK_ALTERNATIVE_ALGEBRA.md` and `audit/LARGE_BLOCK_ALTERNATIVE_INEQUALITIES.md`.

Those examples do not refute the final first-moment decay theorem. A candidate replacement exposes an early good column and retains a global sampling reserve while analyzing later columns. The reports identify the needed new conditional-law, smoothing and localization results; those stochastic results are not yet proved or assumed here.

The generic finite theorems here remain valid. Completing `prop:ub-first-moment` requires valid upstream estimates or a different proof preserving its original model assumptions. The false input is not accepted as an extra premise of that model theorem. Other tasks are still producing their Lean files, as requested by the user.
