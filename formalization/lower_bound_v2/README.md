# Lower-bound integration foundation (LB-00)

This package supplies the compiled shared model, definitions, routine adapters and versioned target statements for the revised lower-bound proof. **It does not prove either lower-bound endpoint.** `Contracts.v1` contains proposition-valued definitions only; no lane may use one as evidence. See `Contracts/v1/EXPORTS.md` for every exact compiled export, `OWNERSHIP.json` for exclusive paths and future proof names, and `audit/LB00/CONTRACT_READY.md` for the release receipt.

## Certified scope

E is a uniform empirical lower-bound target for `physicalInverseLaw`: fixed positive largest-word or cold margin, actual deterministic finite columns, and no `TimeLaw`. Local-good columns and the positive mesh restriction `2 rho log k ≤ kappa0 / 100` occur only in the cold alternative. The separate largest-word target has no local-good parameters.

M is a separate macroscopic target **under explicit scalar integrability**. It selects the transfer partition before requiring interval integrability of that exact partition's cell masses, `profileMaxCost`, and `profilePsi` for every alpha in `[2,4]`. It adds no time continuity, measurable-kernel requirement, or macro J/H integrability. The old arbitrary `TimeLaw`, `AlmostLike`, and integrated costs remain unchanged. The unchanged historical arbitrary-TimeLaw theorem is not certified.

## Build

The verified entry point is `python3 build.py`, run in this directory. It checks Lean **4.33.1** and mathlib commit **0df444a360eaa60ab8c11dca51a86af692955474**, verifies released contract/source hashes, and discovers every Lean module under `RiffleLowerV2/` and `Contracts/`. `python3 build.py --fresh --audit` rebuilds all imported canonical project sources and the new foundation, then inspects the elaborated axiom/dependency closure. Cache-backed mathlib modules are read-only. Missing mathlib modules compile only into this package's private overlay.

The default compiler is `/Users/jialushi/Documents/loop soup/formalization/.tools/lean-4.33.1-darwin_aarch64/bin/lean`; the default package cache is `../.lake/packages`. An equivalent installation can be selected with `LBV2_LEAN` and `LBV2_PACKAGES`; version and commit checks still apply. The Lake file records the same dependency pins; **the custom entry point, not a mutating Lake dependency update, is the verified workflow**. No old `.olean` from the 4.19/4.24 projects is imported.

For a new verification run, redirect output to `.build/new-audit.log`, then run `python3 scripts/audit.py --log .build/new-audit.log --out .build/new-audit`. Preserve released audit snapshots.

Only the coordinator runs package builds or changes dependencies. A filesystem lock prevents concurrent coordinator builds. Lane owners compile through `python3 scripts/lane.py LBxx RiffleLowerV2.<OwnedDirectory>.Main`; each receives `.build/lanes/LBxx/lib/lean`. This entry point compiles only its owner's sources and refuses missing upstream compiled modules. `--check-ready` verifies the released inputs without starting proof work. LB-12 owns audit files only.

## Model and conventions

`TimeProfile.Cuts`, `ShuffleSample`, and `fixedCountPMF` are the canonical concrete sampling basis. Words are the foundations library's length-indexed lexicographic vectors; variable prefixes are a sigma over their actual lengths. `WordOn` has only the selected columns as coordinates. No unused suffix multiplicity enters a prefix or type-class cardinality.

`stableSort` sorts complete row words and maps sorted positions to original labels. `matrixLaw` is its actual pushforward. `physicalForward` independently defines successive chronological cut/interleave operations on position-to-label decks; `physicalInverseLaw` is its inverse pushforward. Their identification with `matrixLaw`, and the independent graph-component mixture identity, are LB-01 proof obligations. The sole checked inversion identity at this stage is the definitional PMF map identity.

Positions are zero based. `manuscriptRank i = i.val + 1`; `[L,U)` corresponds exactly to paper ranks `(L,U]`. `clipTranslate` preserves the literal integer set `H0` and tests `i.val+1-q ∈ H0`. Boundary is taken in the whole integer path, including deck endpoints. Component sorting explicitly uses a lexicographic component/value pair. Expectations and variances are real finite sums, and TV is half the finite L1 distance.

Empirical A/B/J/H use a signed finite step primitive on `S_N = floor(T log N)/log N`. The grid-sum and additivity identities are proved. Their definitions require no macroscopic time regularity. Witness, rounded-type and geometry structures carry only data; their required properties are separate propositions that their owners must prove.

## Release discipline

The version-1 hash manifest is immutable. Never edit a frozen shared file, change a target silently, overwrite a historical report, or regenerate an old manifest to make it pass. Additive changes require independent mathematical/representation/hypothesis review, a new contract version and a new receipt from LB-00. Downstream authors propose additions only in their own `audit/LBxx/` paths. Original packages and the manuscript are read-only for this task.

Seven first-stage lanes LB-01–07 can start from this foundation independently. LB-08 waits for 02/03; LB-09 for 02/05/06; LB-10 for 01/02/04/08/09; LB-11 for 07/10; LB-12's final audit waits for 10/11. No downstream lane was started by LB-00.
