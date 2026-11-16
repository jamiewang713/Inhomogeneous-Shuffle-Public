# CONTRACT_READY — LB-00 / v1

Released 2026-10-01T14:33:14.631459+00:00.

**The shared foundation is ready. LB-01–07 may begin. Neither lower-bound theorem is proved.** Later lanes must still observe the dependency prerequisites in OWNERSHIP.json; checking their shared inputs does not discharge those prerequisites.

## Immutable identity

* Contract manifest: `Contracts/v1/SHA256.json`
* Manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`
* Authoritative manuscript SHA-256: `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d` (matches the planning snapshot).
* Runtime: Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
* Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`. All nine installed dependency revisions were checked against the pinned manifests.

## Imports and exact exports

Import `RiffleLowerV2.Shared` for concrete definitions and checked routine adapters. Import `Contracts.v1` for the versioned target statements. `RiffleLowerV2` is the complete foundation umbrella. Target definitions are propositions, never evidence.

Every exact public declaration type and pending target body is printed in `Contracts/v1/EXPORTS.md`, with source locations and axiom closure. The corresponding machine-readable record is `audit/LB00/public-exports.json`; the complete elaborated dependency record is `compiled-declarations.json`. OWNERSHIP.json specifies each later theorem's exact name and target type. All 58 target propositions have exactly one owner and remain unproved.

The 17 proved public adapters cover canonical sample nonemptiness, row/vector access, sorting/graph compatibility, physical inverse as the map of forward inversion, finite expectation/integral/average, step-integral additivity and exact grid sums, empty-prefix identities, rank conversion and clipping. There is no proved physical/matrix or graph-mixture law identification at this stage.

## Verified execution

From the package directory:

```text
python3 build.py --fresh --audit
python3 build.py RiffleLowerV2.Shared
python3 build.py RiffleLowerV2.Shared.Smoke
python3 build.py
```

All succeeded. The fresh run rebuilt the eight imported canonical project modules and every new module in isolated package-local output. See `build-v1.log`, `lane-LB00-build.log`, `smoke-v1.log`, and `post-freeze-build-v1.log`. The post-freeze run verified the immutable contract/source hashes. Every lane's `scripts/lane.py LBxx --check-ready` passed; see `lane-readiness-v1.log`.

The axiom audit checked the types and bodies of all 364 new elaborated declarations. Its union is exactly `propext`, `Classical.choice`, and `Quot.sound`. No custom axioms, proof placeholders or native proof oracles enter the checked closure. Initial development logs are not certification receipts.

## Independent reviews and scope

The mathematical, representation and missing-hypothesis reviewers approved the exact source and refreshed compiled inventory. Their reports and `REVIEW_RESOLUTION.md` retain the findings and resolutions, including the exact ambient translate in ManyEdgesTarget. No review condition remains open for foundation release.

**E remains pending:** a uniform empirical positive-margin physical-inverse-law lower theorem. It has no TimeLaw or temporal regularity. The largest branch has no local-good premise; the cold branch includes positive rho and its kappa0 mesh budget.

**M remains pending under explicit scalar integrability:** the chosen transfer partition's cell masses and scalar a/psi costs are interval integrable. This is visibly stronger than the historical arbitrary totalized-TimeLaw contract. No kernel, time smoothness or macro J/H regularity was added.

**The original unchanged arbitrary-TimeLaw macro statement remains uncertified.** Its definitions and historical freezes are preserved. The manuscript and old packages were not edited by LB-00. This receipt authorizes downstream proof work, not a lower-bound theorem claim.

## Ownership and changes

Only LB-00 edits shared definitions, target contracts, dependencies, tooling and umbrella imports. Every lane owns its assigned directory and audit subtree. Lane output uses `.build/lanes/LBxx/`; coordinator builds are serialized. Source compatibility ports require provenance and checked adapters from their designated owners. Any shared interface change requires a reviewed additive version and a new receipt; never regenerate this manifest or overwrite this release's reports.
