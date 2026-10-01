# LB09 deterministic geometry implementation receipt v1

The exact frozen deterministic target is proved:

```lean
import RiffleLowerV2.Localization.Geometry
#check RiffleLowerV2.Localization.deterministicColdGeometry
-- RiffleLowerV2.Targets.DeterministicColdGeometryTarget
```

Source correspondence: manuscript `lem:cold-geometry`. The proof constructs a fixed cutoff and regular partition, both actual rounded classes, the canonical ambient word, concrete central bridge and reserves, actual full-word family, and the shared integer cold set. Every field of GeometrySpec is discharged. No localized-family premise or target-valued assumption is used.

## Implementation and constants

`Geometry/Algebra.lean` proves the scalar perturbation bounds, retaining the six-kappa entropy margin from H≤J. `geometryError eta` is exactly the frozen `min(kappa eta,kappa0 eta)/1000`.

`Geometry/Rates.lean` chooses xi as the reciprocal of a sufficiently large fixed natural number using log n/n→0, then chooses a regular partition with constant 1 and a uniform type threshold. Its `exists_uniform_type_data` puts cuts, position sets and tilts after N0. `exists_geometry_scalar_thresholds` gives the two explicit bridge upper bounds by kappa0/50, log N≥12/kappa, and absorption of the fixed `exp(-1)*chiGood^2*k^(-1)` reserve factor. All thresholds precede cuts and witnesses.

`Geometry/Empirical.lean` reuses the checked shared grid-integral identity, specializes the actual type error to J/H, and bounds the actual deleted bridge integrals. `Geometry/Bounds.lean` combines these with WitnessSpec and BridgeSpec to prove all five effective exponent inequalities.

`Geometry/Consequences.lean` proves exact full-family cardinality, strict lower/weak upper full-word mass bounds, reserve mean lower bounds with every fixed factor, and the shared positive digit floor for full words and reserves. It uses the independently implemented concrete word-factorization and bridge APIs. `Geometry.lean` combines these with the independently implemented `coldRelativeSet_estimates`, preserving the frozen factors exp(-2), 2 and 4.

## Verification

From `formalization/lower_bound_v2`:

```text
python3 audit/LB09/serial_build.py RiffleLowerV2.Localization.Geometry
python3 audit/LB09/serial_build.py RiffleLowerV2.Localization.Geometry.Check
```

Both succeeded without warnings. Final logs are `audit/LB09/geometry_build_dev03.log` and `audit/LB09/geometry_axioms_v1.log`, each ending `LB09 BUILD_OK`. Check.lean includes a literal assignment to the frozen target and prints the target plus its major helper axiom closures. Every printed closure is exactly the standard set `propext`, `Classical.choice`, `Quot.sound`.

All unsuccessful development logs were preserved under distinct names. No shared file, contract, cache configuration, upstream source, manuscript, or historical audit was modified. The only implementation writes by this worker are Geometry.lean, Geometry/*.lean and new LB09 audit artifacts. Independent final review of these implementation files is requested from another worker; the author's own verification does not replace it.

## Source hashes

| Source relative to Localization/ | SHA-256 |
|---|---|
| Geometry.lean | e15fde27bdb4ee637de7cc336d2598accd64aa915c527c9767ddfe807d608553 |
| Geometry/Algebra.lean | 18ece81b27c2316022703f93813ddf5cc450f1e1e28717b8f750a34cd7822235 |
| Geometry/Bounds.lean | a8c6b7796fb4d6b7610511024c1c5ea22b2187ff9013b7c8bca93d56ec1afa1c |
| Geometry/Check.lean | e424266a03821635e4fe39894f148a25a956bb426cfed5c72cb86a4fd2df0419 |
| Geometry/Consequences.lean | 0647c1532f4682f21edcd078fab3cff5188a262714bc983b5cd7c6f8ec15e451 |
| Geometry/Empirical.lean | 3af636f6d58c60ef073295b3d4207336cee41f1ab0fe5e26923e2dd17e67bc18 |
| Geometry/Rates.lean | 7e97b7705b2adbe9ca9b4707a792f2bbb383897d611b16182aaf2afb9dc86a58 |

No deterministic geometry obligation remains pending in this implementation. Final probabilistic localization, relative endpoints, empirical assembly, global axiom inventory and overall LB09 receipt are the coordinator/other workers' remaining obligations.
