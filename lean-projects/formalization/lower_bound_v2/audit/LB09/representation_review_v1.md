# LB09 independent representation review v1

Status: **APPROVE THE UNCHANGED FROZEN INTERFACE**, subject to the coordinator's completed-input registration and acknowledgement. This is a pre-proof statement/representation review, not certification of an LB09 theorem. No Lean proof, shared definition, contract, manuscript, or historical audit was modified.

## Reviewed scope and evidence

Read the adopted LB09 prompt; manuscript labels `lem:cold-geometry`, `lem:finite-relative-endpoints`, and `lem:localization`; frozen `Contracts/v1/WitnessGeometry.lean`; shared Geometry, Model, Path, Statistics, Empirical, and Adapters; original foundations Matrices and historical Cold/Sorting; completed LB02/LB05/LB06 sources and receipts; and `audit/LB09/INTERFACE_PROPOSAL_v1.md`.

All 43 files bound by the frozen v1 manifest match their recorded hashes. `python3 scripts/lane.py LB09 --check-ready` returned `LB09 CONTRACT_INPUTS_OK`. `python3 scripts/check_dependency_receipt.py LB06-completed-v1` returned `LB06-completed-v1 DEPENDENCIES_OK`. The LB02 receipt's 29 source hashes and LB05 receipt's nine source hashes match current files. These checks establish the reviewed inputs' identity, not downstream proof completion.

The principal reviewed file hashes are:

| File | SHA-256 |
|---|---|
| `Contracts/v1/WitnessGeometry.lean` | `bbd3f28678e95ace37f07c0d993992f20fd4dc4d565ccbc11d0b8a4f1ba822bc` |
| `RiffleLowerV2/Shared/Geometry.lean` | `cb992d0297bcf75ada15ff6154a146caadfa3d984629aafd70f74feef6bfbb09` |
| `RiffleLowerV2/Shared/Path.lean` | `513afea203a5ad1a3b851fdb8317b4f6473d2c54e1c0466139b349530563acbf` |
| `RiffleLowerV2/Shared/Model.lean` | `cceadf1b4a5be2f412fe15a9b52b7b7f3c67bfa6d19270955f7c338f01e90930` |

## Exact public interface decisions

Retain the following required theorem names, with no additional theorem binders or target changes:

```lean
RiffleLowerV2.Localization.relativeEndpoint : Targets.RelativeEndpointTarget
RiffleLowerV2.Localization.deterministicColdGeometry : Targets.DeterministicColdGeometryTarget
RiffleLowerV2.Localization.localization : Targets.LocalizationTarget
RiffleLowerV2.Localization.coldGeometryFromEmpirical : Targets.ColdGeometryFromEmpiricalTarget
RiffleLowerV2.Localization.lB09 : Targets.LB09Target
```

The last target is the conjunction of the preceding four target propositions in the frozen order: relative endpoints, deterministic geometry, localization, and empirical assembly. Its proof must assemble actual proved declarations. Merely importing or inhabiting a structure that records the target as an assumption is insufficient.

The relative endpoint theorem retains arbitrary `k N K`, including `N = 0`, with only `l ≤ m ≤ K`; its suffix is `WordOn k (columnSet K l m)`. Geometry construction retains `2 ≤ k`, positive fixed `T eta rho chiGood`, and `2*rho*log k ≤ kappa0 eta/100`, then chooses `xi`, a regular partition, and `N0` before every cut array and every witness satisfying `WitnessSpec`. Localization retains its threshold before every cut array, witness, and supplied geometry. The empirical assembly chooses `xi` and its partition before the requested probability tolerance. No thresholds may depend on a later cut array, chosen witness, selected word, or sample.

`LocalizationTarget` is deliberately a conditional intermediate whose input is concrete geometry data together with a proof of `GeometrySpec`. It does not complete LB09 alone: `deterministicColdGeometry` must construct that data, and `coldGeometryFromEmpirical` must discharge both witness and geometry inputs using actual LB05/LB06 results.

## Coordinate and finite-domain fidelity

The shared zero-based column set `columnSet K l m = {j | l ≤ j.val ∧ j.val < m}` is exactly the manuscript's one-based columns `(l,m]`. The correct blocks are `[ms,mu)`, `[mu,mu+bridgeLength)`, and `[mu+bridgeLength,K)` in Lean coordinates. `WordOn` has only those coordinates, so it avoids spurious cardinality factors from unused ambient columns. `wordOnList` orders them by the ambient column index. Lean proofs must establish its injectivity and the expected first-difference order; these facts are not encoded as assumptions.

`prefixAt` uses `min m K` to remain total. Every substantive application must carry the witness's depth bounds before simplifying away this minimum. `sidePrefix` is cut at `j+1`: the values it assigns later than `j` are harmless, and its earlier values are the ambient prefix followed by the initial part of `x`.

`joinColdWord` uses the ambient word only outside the three blocks. Under witness bounds those unused columns are exactly `[0,ms)`. The full-word cardinality assertion consequently requires a proof that the map `(x,z) ↦ joinColdWord G x G.central z` is injective. This is a finite coordinate restriction argument, including an empty tail block; it must not be asserted from `Finset.image` alone.

For `l=m`, the suffix domain is empty, its unique word has mass one, its mass-before is zero, its lower relative count is zero, and its upper relative count is the ambient count. Thus the right-hand fluctuation is precisely the ambient fluctuation. The universal endpoint target correctly retains this case. For `N=0`, all sample counts and prefix means are zero, so the totalized real divisions do not invalidate the identities. For `k=0`, nonempty word coordinates have no inhabitants; the empty-word cases are still valid.

As a supplementary representation check, an in-memory exact rational enumeration verified both endpoint identities in 3,864 cases: every binary column assignment with `0 ≤ N ≤ 3`, `0 ≤ K ≤ 2`, all ambient words, admissible `l,m`, and suffixes. This includes zero counts and empty suffixes. It is a finite sanity check, not a Lean proof or an asymptotic argument.

## Endpoints, rank conversion, and edges

The left relative endpoint is the sum of preceding first-difference side cylinders. The right identity has the essential term

```lean
(prefixCount (prefixAt l a) omega : ℝ) - prefixMean cuts (prefixAt l a)
```

before subtracting the following cylinders. The frozen target correctly preserves it. The finite bound is on the *sum* of both absolute endpoint errors, with factor

```text
A * ((2*sqrt(k*K)+1)*sqrt(muA) + 2*k*K+1).
```

Each side uses at most `k*K` disjoint subcylinders whose mean sum is at most the ambient mean. Prove this mass inequality before applying Cauchy--Schwarz; a bound on the number of side prefixes alone is insufficient. Nonnegativity handles zero and small means without dividing by them.

`integerHalfOpen l r` is exactly the integer set satisfying `l ≤ z < r`. Its floor/ceiling outer bounds merely make it finite. `coldRelativeSet` is a finite union, so adjacent selected intervals may merge. Cardinality estimates can use disjoint half-open probability intervals; boundary estimates must use subadditivity, not the false assertion that every selected interval is a separate connected component. The frozen `exp(-2)*N^h ≤ M ≤ 2*N^h` and `boundary ≤ 4*sqrt M` are explicit eventual bounds that require uniform absorption of the integer rounding terms. They are stronger concrete choices than bare source `o/O` notation, but are compatible with the source argument.

Sorted Lean positions are `i : Fin N`; the manuscript rank is `i.val+1`. `rank_interval_iff` translates `[L,U)` in zero-based coordinates to `(L,U]` in manuscript coordinates. `clipTranslate` then requires `manuscriptRank i - q ∈ Hrel`, where `q = lowerRank ambient omega`. Preserve these conventions and prove the reserve bound with its two spare units. Do not shift `Hrel`, replace its half-open convention, or bound the random translation probabilistically.

After localization is proved, assign each repeated complete word the edge whose zero-based left position is its complete-word lower rank. The count-at-least-two premise ensures this is in `Fin (N-1)`. Both endpoints carry that word and lie in `Hq`; equality of chosen edges forces equality of their endpoint words, proving injectivity. The target's graph uses `Fin (N-1)` edge identifiers, whereas historical Cold uses pairs of positions. A direct proof or an explicit finite equivalence is necessary when reusing the historical argument.

## Geometry and probabilistic proof obligations

Keep real `b = beta(s)` distinct from the central bridge word. At the first good column choose the central larger digit; at the second choose the smaller. The minus reserve changes only the first distinguished column, the plus reserve only the second. All three bridge mass bounds retain the exact `chiGood^2*k^(-bridgeLength)` factor. The all-digit lower bound is `min xi (min chiGood (1/k))`; positivity and every use of logarithms must be proved from the selected supports and good/maximal digits.

The proposal correctly avoids trying to absorb type errors into a possibly saturated displayed witness entropy inequality. The actual empirical result `H ≤ J`, together with `J ≤ b/2-3*kappa`, provides six units of `kappa` slack in `H ≤ b-J-6*kappa`. This permits the frozen post-rounding entropy buffer. Tail empirical exponents are on the block *after* the bridge: their comparison with the witness tail must explicitly subtract bridge integrals. `kappa0 ≤ kappa/100` explains why the stronger bridge budget is sufficient for both the reserve and collision exponent margins.

The proposed one-event localization proof is sound at the representation level. Use the actual `allPrefixEvent (kappa eta/4)` for every endpoint side prefix and every reserve prefix. Geometry gives `b ≥ 4*kappa` and reserve means `mu ≥ N^(b/2+kappa) ≥ N^(3*kappa)`. For `N ≥ 2`, sufficiently large uniformly in the fixed parameters,

```text
N^(kappa/4)*(sqrt(mu)+1) ≤ 2*N^(kappa/4)*sqrt(mu) ≤ mu/2
```

because `N^(5*kappa/4) ≥ 4` suffices. Consequently every reserve count is at least half its mean on that same event. This avoids an additional event and is a valid strengthening of the source's separate reserve-tail argument. The checked LB02 bound `2*(K+1)*k^K*exp(-N^(kappa/4)/8)` already supplies the required polynomial union bound, uniformly for `K ≤ T*log N`. No new union over tail words or independence from tail columns is needed. All deterministic tail-word conclusions must be obtained inside the same event implication.

The endpoint absorption must use `K ≤ T*log N` and `b ≥ 4*kappa` to prove the displayed error is at most `N^(b/2+kappa/2)`, with an `N0` independent of `b`. Reserve half-means must then exceed this error by two. Generic growth-limit or concentration lemmas are acceptable helpers only when their concrete inequalities are discharged in the final theorem.

## Completed inputs and import obstacles

| Input | Actual relevant exports | Reviewed status |
|---|---|---|
| LB00 | Frozen shared definitions and `Contracts.v1` | Ready; frozen hashes and lane readiness pass |
| LB02 | `Thinning.allPrefixConcentration`, `prefixFailureUniform`, `prefixTails`, `exists_canonicalMaxWord`, maximal-word identities | `LB02_READY_v1.json` says complete; source hashes match; Main and relevant `.olean` files exist in shared and lane overlays; obtain the coordinator's current completed-input acknowledgement before dependent use |
| LB05 | `Witness.oneColumnTilt`, `empiricalTilt`, `coldWitness`, `lB05` | `LB05_READY_v1.json` says ready; source hashes match; lane Main output exists, but shared `Witness/Main.olean` was absent at review time; coordinator registration is required |
| LB06 | `Types.roundedType`, `constructedTypeData_spec`, `exists_type_partition`, empty-block and approximation lemmas | Completed integration receipt exists; shared Main output exists; `LB06-completed-v1` check passes |
| Deterministic sorting | `Model.prefixRanks` in completed `Model.Sorting` | Already integrated; use only if the coordinator acknowledges this optional helper dependency, or supply an owned provenance-preserving proof |

No old `RiffleLower/Sorting.olean` or `RiffleLower/Cold.olean` is registered in the shared overlay. Foundations `RiffleShuffle.Matrices.olean` is registered and provides legal-prefix rank statements, though adapting them requires proofs of legality and model compatibility. Historical Cold's `localized_collisions_supply_edges` is mathematically suitable only after its actual `localizedKeys` premise is established. Any local source adaptation needs recorded provenance and a new proof checked under the pinned toolchain. Importing historical cache files is not acceptable.

The needed maximal-prefix mean identity is at the selected depth `ms`; LB02's horizon maximal-word identity alone is not literally that statement. Use the checked canonical-word existence and prove the grid-prefix product identity, or explicitly prove a truncation adapter. This is an API obligation, not a missing mathematical hypothesis.

The proposal requests exactly the appropriate unchanged interface and import acknowledgements. No mathematical counterexample or necessary target amendment was found. Remaining obstacles are coordinator integration/authorization, finite coordinate and lexicographic APIs, exact integer boundary bookkeeping, and substantial uniform estimates; none may be concealed as a premise naming the desired result.
