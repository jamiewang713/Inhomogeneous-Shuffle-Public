# Lower-bound dependency and status ledger

This is a dependency map, not a list of proved lower-bound results. All pending target definitions are executable statement checks only.

| Lane | Exclusive proof directory | Dependencies | Source labels | Status |
|---|---|---|---|---|
| LB01 | `RiffleLowerV2/Model/` | LB00 | `lem:ub-graph-representation` | Pending proof |
| LB02 | `RiffleLowerV2/Thinning/` | LB00 | `lem:successive-thinning-tail`, `cor:iterated-hypergeom`, `prop:largest-prefix` | Pending proof |
| LB03 | `RiffleLowerV2/Factorial/` | LB00 | `lem:fixed-column-factorial`, `lem:central-window` | Pending proof |
| LB04 | `RiffleLowerV2/Ascent/` | LB00 | `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley` | Pending proof |
| LB05 | `RiffleLowerV2/Witness/` | LB00 | `lem:cold-witness` | Pending proof |
| LB06 | `RiffleLowerV2/Types/` | LB00 | `lem:type-estimates` | Pending proof |
| LB07 | `RiffleLowerV2/ProfileTransfer/` | LB00 | `lem:lower-profile-transfer` | Pending proof |
| LB08 | `RiffleLowerV2/Occupancy/` | LB00, LB02, LB03 | `lem:two-category-poisson` | Pending proof |
| LB09 | `RiffleLowerV2/Localization/` | LB00, LB02, LB05, LB06 | `lem:cold-geometry`, `lem:finite-relative-endpoints`, `lem:localization` | Pending proof |
| LB10 | `RiffleLowerV2/EmpiricalLower/` | LB00, LB01, LB02, LB04, LB08, LB09 | `prop:largest-prefix`, `lem:many-edges`, `lem:lalley`, `prop:cold-lower` | Pending proof |
| LB11 | `RiffleLowerV2/MacroscopicLower/` | LB00, LB07, LB10 | `thm:buffered-reduced-lower-bound`, `lem:lower-profile-transfer`, `prop:cold-lower` | Pending proof |

LB-12 owns `audit/LB12/` only. It may inspect this contract now; final certification requires completed LB-10 and LB-11.

## Checked reusable foundation

* Canonical `RiffleTimeProfile.Base`: simplex costs, Cuts, BorelPartition/regularity, TimeLaw, AlmostLike and LocalGood, unchanged.
* Canonical `RiffleTimeProfile.Ambient` and `FixedCountModel`: finite prefix definitions, exact fixed-histogram sample construction/nonemptiness, PMF law and finite integral/average identities.
* Canonical `RiffleShuffle.Basic`, `Profiles`, `Words`, `Matrices`, `Graphs`: lex-vector words, deterministic sorting, legal prefix ranks, full-word equality graph and reachability. Explicit `toPileProfile`/`toMatrix` adapters connect these to canonical Cuts/Sample.
* New Model/Empirical/Path/Statistics/Geometry definitions are compiled. Shared theorem types and complete axiom closures are printed in `Contracts/v1/EXPORTS.md`. New routine proofs cover row/vector access, matrix sort/graph adapters, inversion as PMF map, expectation/integral/average, empirical additivity/grid sums, empty-prefix mass/count, rank conversion, clipping membership/cardinality, and sample nonemptiness.
* No probability-law equality, empirical cold witness, rounded type estimate, concentration/occupancy/localization, or TV endpoint is counted as proved.

## Compatibility and elementary-helper owners

| Owner | Read-only reuse candidates | Port location if needed |
|---|---|---|
| LB01 | old RiffleLower finite probability/sorting/uniform permutation tools | `RiffleLowerV2/Model/Compat/` |
| LB02 | old Shuffle hypergeometric, fixed-column and residual-sampling tools | `RiffleLowerV2/Thinning/Compat/` |
| LB03 | old fixed-column factorial proofs, canonical moment calculations | `RiffleLowerV2/Factorial/Compat/` |
| LB04 | old uniform-permutation counting | `RiffleLowerV2/Ascent/Compat/` |
| LB05 | old finite cold algebra; canonical one-column analysis | `RiffleLowerV2/Witness/Compat/` |
| LB06 | lean_formalization finite entropy/type-count helpers | `RiffleLowerV2/Types/Compat/` |
| LB07 | canonical lattice counts/quadrature/regular partition construction | `RiffleLowerV2/ProfileTransfer/Compat/` |
| LB09 | deterministic RiffleLower cold edge extraction, only after localization is proved | `RiffleLowerV2/Localization/Compat/` |
| LB10 | largest-word run/TV finite bound if not already integrated by LB01 | `RiffleLowerV2/EmpiricalLower/Compat/` |

Ports are source ports with renamed owned namespaces and original/ported hashes, never old-version cache imports. Dependency registration remains LB00-owned. Existing first_moment 4.33 ports are read-only candidates; none is required by this foundation. Whole upper-proof trees and the old vendored RiffleTimeProfile are excluded.

## Required pending mathematics

All exact future names and target types are in OWNERSHIP.json; every referenced target expands in the compiled EXPORTS inventory. The bundles LB05Target/LB09Target are convenience conjunctions, not premises of final E/M. Intermediate specs may be consumed only after their owners produce checked proofs.

No upper-bound first-moment result, anti-concentration claim, random-pile extension, zero-margin limit or full-cutoff theorem is included.
