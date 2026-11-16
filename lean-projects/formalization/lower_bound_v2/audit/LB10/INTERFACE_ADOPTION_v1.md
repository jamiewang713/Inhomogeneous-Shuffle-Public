# LB10 interface adoption before proofs

The implementation adopts the unchanged five frozen targets in `OWNERSHIP.json`:
`EmpiricalLower.finiteLargestWordTV : Targets.FiniteLargestWordTV`,
`EmpiricalLower.largestOnly : Targets.LargestOnlyTarget`,
`EmpiricalLower.manyEdges : Targets.ManyEdgesTarget`,
`EmpiricalLower.coldOnly : Targets.ColdOnlyTarget`, and
`EmpiricalLower.empiricalCombined : Targets.EmpiricalCombinedTarget`.

No shared definition or contract addition is proposed. The existing LB00
`CONTRACT_READY.md` receipt authorizes these target types; completed integration
receipts certify LB01, LB02, LB04, LB08 and LB09. Read-only verification of
LB01-v1, LB02-v1, LB04-v1, LB04-completed-v1, LB08-v1 and LB09-completed-v1
passes, as does `scripts/lane.py LB10 --check-ready`. The manuscript SHA-256 is
the exact planning snapshot, `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.

The three independent initial reviews agree that the exact targets have a valid
proof route and require no extra hypotheses. In particular, the arbitrary-k
finite largest-word statement must remain arbitrary-k, and no local-good
hypothesis enters the largest-only branch. The physical/matrix and graph laws
are proved inputs. The cold margin fixes kappa and kappa0 before all thresholds.

Implementation-local helper declarations will prove the actual contiguous-run
adapter and uniform null bound, the collision mean/variance consequences, and
the physical graph-scan consequence. Any generic helper premises will be
discharged at the five frozen exports. The combined threshold is the maximum
of the two largest-word thresholds and the cold threshold, so alternating
arrays are included. All new proof sources stay in `EmpiricalLower/`; reports
and source-port provenance stay in this audit directory.

The final delivery will record full compiled types, source-label mapping,
dependency closure, source hashes, successful lane build and axiom audit,
and independent final reviews. This adoption record is not a completion claim.
