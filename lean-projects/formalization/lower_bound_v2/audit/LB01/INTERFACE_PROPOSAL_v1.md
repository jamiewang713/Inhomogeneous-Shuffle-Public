# LB-01 interface proposal v1 — pre-proof

The released LB-00 v1 contract is the intended public interface. No shared assumption, definition, conclusion, target name, toolchain, or import is proposed for change.

Required exports in namespace RiffleLowerV2.Model remain exactly the eight names in OWNERSHIP.json: columnIndependence : Targets.ColumnIndependence; rowRelabeling : Targets.RowRelabeling; stableTie : Targets.StableTie; prefixRanks : Targets.PrefixRanks; graphRepresentation : Targets.GraphRepresentation; graphEventIdentity : Targets.GraphEventIdentity; physicalMatrixBridge : Targets.PhysicalMatrixBridge; inversionTV : Targets.InversionTV.

All quantification stays over arbitrary natural k,N,K and actual Cuts, including empty decks, empty time horizons, and zero piles. The proof will use the canonical uniform assignment space directly; no old permutation sample space will be identified by notation. Any later use of old sample spaces requires a proved map-law equality. Local helper definitions and theorems stay under Model/ and do not alter Contracts/.

Planned proof layers:
1. Finite PMF pushforward/expectation identities; product uniform expectations; explicit equivalence reindexing all column assignments by a row permutation.
2. Stable tie order and prefix intervals; generic finite ordered-key sorting helpers; equality blocks equal graph components.
3. Conditional word-multiset uniformity as an unconditional finite-sum identity using row relabelling. Within-block permutation fibers have product factorial cardinality. Independent permutation enters by an actual nested PMF bind/map.
4. Reverse chronological stable sorting and an explicitly invertible triangular pullback of columns, proving physicalInverseLaw=matrixLaw. This must be a separate theorem; no graph endpoint claims the physical bridge implicitly.
5. Inversion invariance of finite TV against the uniform permutation law.

The three required independent pre-proof reviews are being saved separately to math_review_v1.md, representation_review_v1.md, and hypotheses_review_v1.md. Their comparison and the coordinator response will be recorded before dependent proofs begin. No completed-input receipt is requested at this stage.

Verified input: scripts/lane.py LB01 --check-ready returned LB01 CONTRACT_INPUTS_OK. LB-00 CONTRACT_READY v1 manifest SHA-256 is 4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858. Authoritative manuscript SHA-256 is 672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d.
