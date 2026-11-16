# LB-06 interface proposal v1

Status: proposal for coordinator acknowledgement; no dependent proof work begun.

The required export remains exactly `RiffleLowerV2.Types.roundedType : RiffleLowerV2.Targets.RoundedTypeTarget`, as frozen in Contracts/v1/WitnessGeometry.lean. The source is lem:type-estimates, manuscript SHA-256 672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d. No shared definition or hypothesis amendment is proposed.

The quantifier order stays k >= 2, C >= 0; Ctype(k,C)>0; T>0, 0<xi<1/(4k); m; Cround(k,C,T,xi,m)>0 and N0>=2; every N>=N0,K,P with m cells and IsRegular xi C; every concrete Cuts, arbitrary selected I with cardinality <= T log N; every alpha in [2,4]; an actually constructed RoundedTypeData satisfying both frozen predicates. In particular no LB05 or macroscopic approximation is assumed.

The exact shared objects retained are WordOn, massOn, retainedTilt, cellPositionCount, wordCellCount, RoundedTypeData, roundedClass, massBin, selectedClass, typeJ, typeH, TypeDataSpec and TypeApproximation. Empty selected sets have the unique empty word, zero counts and bin 0. Empty cell factorial terms are 1.

The three independent pre-proof reviews are being recorded as math-review-v1.md, representation-review-v1.md and hypotheses-review-v1.md in this directory. Preliminary findings agree that no frozen target change is needed. Before proofs the lane will compare the completed reports and resolve findings in a separate new record.

Private proof layers: normalized retained weights and quantitative replacement; deterministic supported integer counts (cumulative-floor rounding is an acceptable deterministic realization with coordinate error <1); exact finite type-class cardinalities and two-sided logarithmic factorial/rounding estimates; least maximal mass-bin selection and exact exponent bounds; uniform assembly with explicit constants. All private sources stay within RiffleLowerV2/Types/.

Requested coordinator dependency action: register and compile canonical RiffleTimeProfile.Analysis under the pinned 4.33.1 runtime, preserving its original source, to use exists_regular_partition (constant 1 independent of xi). Also make the pinned Mathlib.Data.Nat.Choose.Multinomial and Mathlib.Analysis.SpecialFunctions.Stirling modules available in the shared read-only overlay if feasible; both currently lack compiled overlay outputs. These are trusted source dependencies, not hypotheses. Any required additive provenance/receipt belongs to LB00. No old toolchain cache import is requested. Lane builds remain scripts/lane.py LB06 RiffleLowerV2.Types.Main.

Readiness: scripts/lane.py LB06 --check-ready returned LB06 CONTRACT_INPUTS_OK. Existing frozen v1 manifest digest is 4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858. Please acknowledge unchanged interface and the dependency additions in a new receipt without overwriting the release.
