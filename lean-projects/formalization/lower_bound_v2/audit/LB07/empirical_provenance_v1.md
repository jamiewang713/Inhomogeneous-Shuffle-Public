# LB07 empirical primitive port v1

Source: `RiffleLowerV2/Witness/Empirical.lean`, SHA-256 `7220bb0fcb372ec11eb74a284f0dfeacd9485a1bf0618d3be6612097159072c8`.

Destination: `RiffleLowerV2/ProfileTransfer/Empirical.lean`, SHA-256 `fcb5630c0d0d0703526c7bcd06ee41f20c68803c10a78d81f51383d736051751`.

Only the declaration namespace and a provenance comment changed. Definitions remain imported from the frozen Shared module. This is source reuse with no import or build dependency on the Witness lane. Its mathematical proofs were freshly compiled by Lean 4.33.1 through `python3 scripts/lane.py LB07 RiffleLowerV2.ProfileTransfer.Empirical`; `empirical_build_v1.log` reports `LB07 BUILD_OK`. The port covers finite monotonicity, constant integration, endpoint bounds, continuity, and linearity. Public signatures are unchanged up to namespace.
