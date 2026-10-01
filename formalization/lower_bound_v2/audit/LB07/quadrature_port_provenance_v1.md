# LB07 quadrature compatibility source provenance v1

Fresh ports use only package-pinned Lean/mathlib and the registered Base import. Full original modules are preserved unchanged.

- `../time_profile/RiffleTimeProfile/LatticeCounts.lean`: SHA-256 `7b2e19acfe289380f5d97ef32be6537ea863112fc4bab4e204335c2980266f0b`
- `../time_profile/RiffleTimeProfile/IntegralEnvelope.lean`: SHA-256 `aee7d4d77c460e60e0f27921f805467f3ee109973665434183786274569b5b9c`
- `../time_profile/RiffleTimeProfile/GridQuadrature.lean`: SHA-256 `4eea67379fd91b79e44c0272ed91baf358c31825740d4a8e46d6520b0f668777`
- `../time_profile/RiffleTimeProfile/AnalyticParameters.lean`: SHA-256 `fa82137739888ac1731858ac3b8ab65adef1d9a8a2d0ed943d5225d74fcaf1f6`

LatticeCounts, IntegralEnvelope, GridQuadrature differ only in namespace/imports and provenance comments. Error ports only the quadratureError definition. All output is within ProfileTransfer/Compat.
