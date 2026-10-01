# LB-03 coordinator integration evidence v1

LB00's serialized `RiffleLowerV2.Factorial.Main` build passed. The compiled module exists in the shared coordinator cache, so downstream lanes can import it through the standard lane workflow.

The coordinator's full compiled-namespace audit contains 278 declaration records, including all ten required exports and the private/generated helper declarations. The union of their transitive axiom closures is exactly `propext`, `Classical.choice`, and `Quot.sound`. LB03 independently read and validated this evidence after completing its own lane/export audit.

Evidence:

- `audit/LB00/LB03_integration_build_v1.log`
- `audit/LB00/LB03_integration_build_provenance_v1.json`
- `audit/LB00/LB03IntegrationCheck_v1.lean`
- `audit/LB00/LB03_integration_audit_v1.log`
- `audit/LB00/LB03_integration_declarations_v1.json`

This supplements `DELIVERY_v1.md` and `verification_v1.json` without altering their earlier records. The original frozen contract and all source hashes remain unchanged. LB00 owns its formal integration-release record; this file records LB03's adoption of the already successful shared build and complete namespace audit.

Build-log SHA-256: `c42ffafc34ae56b11cd16aa4e5859cc00ecf4ba0d9a519369496e811a9ee31ea`.

Compiled-declaration JSON SHA-256: `4d31455c9ca41fd34cf38ed8cba67b871b94b9d682f6527b5f8f609d31a8aa2a`.
