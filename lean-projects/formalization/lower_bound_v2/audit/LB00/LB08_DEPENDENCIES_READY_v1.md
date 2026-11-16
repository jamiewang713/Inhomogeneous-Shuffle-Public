# LB08 completed-dependency readiness v1

**DEPENDENCIES_READY** under the unchanged frozen v1 contract. The coordinator has built and audited both required completed inputs in `.build/lib/lean`:

- `import RiffleLowerV2.Thinning.Main`: LB02's seven exact targets, concrete residual prefix transforms/tails and direct residual independence are certified by `audit/LB00/LB02_INTEGRATION_ACK_v1.md`.
- `import RiffleLowerV2.Factorial.Main`: LB03's ten exact targets and actual conditional deleted-word mean are certified by `audit/LB00/LB03_INTEGRATION_ACK_v1.md`.

LB02 registry manifest `Contracts/dependencies/LB02-v1/SHA256.json`: `3c56558d2661a6d89fe9b095400a8a52516342dd0da74bde8ca690944556ab66`. Integration receipt SHA-256: `0db93734c4e1cf214bb967b2de85a354182367eb17328ef53a79786c3396e6cf`.

LB03 registry manifest `Contracts/dependencies/LB03-v1/SHA256.json`: `ec889ccc6409f4339ff31b41beae3b5847b90ac6eb62eab0809f263f29fc2c4f`. Integration receipt SHA-256: `fe879399d33a3b2102d8c1952be8889c8a169a6ad1c957065d92c5caa044e9ae`.

Both read-only checks passed: `python3 scripts/check_dependency_receipt.py LB02-v1` and `python3 scripts/check_dependency_receipt.py LB03-v1`. Both imports are present in the coordinator overlay. LB08 need not change shared cache or configuration; use the existing assigned lane build after the pre-proof review/proposal acknowledgement.

This receipt certifies upstream readiness only. It does not replace the pending review of LB08's exact interface, prove any occupancy target, or change any frozen type, historical receipt or final endpoint status.
