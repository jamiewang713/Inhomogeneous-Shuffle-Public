# Additive completed umbrella comparison v1

The original `RiffleLowerV2.lean` imports only Shared and Contracts.v1 and is hash-frozen by Contracts/v1/SHA256.json. It is retained byte-for-byte as the historical foundation entry point.

The new `RiffleLowerV2.Completed` imports that foundation and all eleven completed lane Main entry points. Consumers of the completed proof package should import this module. It changes no definition, assumption, proof source, historical manifest or existing module import list. The new import graph is acyclic: every lane depends on the frozen foundation or earlier lanes, and none imports Completed.

The original build.py, scripts/audit.py and Check.lean remain frozen. A separate versioned full-check runner uses the pinned frozen builder with an empty isolated output directory and supplies a new complete environment audit. This prevents the foundation-only audit from being mistaken for a final proof audit.
