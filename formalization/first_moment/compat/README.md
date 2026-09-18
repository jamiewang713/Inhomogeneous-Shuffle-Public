# Common Lean 4.33.1 compatibility sources

The time-profile and foundation packages use Lean4.33.1. The completed stable-block and first-moment model modules were checked initially on Lean4.19.0. These local copies allow importing the completed layers together without changing any frozen original source.

`lean-4.33/stable_blocks` contains the eleven previously proved modules. Four proof-only edits address changed match simplification and renamed mathlib APIs. All153 theorem declarations compile and their dependency audit reports only standard Lean foundations. The original definitions and theorem statements are unchanged.

`lean-4.33/FirstMomentModel` contains copies of the three completed model modules. The changes are a renamed mathlib import, the renamed natural-cardinality injection theorem, and an explicit unfolding in a cardinality proof. All definitions, theorem assumptions and conclusions are unchanged. The native4.19 modules and their freeze records remain authoritative.

Each directory contains `PROVENANCE.json` with both original and compatibility hashes and `COMPATIBILITY.patch` with the complete diff. The scripts `check_compat_stable.py` and `check_compat.py` check provenance before building. Their outputs are separate from the native4.19 artifacts. The first-moment core compiles unchanged on both versions.

This is source compatibility, not a mathematical model equivalence. Importing both layers does not prove the pending list/vector, event, expectation or numerical adapter identities. Those require separately reviewed and frozen theorems.
