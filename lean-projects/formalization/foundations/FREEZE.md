# Frozen foundation contract

Frozen at 2026-09-17T20:08:17.042471+00:00 before the first project Lean file was written.

CONTRACT.md SHA-256: `2d48b42c85f7946ddb308efc21d47a4e6b596b497d5c8e447f4ae9ac1062dfd0`.

All 74 IDs received three independent source-based reviews: mathematical reconstruction, Lean representation design, and hidden-assumption/counterexample audit. The reports are under reviews/. The primary agent compared their reports before this freeze.

Agreement: N>0 and k≥2 are standing source data; K=0 and zero pile counts remain allowed. No profile-regularity, independence, asymptotic, positivity-of-every-pile, or sortedness assumption was added. Sorting is a certified permutation and matrix existence is proved.

Resolved BEFORE freeze: endpoint comparisons use equal-length truncations; rankSet is a Finset; blockGraph is a spanning restriction with outside vertices isolated; J is defined at every depth but normalization/coverage requires depth≤K. These are explicit representation conventions and the endpoint repair is grounded in the older papers.

After this freeze, proof scripts and local proof steps may change; mathematical assumptions, definitions, and named theorem statements may not. No axiom, sorry, admit, placeholder, or unsupported project lemma is permitted. Any additional named lemma requires stopping rather than silently extending the contract. Standard trusted Lean foundations and mathlib are the only external logical inputs.
