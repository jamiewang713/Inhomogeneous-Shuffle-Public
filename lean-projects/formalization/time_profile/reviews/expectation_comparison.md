# Three-report comparison and freeze

The parent compared `expectation_math.md`, `expectation_design.md` and `expectation_adversarial.md` before any expectation Lean source was written. Each reviewer independently re-read the authorized source material and approved every definition and P01–P08 statement in the final draft.

All three agree on the concrete uniform law on the product of constrained column-assignment types. Nonemptiness, count conservation, row symmetry, normalization, integrability and column factorization are conclusions to prove, not new inputs. Marginals concern unsorted labelled rows; cardinality invariance supplies the separate sorted interpretation. The side suffix remains free, ambient counts are unconditional, and cF remains the deterministic maximum-of-expectations expression.

The draft already includes the reviewers' two typing/dependency clarifications: normalized observed-row legality requires N>0, and the column component of P02 precedes P03 while the full-matrix component may follow it. No further correction was requested. N=0, K=0, zero piles, impossible prefixes, empty side maxima and sample-dependent row permutations were checked. No time measurability, support, row independence, conditional-law or positivity hypothesis is added.

The unchanged final mathematical content was moved to `EXPECTATION_CONTRACT.md`, its status was set to frozen and a checksum was recorded before implementation was authorized. Public implementation declarations may split the reviewed conjunctions and introduce their explicitly reviewed finite-uniform helpers; they may not alter the mathematical domains or introduce scientific premises. P01–P08 closes only the expected-count interpretation, not conditional exploration or anti-concentration.
