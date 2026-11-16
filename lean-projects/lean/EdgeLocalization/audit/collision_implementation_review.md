# Root verification of the frozen collision addendum

The 58 new declarations in `collision_theorem_index.json` are implemented and verified. The root compared the implemented Matrix probability and expectation formulas with the frozen contract, checked the final Estimates statements and proofs, and read the independent implementation reviews of the model, sorting, and bounds. The reviews request no mathematical or assumption correction.

The model has the prescribed integer column counts and their sum identities as data. It constructs uniform finite column laws, their independent product, and the actual sorted deck. The prefix probability, expected occupancy, and falling-factorial collision formulas are proved outputs. No model field assumes one of those identities or a concentration estimate.

The final bounds include all deck sizes:

```
E[collision pairs] = choose(N,2) * prefixPairFactor * tailCollisionFactor
E[collision pairs] ≤ ((N−1)/(2N)) * prefixMean² * tailCollisionFactor
E[internal edges] ≤ prefixMean² * tailCollisionFactor / 2
edgeDensity ≤ prefixMean⁴ * tailCollisionFactor² / 4
edgeDensity ≤ prefixMean.
```

Natural subtraction and total real division in the tight coefficient have the frozen conventions. The zero- and one-row cases are proved before any nonzero-denominator cancellation. Prefix/tail factorization covers empty index sets. Zero piles, equal and unequal requested digits, overlapping label pairs, and both orientations of reordered collision pairs are explicit. Sorting acts on distinct original labels, permitting repeated row words.

`verify_collision.py` passed the exact 58-statement inventory, frozen source/contract/review hashes, full addendum build, compiled signature extraction, and logical dependency checks for all theorems and eight principal constructors. `verify.py` independently passed the original 33-statement inventory and the full default project build after importing the addendum. The only reported logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`. Both verification JSON files record the actual compiler, timestamps, and source hashes.

This raises the verified finite theorem count to 91. It completes the unconditional fixed-column collision dependency and the finite probability content behind the small-singleton/terminal routes. It does not certify the logarithmic exponent conversion, entropy-weighted stable-class summation, endpoint smoothing, stable localization/cardinality, large-block bound, or exploration preservation. The printed stronger small non-singleton statement remains distinct from the proved collision estimate. No source file or old frozen statement was changed.

The next selected work is the separately reviewed occupancy-conditioned estimate from the source's internal-edge paragraph. Its signatures must be fixed under a new additive freeze before implementation; it was expressly excluded from this completed collision contract.
