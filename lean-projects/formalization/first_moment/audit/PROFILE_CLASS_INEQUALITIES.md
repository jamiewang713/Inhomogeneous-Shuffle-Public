# Actual profile classes: independent adversarial review

Reviewer: `inequality_audit`. Decision: **approve all six definitions and P1–P4 exactly as proposed**. This is the pre-implementation mathematical and interface review. It does not claim that the new declarations have already been implemented or compiled.

Reviewed `PROFILE_CLASS_CONTRACT.md` SHA-256:
`615b9396951f5ac23f83ddb68f0506cc0d75597d86e64bdaa3b3f1403bf3e149`.
The earlier frozen contracts remain at:

- `MODEL_BRIDGE_CONTRACT.md`:
  `7d04c06ab51c086bf97d60e3b52caac9b798cdb07b7b0cb5b99ea7a78042cbc5`.
- `FROZEN_CONTRACT.md`:
  `5ba1c21dc9933186ebff72f9c502b286d15787db29d6d62961a9ea8bfe866f0b`.

No contract or Lean implementation was changed by this review.

## Source and domain comparison

The active TeX definition `def:space-time-digit-profile` uses positions
strictly after the longer boundary word and through the stable word's
final digit. Its one-based range translates exactly to
`[(Riffle.join y z).length, x.length)` in zero-based indices. The proposed
`exceptionalPositions` and `goodDigitCount` use this range, not the larger
range after the ambient prefix. Thus digits between the ambient prefix and
the boundary join remain part of the fixed boundary data.

The source profile lists good-digit counts and exceptional locations.
The first-moment proof later explicitly says that exceptional digit values
have also been included in the class count. The proposed key implements
that refinement literally. The stored length and routing value are further
finite refinements; they cannot invalidate an upper bound on the number
of source classes. A refinement must be counted with its full cost, which
the frozen `profileCountBound` does.

The source specialization must use a cell map encoding both the time-cell
and simplex-cell indices. Its good predicate must be the representative
probability test at the recorded position. Requiring digit validity in
that specialized predicate does not change it on legal source words.

The domain contains the exact existing admissible-pair predicate, stable
membership, and the real exceptional cutoff. No legality, retention,
nonterminal, or finiteness field is added. The necessary legality and
prefix relation follow from:

- `Riffle.admissiblePair_rawPair`;
- `Riffle.stable_desc`.

The already proved `Riffle.admissiblePair_retained` supplies retention when
comparing this domain to the source terminology. It is not an additional
assumption. Nonterminal terminal-fallback words have not been silently
removed; that removal requires the later numerical argument.

## Exact theorem-interface review

| Interface | Adversarial check |
| --- | --- |
| P1 `profileWord_exceptional_budget` | The subtype gives `(q : ℝ) ≤ alpha * log N`. Since `q` is natural, `Nat.le_floor` gives the stated bound directly. No sign hypothesis on `alpha` is needed. |
| P2 `goodDigitCount_le` | The counted set is a subset of `Fin K`; its cardinality is at most K for all raw words. No legality or length assumption is needed. |
| P3 `encodeProfile_eq_data` | Boundary-code equality recovers the two words using the proved boundary injections. The other projections recover the length, all flattened counts, the exceptional support, the actual labels on that support, and the route. The count flattening is a genuine equivalence `Fin c × Fin k ≃ Fin (c*k)`. Equality of labeled sparse assignments gives digit equality after transport along support equality. No stable-word equality or exact `cL` equality follows or is claimed. |
| P4 `profileClass_card_le` | The class type is the range subtype of the concrete encoder in an already finite `ProfileKey`. Its value map is injective, hence its cardinality is at most the target cardinality. This uses no finiteness premise on `ProfileWord`. The target cardinality is exactly the previously frozen formula with `d=c*k`. |

The exact count is

`4*(k+1)^2*(K+1)^(c*k+3)*(sparseCount K k qb)^2*(sparseCount K k qe)`.

The two boundary-code lengths and the stable-word length account for the
three additional powers of `K+1`. The two boundary tags account for
`(k+1)^2`; the route accounts for 4; both boundary sparse assignments and
the exceptional sparse assignment retain their value factors.

This is a bound on realized descriptors. It does not assert that all
stable words inject into this finite key, and it does not count the number
of words inside a single descriptor fiber. That separate entropy bound is
not among P1–P4.

## Negative cutoff and degenerate cases

The contract correctly keeps the real inequality in `ProfileWord`.
Replacing it by the derived floor inequality would change the domain for
negative alpha: `alpha*log N < 0` makes the original domain empty, whereas
`q ≤ Nat.floor (alpha*log N) = 0` permits zero-exception words. The proposed
contract avoids this error and needs no `alpha ≥ 0` hypothesis.

Other cases are covered without additional premises:

- If `K=0`, all legal words and extension supports are empty.
- If `x=join y z`, every good count and the exceptional support are empty.
  This includes the source singleton classes.
- If `c=0`, a supplied map `Fin K → Fin 0` already forces `K=0`. The finite
  counting statement does not need a separate `c>0` hypothesis.
- Empty cells produce zero counts.
- If no extension digit is good, the exceptional assignment records the
  entire extension and its values.
- Budgets exceeding K are harmless: the frozen sparse count already
  includes only zero binomial terms beyond K.
- Arbitrary raw words can have lengths greater than K in P2; its filtered
  support still has cardinality at most K. Actual domain words are legal,
  so this does not truncate any source position in the encoder.
- Zero piles cause no invalid stored digit: actual domain words are legal.
- Arbitrary keys need not have preimages; `ProfileClass` uses exactly the
  realized range, not every syntactically possible key.

## Universal deterministic data and later limits

For this finite theorem, arbitrary fixed `cell`, `good`, and `route` are
legitimate universally quantified data. The proof does not need cell
regularity, time measurability, probability identities, or convergence.
An arbitrary route divides the realized descriptors into at most four
categories; it does not prove any density estimate for those categories.

The later source application must instantiate these data with the actual
time/simplex cells, representative threshold, and desired density routing.
The eventual `N^epsilon` conclusion also needs a fixed cell count before
N tends to infinity, together with the previously specified small-budget
parameter choices. P1–P4 do not claim that asymptotic conclusion for an
arbitrary cell count growing with N.

## Exact quantities within a class

For the actual source specialization, equal keys fix the boundary pair,
stable-word length, all good counts, and every exceptional position and
value. Consequently they fix:

- the source entropy H and representative cost S;
- the exact exceptional cost Q;
- the boundary quantities `cF` and `cL(join y z)`;
- the source tail cost `cE`, which depends only on the stable-word length
  and the fixed pile environment.

They do **not** generally fix exact `cL(x)`. Actual pile probabilities can
vary between positions within one coarse cell, and permuting good digits
between those positions changes the actual product mass while preserving
all stored counts.

Here is a concrete example in the universally quantified deterministic
setting of this contract. Take

- `N=1000`, `K=3`, `k=3`;
- successive pile-count vectors `(300,400,300)`, `(401,399,200)`, and
  `(399,401,200)`;
- the empty ambient prefix, `b=1`, `chi=1/20`, `C=1`, `delta=1/100`;
- `y=z=[1]`, one cell, an everywhere-true good predicate, `alpha=0`, and
  constant route.

Both boundaries are admissible genuine first-column crossings: their
outward supports are empty, and the left and right large-pile indices are
0 and 2. Their common fluctuation exponent is

`F = log(300)/(2*log(1000)) = 0.4128535424...`.

The join has `cL=log(400)/log(1000)=0.8673533304...`, so it has not stopped.
Consider the distinct legal words

`x_plus=[1,0,1]` and `x_minus=[1,1,0]`.

Their exact size exponents are

`cL(x_plus)=log(400*401^2/1000^2)/log(1000)=0.6027829121...`,

`cL(x_minus)=log(400*399^2/1000^2)/log(1000)=0.6013352609...`.

Both exceed `F+delta=0.4228535424...`; since both have length K, they are
members of the nonterminal fallback set and hence of `Stable A y z`.
Their good counts are one 0 and one 1, their exceptional supports are
empty, and every other key field agrees. Their `cL` values differ by the
strictly positive quantity

`2*log(401/399)/log(1000)`.

Thus neither word injectivity nor exact `cL` constancy can be appended to
P3. The numerical values above were independently evaluated; the formulas
and the large strict margins establish the counterexample. No such false
conclusion occurs in the proposed contract.

## Sign-off

All six definitions and P1–P4 preserve the requested actual model domain
and the earlier frozen interfaces. The real cutoff, labeled exceptional
support, pair reconstruction, arbitrary deterministic routing, and
realized-range class definition address the identified failure modes.
No correction or additional model hypothesis is required before freeze.
