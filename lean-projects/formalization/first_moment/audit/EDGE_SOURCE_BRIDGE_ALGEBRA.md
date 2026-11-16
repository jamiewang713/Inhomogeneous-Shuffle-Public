# EdgeLocalization to actual source exponents: algebra reconstruction

This is a pre-freeze reconstruction only. No Lean declaration, model hypothesis, or frozen file has been changed. The authorized TeX's ambient definition and tail exponent are at lines 490–516, with the fixed-column row model described at lines 448–468. The inspected Lean inputs are the literal EdgeLocalization collision/exponent definitions and the already proved `StableNumericalBridge`.

## Verdict and intended scope

One new definition, the proposed `prefixVector`, suffices. All proposed word, legality, cL, mean, ambient-error, column-psi, and cE identities are valid for the literal array `(asCuts D).count`. They require only the stated legality/prefix data; several identities need no ambient-prefix premise at all. No stochastic-law equality is needed for these finite identities, and none is established by them.

The most useful minimal set of public conclusions is: prefix word, legal prefix, coordinatewise ambient restriction, cL equality, prefix mean to TimeProfile mass, prefix mean to actual expected cylinder count, ambient error to the continuing vector's TimeProfile mass, column psi, and tail cE. The elementary digit, probability, proof-irrelevance, and finite-reindexing facts can remain proof-local. This is a proposed decomposition for later exact statement review, not a frozen catalog.

## The one new definition and canonical data

For implicit `D : Riffle.Model`, actual word x and proof `hx : Riffle.Legal D x`, set

`prefixVector x hx : Fin x.length → Fin D.k`

to exactly

`fun t => legalVector x hx (Fin.castLE hx.1 t)`.

Here `hx.1 : x.length≤D.K`. No new word encoding or extra zero padding is introduced. The full vector is the already frozen `legalVector`; the restriction keeps precisely its actual word coordinates.

Throughout write `n := (asCuts D).count`, so by the frozen definition

`n j l = D.n j.val l.val`.

The column-total proof needed by later EdgeLocalization estimates is already `(asCuts D).sum_count`. The bounds `N≥2` and `k≥2` come from `D.one_lt_N` and `D.two_le_k`. They are not new premises to these model adapters.

For every `t : Fin x.length`, the proof-local digit identity is

`(prefixVector x hx t).val = Riffle.digit x t.val`.

It follows directly from `legalVector_digit` because the cast preserves t.val and t.isLt supplies the required strict bound. The padding branch of `legalVector` is never used by this restriction.

## Literal word, legality, and ambient coordinate restriction

**Prefix word.** With only x and hx,

`EdgeLocalization.prefixWord (prefixVector x hx) = x`.

`prefixWord` is `List.ofFn` of the digit values. Its length is x.length. At every valid position the preceding digit identity and `Riffle.digit`'s definition identify its entry with the entry of x. `List.ext_getElem` (or the corresponding ofFn identity) proves literal list equality, not merely equality of cylinder events. Empty x and full-length x are included.

**Legal prefix.** Again with only x and hx,

`EdgeLocalization.legalPrefix n hx.1 (prefixVector x hx)`.

For t, unfold n and use the digit identity. The target is exactly

`0 < D.n t.val (Riffle.digit x t.val)`,

which is the second component of `hx.2 t.val t.isLt`. There is no need to derive a real-probability inequality and cast back to natural counts.

**Ambient restriction.** For `A : Riffle.Setup D`, x, hx, and the sole extra premise `hAx : A.w <+: x`, let a=A.w.length. Then for every `t : Fin a`,

`prefixVector x hx (Fin.castLE hAx.length_le t)`
`  = prefixVector A.w A.w_legal t`.

Apply `Fin.ext`. The two value identities reduce this to equality of the two list digits. The already proved `Riffle.digit_prefix hAx t.isLt` gives that equality, in the appropriate direction. In particular, the actual canonical ambient vector is used on the right; no arbitrary independently selected representation of A.w is substituted.

No separate `a≤x.length` or legality proof for A.w is necessary: the first is derived from hAx and the second is already `A.w_legal`. Compositions of `Fin.castLE` carry the same natural value. Different proofs of the same length inequality are proposition proofs and hence interchangeable by proof irrelevance; they need no new mathematical premise.

An optional generic version for arbitrary u prefixing a legal x would derive legality of u by `Riffle.legal_prefix hx hux`. The ambient-specialized version already suffices for the proposed integration and avoids an unnecessary extra public statement.

## Exact ambient-size exponent

For A, any legal x, and hx, the minimal identity is

`EdgeLocalization.ambientSizeExponent D.N n hx.1 A.w.length A.b (prefixVector x hx)`
`  = Riffle.cL A x`.

**No premise that A.w prefixes x is needed for this identity.** Both definitions are total finite sums of the same digits over the same interval, whether or not the word is a descendant. The actual source application will of course use a descendant when invoking density or mean-extension theorems.

Reindex the EdgeLocalization finite set

`{t : Fin x.length | A.w.length≤t.val}`

by `t↦t.val` onto `Finset.Ico A.w.length x.length`. This map is injective by `Fin.ext`. For surjectivity, i in the Ico interval has `i<x.length`, which constructs its `Fin x.length` preimage. The summands agree because n is the literal count array and `prefixVector` has the literal list digit. After the reindexing, both sides are

`A.b - (sum_(A.w.length≤i<x.length) log(D.N/D.n i (digit x i)))/log D.N`.

The existing `cL_prefix_eq A x hx x List.prefix_rfl` then gives the exact TimeProfile counterpart

`Riffle.cL A x = TimeProfile.cL D.N (asProfile D) (legalVector x hx)`
`  A.b A.w.length x.length`.

The interval may be empty: if A.w.length>x.length, both sums are empty and the identity still holds. There is no approximate replacement of A.b, no logarithmic mean error in this identity, and no loss term. The source's one-based interval `M_w<j≤M_x` is exactly this zero-based interval `[M_w,M_x)`.

## Prefix mean, actual expected mass, and ambient error

For any `j : Fin D.K` and `l : Fin D.k`, the proof-local probability identity is

`EdgeLocalization.singleFactor D.N (n j) l = TimeProfile.prob (asProfile D j) l`.

Both sides reduce to `(D.n j.val l.val : Real)/(D.N : Real)` using `asCuts`, `asProfile`, `Cuts.profile_prob`, and `singleFactor`. No positive-pile premise is needed for this equality; zero coordinates also agree.

For only x and hx, the first useful mean identity is

`EdgeLocalization.prefixMean D.N n hx.1 (prefixVector x hx)`
`  = TimeProfile.prefixMass D.N (asProfile D) (legalVector x hx) x.length`.

Both definitions have the external factor `(D.N : Real)`. Reindex the product over `Fin x.length` by `Fin.castLE hx.1` onto `TimeProfile.positions D.K 0 x.length`. This is injective by equality of values; for a position j in that set, its bound `j.val<x.length` gives the inverse finite coordinate. Products' summands agree by the preceding probability identity and the literal restriction in `prefixVector`. This proof uses no logarithm law, no approximation, and no sampling independence premise.

The existing `expectedCount_cylinder_eq x hx x List.prefix_rfl` identifies the right side with the actual expected cylinder count, giving the second useful identity

`EdgeLocalization.prefixMean D.N n hx.1 (prefixVector x hx)`
`  = (Riffle.expectedCount D (Riffle.Cylinder D x) : Real)`.

This use is justified by the already proved stable numerical bridge. An additional equality of two random sample laws is not required in this argument. It is an equality of the inspected deterministic mean expressions, and its expected-count interpretation has an existing proof.

Taking x=A.w and hx=A.w_legal gives the actual ambient mean without any continuation word. If a continuation x with hx and hAx is present, apply the second identity at A.w and then the existing

`expectedCount_cylinder_eq x hx A.w hAx`

to obtain

`EdgeLocalization.prefixMean D.N n A.w_legal.1 (prefixVector A.w A.w_legal)`
`  = TimeProfile.prefixMass D.N (asProfile D) (legalVector x hx) A.w.length`.

This route avoids a second proof that the product mass depends only on the shared prefix. It is also possible to prove that fact directly using product congruence and prefix digits, but no extra public lemma is necessary.

Consequently, for A,x,hx,hAx, unfolding `ambientMeanError` gives

`EdgeLocalization.ambientMeanError D.N n A.w_legal.1`
`  (prefixVector A.w A.w_legal) A.b`
` = log(TimeProfile.prefixMass D.N (asProfile D) (legalVector x hx) A.w.length)`
`     / log(D.N) - A.b`.

The canonical bound `A.w_legal.1` can be replaced by `hAx.length_le.trans hx.1` in an application because these are proofs of the same proposition. The latter is the proof term produced by EdgeLocalization's mean-extension and density theorems. No vector changes when that proof changes.

A direct expected-count version of this equality needs only A and has right side

`log((Riffle.expectedCount D (Riffle.Cylinder D A.w) : Real))/log(D.N)-A.b`.

It can be kept proof-local, since it follows by unfolding the definition and the general prefix-mean identity. For the eventual source application, `AmbientApproximation` then gives the absolute bound on this error and hence its upper bound eb. There is no claim that the signed error is zero or nonnegative.

**Normalization warning:** EdgeLocalization's `prefixMass` is the probability product, while TimeProfile's `prefixMass` already includes the factor N. The correct equality uses EdgeLocalization's `prefixMean`. Equating the two `prefixMass` definitions would be false by a factor N. For the empty prefix the probability product is 1 and both mean expressions are N. With ambient b=1 the existing `ambientMeanError_root` gives error exactly zero.

## Column psi and the tail exponent

For D and every `j : Fin D.K`, with no word or setup premise,

`EdgeLocalization.columnPsiTwo D.N (n j) = TimeProfile.psi (asProfile D j) 2`.

Unfold both definitions and `TimeProfile.powerSum`. Rewrite `singleFactor` to the profile probability. EdgeLocalization takes its natural square, whereas the source's psi takes real power at exponent 2. The trusted natural-exponent specialization of real power (`Real.rpow_natCast`, with the numeral cast normalized) identifies these exactly, including a zero probability. Both sides then take the negative logarithm of the same finite sum. No logarithm quotient rule or assertion of positivity of every summand is involved.

For D and **every natural M**, again with no word, setup, or `M≤D.K` premise,

`EdgeLocalization.tailEdgeExponent D.N n M = TimeProfile.cE D.N (asProfile D) M`.

The two finite supports agree:

`{j : Fin D.K | M≤j.val}`
`  = TimeProfile.positions D.K M D.K`.

The extra upper bound `j.val<D.K` on the right is already `j.isLt`. Filter extensionality proves support equality, and the preceding column identity proves equality of every summand. The common denominator is `Real.log D.N = logScale D.N`; the outer sign also agrees.

If M=D.K or M>D.K, both supports are empty, so both exponents are exactly zero. This is why a length-upper-bound premise must not be added to this identity. K=0 is also covered. There is no `Riffle.cE` declaration to target in the current stable-block model: the exact existing destination is `TimeProfile.cE`.

The existing `tailSquareFactor_eq_rpow_tailEdgeExponent` and this new equality will subsequently give the exact square-product identity `tailSquareFactor=N^cE`, using only the model's column totals and N≥2. By contrast, the actual fixed-count two-row `tailCollisionFactor` is only bounded above by that quantity. It is generally not equal and must not be identified with `N^cE` in a later proof.

## Minimal dependency structure and edge cases

The proof order can be:

1. Define the canonical restriction; derive its digit equality locally.
2. Prove the literal word, natural-count legality, and ambient coordinate restriction.
3. Reindex the finite cL sum and invoke the existing source cL bridge when needed.
4. Identify the elementary probabilities, reindex the prefix product, and use the existing expected-cylinder equality. Deduce the continuing-vector ambient-error identity.
5. Identify column psi and the two tail supports, proving cE equality for arbitrary M.

All required nonnegativity, alphabet bounds, and positive logarithmic scale are already supplied by Model, Legal, or Setup. The basic equality layer needs no horizon relation `K=floor(T log N)`, no AlmostLike assumption, no partition, no variational margin, no boundary admissibility or Gamma membership, and no ambient approximation. Those enter later source applications, not the identities.

Zero piles outside a legal prefix are permitted. Legality supplies positive counts only where the mean-extension theorems need them. The mean and cL identities themselves are proved by equal finite expressions, so no unproved use of `exp(log 0)` is hidden in their proofs. Empty words, full words, ambient words longer than x in the cL identity, and tail lengths beyond K are treated explicitly above.

The list identity identifies the prefix argument passed to EdgeLocalization's density. It does **not** identify `matrixLaw`, sorted-row rank labels, or graph events with any other graph-law representation. A separate law/graph bridge would still be required if the final first-moment theorem is phrased in a different representation. No such equality is assumed here.

## Read implementation hashes

```
Collision/Model.lean       43c19b97e925dee9186d496560cdf143c89b76279ba4f36420e84401a4b4e3dd
Exponent/Model.lean        db39dbcc02675a03461380ce8afdbc2c798268285ceb52e9f2401fbd55869106
Exponent/Mean.lean         81990e2b66d7904b76e1a50ee29e4bd77e02380db81520c9a0a36542c482c968
Exponent/Tail.lean         d90467dc983d54befe7a75ec2e09cc147b0caf96f2311720e166324153fdf24d
StableNumericalBridge.lean a1485441183054eba94a887919725e6da0bba49f549500a540c24526d4b3de7f
```

No mathematical obstruction was found in this finite adapter batch. Exact exported names, proof arguments, and theorem statements remain for the subsequent shared statement review and freeze.
