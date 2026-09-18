# Actual profile-fibre entropy: independent adversarial review

Reviewer: `inequality_audit`. Decision: **approve both definitions and
PF1–PF4 exactly as proposed in `PROFILE_FIBRE_CONTRACT.md`**. No correction
or additional hypothesis is needed.

Reviewed exact-contract SHA-256:
`a90fa7f7a0679465139c1c74be4ec9237a01dc6fde3c012a85dd513732622727`.

The preliminary statement candidate, actual `ProfileClasses.lean`, and
the already proved `Entropy.lean` interfaces were inspected. The source
was reread at `def:space-time-digit-profile` and the first-moment passage
asserting the within-class entropy bound and inclusion of exceptional
digit values. No implementation, freeze, or earlier contract was changed.

## Exact-interface checks

**Definition 1.** `profileKeyCounts` is the inverse-coordinate reading of
the existing count vector. The forward `finProdFinEquiv (a,l)` here is
consistent with the inverse equivalence used when encoding counts. It
does not change the key, normalize counts, or add compatibility data.
Its arbitrary natural parameters require no positive-alphabet premise.

**Definition 2.** `ProfileFibre` is exactly the fibre of the concrete
encoder on the already frozen actual domain. It retains the real
exceptional cutoff, admissible boundary pair, and stable membership. It
does not replace the cutoff with its natural-floor consequence or add
legality, retention, finiteness, or routing correctness as a premise.

**PF1.** Function equality with the actual good counts follows directly
from the finite-product equivalence's inverse identity. It gives each
cell/digit count, not merely the total number of positions.

**PF2.** Actual fibre finiteness is a genuine derived proposition. In the
nonempty case, the restriction to the common finite good-position set is
injective into a finite word type. In the empty case finiteness is direct.
There is no need for a finite-domain assumption or an unproved choice of
a finite enumeration of all stable words.

**PF3.** The stated exact bound follows from an injection into the existing
type-class subtype and the proved `type_class_card_le_exp_entropy`.
Exceptional locations and values are fixed before this injection, so no
exceptional-label factor is charged a second time. The only alphabet
positivity used by the existing theorem follows from `D.two_le_k`.

**PF4.** The real-power conversion is exact for every real H:

`N^(H/log N) = exp(log N * (H/log N)) = exp(H)`.

`D.one_lt_N` supplies `N>0` and `log N != 0`. No nonnegative-entropy,
positive-alpha, or separately assumed logarithm condition is needed.

## Reconstruction within a fibre

For a nonempty fibre choose one witness internally, with boundary words
`y0,z0`, stable word `x0`, join length v, stable length M, and exceptional
support Q. Any other fibre element has the same key. The proved
`encodeProfile_eq_data` therefore gives:

- the same two actual boundary words, not merely their lengths;
- the same stable length M;
- the same natural good counts;
- the same exceptional support Q and the same digit at every position
  in Q.

The common free set is exactly

`J = { i : Fin K | v <= i.val and i.val < M and i not in Q }`.

For every fibre word, stable membership and the existing admissible-pair
theorem imply legal membership in `Desc D (join y0 z0)`. Thus all words
share the entire prefix before v and have legal digits at every position
below M. The three pieces determining a word are consequently disjoint
and exhaustive:

1. its fixed boundary-join prefix;
2. the fixed exceptional labels;
3. its digits on J.

Equal restrictions on J therefore imply equal full stable lists, using
the common length. Together with equality of the boundary words, this
gives equality of the original triples and then of the subtype elements.
Proof fields do not create multiplicity, by subtype extensionality.

This injection is restricted to one fibre. The construction does not
contradict the earlier counterexample of distinct words with equal full
profile keys; those words have different restrictions on J.

## The digit-dependent good predicate is harmless

There is no requirement that `good i a` depend only on i, on the cell, or
on the digit independently of i. For a given fibre word and an index in
its extension range, Q membership is exactly the negation of goodness
for that word's own digit. Equality of Q between fibre words therefore
implies that J is the good-position set for every word, even though the
allowed digits at an individual free position can differ from the allowed
digits at another position.

The restricted words are mapped into the full type class with the stored
counts. That type class may contain additional digit arrangements which
violate the original position-specific good predicate, stable membership,
or routing. This only enlarges the target of the injection and is valid
for an upper bound. A surjection onto the full type class is not needed
and would generally be false.

The bijection from `Fin J.card` to J preserves the inherited cell label.
Consequently its per-cell/per-digit count equals the actual
`goodDigitCount`, and PF1 identifies that count with the stored key.
There is no unproved empirical-count compatibility hypothesis.

## Unrealized keys, empty sets, and other adversarial cases

- For an unrealized key, the fibre is empty. Stored counts, sparse
  supports, boundary codes, or routing data can be mutually incompatible;
  no consistency premise is required. Cardinal zero is bounded by the
  strictly positive exponential of its arbitrary stored entropy.
- For a realized key, there are no spurious exceptional positions outside
  the extension: equality with an actual encoded support forbids them.
- If J is empty and the key is realized, every good count is zero, the
  entropy is zero, and at most one word remains after fixing the prefix
  and exceptional labels. An empty *unrealized* fibre need not have zero
  stored entropy; PF3 correctly uses only exponential positivity there.
- Terminal singleton words and empty continuations fall under that
  realized-empty-J case without a separate singleton assumption.
- If alpha is negative, the original real cutoff makes the actual domain
  empty because `log N>0`. PF2–PF4 still hold; the floor is not used to
  enlarge the domain.
- `K=0`, `c=0`, zero counts, and unused cells require no hidden
  nonemptiness hypotheses. A supplied `Fin K -> Fin 0` already rules out
  nonzero K when c is zero.
- A route may distinguish words even when their other data agree. Fixing
  it only makes the fibre smaller; no density-case correctness assumption
  is needed for the entropy estimate.
- The finite-key count-vector coordinates are bounded by K. PF3 does not
  infer that arbitrary stored counts sum to the number of free positions;
  that fact is available only from a witness in the nonempty branch.

## Exact source normalization

Let `L=log N>0`, let n be the natural counts, and let
`nTot(a)=sum_l n(a,l)`. For a positive cell total, the source expression is

`(nTot/L) * sum_{l:n_l>0} (n_l/nTot) * log(nTot/n_l)`

`= (nTot*log nTot - sum_l n_l*log n_l)/L`.

Zero-count terms vanish, and a cell with total zero contributes zero on
both sides. Summing over cells gives exactly

`H_source = typeEntropy(n)/log N`.

Thus the proposed exponent is the correct normalized entropy, with no
asymptotic term. The source's exceptional labels are already fixed by the
key and are not part of this free-word entropy. Counting all K positions
with padding under the unchanged stored counts would generally be wrong;
the proposed application on exactly J avoids that mistake.

The contract correctly leaves the concrete cross-package identification
with `TimeProfile.profileH` for a later proved bridge. The present theorem
does not hypothesize that identification, make exact `cL` constant, or
assert any edge-density or localization estimate. Those probabilistic
issues, including the counterexamples in the separate large-block audit,
do not invalidate this deterministic fibre count.

## Sign-off

Both definitions and PF1–PF4 are mathematically valid with exactly the
stated existing model and deterministic data. The suggested proof avoids
the unsafe changes tested above. It may be frozen as proposed; no code or
freeze operation was performed by this reviewer.
