# Independent reconstruction of the actual profile-class map

## Exact proposed-contract sign-off

Decision: **APPROVE the exact proposed `PROFILE_CLASS_CONTRACT.md`, all six
definitions and P1–P4, with no correction or additional assumption.**

Reviewed proposed-document SHA-256:
`615b9396951f5ac23f83ddb68f0506cc0d75597d86e64bdaa3b3f1403bf3e149`.

The exact-document review confirms:

- Definitions 1–2 use precisely the extension after `join y z`, not the
  ambient extension, and P2 needs no legality or length assumption because
  its finite set is a subset of `Fin D.K`.
- Definitions 3–4 preserve the original real exceptional cutoff in the
  source subtype. P1 only derives the natural-floor consequence. In
  particular, negative alpha does not introduce spurious words with empty
  exceptional support.
- Definition 5 stores the two proved boundary encodings, actual length,
  exactly `c*D.k` natural count coordinates using the stated standard finite
  product equivalence, the exact labeled exceptional support, and one of
  four routing values. All required range and budget facts follow from the
  source subtype and existing theorems.
- Definition 6 takes the actual range subtype. It neither identifies
  arbitrary unrealized keys with actual classes nor claims injectivity of
  individual stable words.
- P3's seven conclusions follow from equality of the seven corresponding
  pieces of data, using boundary injectivity and equality of the dependent
  sparse assignments. In particular, the digit-equality conclusion concerns
  the actual exceptional digits, not just the support cardinality. The
  theorem correctly makes no exact-cL or stable-word-equality claim.
- P4 is precisely the frozen `profileCountBound` with
  `qb=boundaryBudget A`, `qe=exceptionalBudget A alpha`, and `d=c*D.k`.
  Finiteness of the range subtype follows from the finite code type; no
  finite-domain premise is necessary.
- The source-specialization paragraph correctly treats cell/good/route as
  deterministic data requiring the indicated source instantiation. The
  valid-digit clause in source `good` is automatic on every encoded legal
  digit. The contract explicitly leaves within-class entropy and density
  routing validation to their separate proofs.

All previously checked edge cases remain covered by these exact interfaces.
No code or existing frozen contract was changed during this review.

## Independent reconstruction

This is a pre-implementation mathematical audit. No existing contract or Lean
file is changed. The source is the authorized article's
`def:space-time-digit-profile` (699–746), exceptional truncation/counting proof
(1094–1118), and final class grouping (1870–1877), together with the already
proved stable-block and boundary-encoding interfaces.

## Candidate data and source domain

Fix the existing `D : Riffle.Model` and `A : Riffle.Setup D`, and deterministic
data

```
c : Nat,
cell : Fin D.K -> Fin c,
good : Fin D.K -> Nat -> Prop,
alpha : Real.
```

The abstract joint-cell labels are instantiated in the paper by the pair
of time-cell and simplex-partition indices. Thus the source instance has
`c = R*(m+1)`. The source good predicate is exactly the representative-digit
condition `p_l^(i(j)) > 2 chi`. The finite counting argument itself is valid
for arbitrary `cell` and `good`; no probabilistic or regularity premise is
needed for this deterministic construction. Matching these data to the source
definitions remains an explicit instantiation step.

For a triple `(y,z,x)`, put `v = Riffle.join y z` and define its exceptional
support by

```
E(y,z,x) = {i : Fin D.K |
  v.length <= i.val and i.val < x.length and
  not good i (Riffle.digit x i.val)}.
```

The domain is exactly the subtype of triples satisfying

```
Riffle.AdmissiblePair A y z,
x in Riffle.Stable A y z,
(E(y,z,x).card : Real) <= alpha * Real.log (D.N : Real).
```

The source truncation is `R_x <= alpha`, where `R_x = #E/log N`.
These formulations are equivalent because `D.one_lt_N` gives `log N > 0`.
No replacement stochastic assumption is being introduced.

`admissiblePair_rawPair` followed by `stable_desc` gives legality of x and
`v <+: x`; hence `v.length <= x.length <= D.K` and every used digit is below
`D.k`. Also `admissiblePair_retained` shows that every such pair is already
retained. A separate retention premise is unnecessary.

Set

```
qb = boundaryBudget A,
qe = Nat.floor (alpha * Real.log (D.N : Real)).
```

`Nat.le_floor` applied directly to the exceptional-support premise yields
`E.card <= qe`. No independent natural budget or alpha-positivity premise
is needed for this finite theorem.

## Good-digit counts and key

For `a : Fin c` and `l : Fin D.k`, the unnormalized natural count is

```
n(a,l) = #{i : Fin D.K |
  v.length <= i.val and i.val < x.length and
  cell i = a and Riffle.digit x i.val = l.val and
  good i (Riffle.digit x i.val)}.
```

Each count is at most D.K, as it counts a subset of `Fin D.K`. It therefore
gives an element of `Fin (D.K+1)`. Flatten `(a,l)` using one fixed equivalence
between `Fin c x Fin D.k` and `Fin (c*D.k)`. The frozen count-vector dimension
is exactly `d = c*D.k`, with no omitted coordinate or extra count coordinate.

The concrete key in

```
ProfileKey D.K D.k qb qe (c*D.k)
```

contains, in the frozen order:

1. `encodeBoundary A .left y`;
2. `encodeBoundary A .right z`;
3. the actual length of x in `Fin (D.K+1)`;
4. the flattened vector of natural counts above;
5. the sparse assignment with support E and value `digit x i` at each i;
6. a deterministic route value in `Fin 4`.

Legality of x supplies the sparse labels in `Fin D.k`. The floor-budget
argument supplies the cardinality proof for the sparse assignment.

The route may be supplied as a function on the domain or on word triples;
either choice is only deterministic data and introduces no mathematical
hypothesis. Its agreement with particular density cases is a separate
instantiation fact. In particular, the counting theorem must still allow
nonterminal terminal-fallback blocks in `Stable`; their later exclusion by
the first-moment margin is not a premise of this construction.

## Actual classes and exact finite bound

Define actual classes as the range subtype of this concrete key map, or
equivalently as the quotient of its source domain by equality of keys.
Using the range subtype avoids choosing representatives and does not require
any pre-existing finiteness instance for the source domain.

The class subtype injects into the frozen `ProfileKey` by its value map.
Consequently its natural cardinality is at most

```
profileCountBound D.K D.k qb qe (c*D.k)
 = 4*(D.k+1)^2*(D.K+1)^(c*D.k+3)
     * (sparseCount D.K D.k qb)^2
     * (sparseCount D.K D.k qe).
```

Here the square applies to the boundary sparse-count factor, as in the frozen
definition: `(sparseCount D.K D.k qb)^2`. The two actual boundary encodings
are already proved injective. No injectivity claim about individual stable
words is valid or needed: good-digit rearrangements intentionally belong to
the same profile class.

Equality of keys fixes both boundary words, the extension length, every good
count, all exceptional positions and digit values, and the chosen route.
For the source data this fixes the normalized counts, s and u, H, S, and the
exact exceptional cost Q. The exact cL can still vary within a class, because
actual column masses vary inside a representative cell. Recording the route
allows a case refinement without asserting that cL is constant.

## Exact correspondence and refinement

The zero-based interval `[v.length,x.length)` is exactly the paper's one-based
condition `s log N < j <= u log N`. It must not be replaced by the longer
ambient interval `[A.w.length,x.length)`.

The paper's normalized good counts are `n(a,l)/log N`. With N fixed and
`log N > 0`, equality of these normalized values is equivalent to equality
of the stored natural counts.

The displayed source definition stores only the exceptional set, but the
counting and first-moment proof explicitly include exceptional digit values
(1873–1877). The proposed key is the previously reviewed genuine refinement
that records these values. They are necessary to fix the exceptional cost Q
and to recover a class word from its remaining good-position digits.

Within a fixed key, the suffix good positions are the fixed complement of E,
and their cell counts are fixed. The existing type-class entropy theorem can
therefore be applied after restricting to those positions. That within-class
entropy bridge is a separate obligation; the range-cardinality theorem alone
does not claim it has been established.

## Edge cases and proof-local obligations

- If x=v, the suffix, exceptional support, and all good counts are empty or
  zero. This includes terminal singleton profiles and terminal ambient words.
- No premise `c>0` is required. If c=0 and K>0, the supplied function
  `Fin K -> Fin 0` cannot exist. If K=0, both the function and the count vector
  are empty and the construction is valid.
- If alpha<0, the real support bound makes the domain empty because log N is
  positive. Natural floor remains a total definition. The source's actual
  alpha is positive, but that is unnecessary for the finite count theorem.
- A budget qe>K is harmless; frozen sparse counting already handles it.
- Zero piles require no extra hypothesis. Only actual legal digits are stored.
- The boundary tag/support edge cases remain handled by the proved boundary
  encodings, including genuine crossings at K and final fallback violations.
- Each good count is bounded by K using only a filtered-universe cardinality
  bound. No hidden feasibility assumption about prescribed counts is needed.
- If useful for source matching, a proof-local finite partition identity gives
  `sum_(a,l) n(a,l) + #E = x.length - v.length`; every suffix position is
  exactly good or exceptional and has one cell and one legal digit.

No mathematical obstruction or additional model hypothesis was found. The
remaining work is to freeze the exact data/definitions and range-cardinality
interfaces after independent comparison, then implement their finite
bookkeeping proofs.
