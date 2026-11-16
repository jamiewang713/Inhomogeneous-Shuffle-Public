# Actual profile fibres: statement-design candidate

This is a bounded pre-freeze proposal, not an implementation or a new freeze. It preserves the original first-moment, boundary-encoding, and profile-class contracts. The mathematical source reread for this review is the authorized unified TeX, especially `def:space-time-digit-profile` and the final first-moment proof at lines 1872–1876. Relevant project Lean and trusted mathlib interfaces were inspected. No other mathematical source was used.

The proposed bridge is valid for arbitrary keys, including keys realized by no word. It adds no finite-type, count-compatibility, regularity, sign, or probability hypothesis. Its exact bound is stronger than the source's displayed asymptotic within-class bound. Exceptional labels are fixed in the key already; their number is not charged again in this entropy bound.

## Recommended public interface

Use a new `FirstMomentModel/ProfileFibreEntropy.lean` in namespace `InhomogeneousShuffle.FirstMoment.Model`, importing the existing `FirstMomentModel.ProfileClasses` and `FirstMoment.Entropy`. I recommend exactly two definitions and four theorems. All helper position sets, enumerations, digit restrictions, injections, and entropy conversion facts can remain proof-local.

The first definition reads the existing flat count vector without modifying the key:

```lean
def profileKeyCounts {K k qb qe c : ℕ}
    (key : ProfileKey K k qb qe (c * k)) : Fin c → Fin k → ℕ :=
  fun a l => (key.2.2.2.1 (finProdFinEquiv (a, l))).val
```

The second is the actual encoder fibre, with all original domain predicates intact:

```lean
def ProfileFibre {D : Riffle.Model} {c : ℕ}
    (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4)
    (key : ProfileKey D.K D.k (boundaryBudget A)
      (exceptionalBudget A alpha) (c * D.k)) : Type :=
  {p : ProfileWord A good alpha //
    encodeProfile A cell good alpha route p = key}
```

Use the following shared binders in each theorem, without extra hypotheses:

```lean
{D : Riffle.Model} {c : ℕ}
(A : Riffle.Setup D) (cell : Fin D.K → Fin c)
(good : Fin D.K → ℕ → Prop) (alpha : ℝ)
(route : ProfileWord A good alpha → Fin 4)
```

**F1. `profileKeyCounts_encode`.** For `p : ProfileWord A good alpha`, conclude the function equality

```lean
profileKeyCounts (c := c) (encodeProfile A cell good alpha route p) =
  goodDigitCount A cell good p.val.1 p.val.2.1 p.val.2.2
```

The equality is an exact link to the actual natural counts, not an assumption identifying abstract counts with source words. The inverse identities for `finProdFinEquiv` prove it directly.

For F2–F4 add only the key data binder

```lean
(key : ProfileKey D.K D.k (boundaryBudget A)
  (exceptionalBudget A alpha) (c * D.k))
```

**F2. `profileFibre_finite`.** Conclude

```lean
Finite (ProfileFibre A cell good alpha route key)
```

This is a derived proposition, not a `Finite` premise or a new axiom. Making it public prevents the totalized `Nat.card` convention on infinite types from obscuring what the entropy bound establishes, and permits later finite sums over each fibre.

**F3. `profileFibre_card_le_exp_entropy`.** Conclude

```lean
(Nat.card (ProfileFibre A cell good alpha route key) : ℝ) ≤
  Real.exp (typeEntropy (profileKeyCounts (c := c) key))
```

**F4. `profileFibre_card_le_rpow_entropy`.** Conclude the exact normalized form

```lean
(Nat.card (ProfileFibre A cell good alpha route key) : ℝ) ≤
  (D.N : ℝ) ^
    (typeEntropy (profileKeyCounts (c := c) key) /
      Real.log (D.N : ℝ))
```

No separate normalized-entropy definition is needed. The positivity of `D.N`, of its logarithm, and the nonzero logarithm needed for cancellation all follow from `D.one_lt_N`. Likewise `0 < D.k` follows from `D.two_le_k`; it must not become a new theorem premise.

These arbitrary-key statements specialize to `key : ProfileClass A cell good alpha route` by passing `key.val`. A separate realized-class wrapper is unnecessary. If the other independent reviews prefer only realized keys, that is mathematically viable but provides a less general endpoint without simplifying the important injection argument.

## Proof structure and exact existing dependencies

The core proof splits on whether the fibre is inhabited. An empty fibre is finite and has cardinal zero; `Real.exp_pos` gives F3 without any count compatibility condition. For a nonempty fibre, fix one witness `p₀`. This witness is chosen inside the proof, not supplied as a new hypothesis.

Let `y₀,z₀,x₀` be its triple, `v = (Riffle.join y₀ z₀).length`, `M = x₀.length`, and `Q = exceptionalPositions A good y₀ z₀ x₀`. Define the proof-local finite set

```lean
J := Finset.univ.filter (fun i : Fin D.K =>
  v ≤ i.val ∧ i.val < M ∧ i ∉ Q)
```

For any two fibre elements, equality of their encoder values follows by transitivity through `key`. Apply the already proved

`InhomogeneousShuffle.FirstMoment.Model.encodeProfile_eq_data`

to recover the same two boundary words, length, actual natural counts, exceptional support, exceptional digits, and route. Thus every word has the same extension interval and the same `Q`. On that interval, membership outside `Q` is exactly goodness for that word's own digit, even though the predicate `good` may depend on the digit. Consequently `J` is precisely the good-position set for every fibre word. No independence or uniformity assumption on `good` is required.

The existing deterministic stable-word result supplies, separately for every fibre element,

```lean
Riffle.stable_desc
  (Riffle.admissiblePair_rawPair p.property.1)
  p.property.2.1
```

Its conclusion is membership in `Riffle.Desc D (Riffle.join y z)`: the stable word is legal and extends the boundary join. This gives `x.length ≤ D.K`, legal digit bounds on all positions in `J`, and the common fixed prefix before `v`.

Choose the proof-local finite reindexing

```lean
e : Fin J.card ≃ ↥J := J.equivFin.symm
```

and set `cellJ j = cell (e j).val`. Restrict the stable word's digits to `e j`, turning their natural values into `Fin D.k` using legality. A finite-set bijection shows, for every cell `a` and digit `l`, that the corresponding count of this restricted word equals `goodDigitCount` of the original word. F1 and its equality to `key` identify this with `profileKeyCounts key a l`. The restriction therefore belongs to

```lean
typeClass cellJ (profileKeyCounts (c := c) key)
```

whose domain has length `J.card`, not `D.K`. Counting padded full-length words with the existing type-class theorem would incorrectly charge fixed prefix or exceptional positions and must be avoided.

The map from the actual fibre to this type-class subtype is injective. Given equal restricted words, use the previously recovered equal lengths and split each position of the stable words into:

1. before the common boundary join: `Riffle.digit_prefix` gives the fixed prefix digit;
2. in the common exceptional support: `encodeProfile_eq_data` gives the fixed label;
3. in the remaining extension: surjectivity of `e` and equality of restrictions give the digit.

`List.ext_getElem`, after unfolding the totalized `Riffle.digit` only at positions known to be in bounds, then gives equality of stable lists. Equality of both boundaries gives equality of the original triples, and subtype extensionality gives equality of fibre elements. This proof does not assert that the full profile encoder itself is injective.

The exact finite-cardinality bridge can use `Finite.of_injective`/`Fintype.ofInjective` for F2, and `Finite.card_le_of_injective` plus `Nat.card_eq_fintype_card` and the cardinality of a finite-set subtype for F3. The final entropy estimate is the already proved

```lean
InhomogeneousShuffle.FirstMoment.type_class_card_le_exp_entropy
  (K := J.card) (k := D.k) (d := c)
  hk cellJ (profileKeyCounts (c := c) key)
```

where `hk` is derived from `D.two_le_k`. This theorem itself already handles impossible count vectors and empty or unused cells. There is no need for a new multinomial formula or a second entropy argument.

F4 is an exact rewriting of F3 using `Real.rpow_def_of_pos` and cancellation of the nonzero `Real.log (D.N : ℝ)`. Neither an asymptotic loss nor a new estimate is used.

## Source normalization and remaining integration work

If the natural counts are `n a l`, the source counts are `n a l / log N`. With `nTot a = ∑ l, n a l`, the zero-aware source entropy is exactly

`(∑ a, nTot a * log(nTot a) - ∑ l, n a l * log(n a l)) / log N`,

which is the exponent in F4. Positive count terms permit the usual logarithm-of-a-ratio identity; zero terms vanish. The logarithms of `log N` cancel because each cell total is the sum of its digit counts. There is no additional error term in this finite identity.

An explicit theorem identifying this expression with the existing `TimeProfile.profileH` still requires the concrete model-to-time-profile mapping: the joint time/simplex cell equivalence, the representative threshold predicate, the extension endpoints, and the actual digit-count equality. The existing `TimeProfile.profileH_source_formula` identifies that package's entropy with the TeX formula, but by itself does not prove this cross-package map. Such an identification must be proved as a later bridge, not hypothesized in F3 or F4. The source's one-based extension `s log N < j ≤ u log N` corresponds exactly to the existing zero-based interval `[join.length, x.length)`.

The source permits exact block costs to vary within a refined profile class. The proposed theorem does not conclude that the exact `cL`, fluctuation exponent, or individual edge contribution is constant. F3 bounds the number of words in the fibre; final assembly must still apply the numerical/edge estimate to each actual word with its own data or use a justified uniform upper bound. In particular no maximum or representative-cost equality is smuggled into the entropy bridge.

## Edge cases

An unrealized key, a negative real cutoff with empty domain, or any incompatible stored count vector is handled by the empty-fibre branch. A realized key's exceptional support cannot contain spurious positions, because it is exactly the encoded support; arbitrary unrealized keys need no well-formedness premise. Empty continuation, terminal singleton, and `J.card = 0` give entropy zero and cardinal at most one. If `c = 0`, the supplied cell map already controls whether `K` can be nonzero; no positive-cell-count assumption is necessary. Zero natural counts and unused cells are valid inputs to the existing `typeEntropy`. The arbitrary route can only split a fibre further and does not require a routing correctness assumption for this deterministic counting theorem.

No Lean code, frozen contract, or earlier report was edited in preparing this candidate.
