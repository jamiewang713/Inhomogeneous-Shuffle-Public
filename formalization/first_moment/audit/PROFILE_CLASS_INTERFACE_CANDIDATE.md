# Actual profile-class counting: candidate interface

Status: independent statement design only, 2026-09-17. No new definition or statement is frozen or implemented by this report. The original two frozen contracts remain unchanged.

I independently reread the authorized unified TeX's space-time digit profile definition, exceptional-profile truncation/counting proof, and final first-moment class decomposition. I also inspected the proved boundary bridge, the frozen `ProfileKey` count, the existing entropy interface, and the current `TimeProfile` digit definitions.

The proposed actual domain and range-of-keys construction are viable. The minimal recommended supplement has six definitions and four public theorems. It counts realized refined descriptors, not individual stable words.

## Fixed deterministic data

Work in namespace `InhomogeneousShuffle.FirstMoment.Model` with:

* `D : Riffle.Model` and `A : Riffle.Setup D`;
* a natural `c` and `cell : Fin D.K → Fin c`, assigning a joint time/partition cell to each column;
* `good : Fin D.K → ℕ → Prop`, a total predicate on column/digit pairs;
* a real exceptional cutoff `alpha`.

There is no positivity, regularity, measurability, or decidability premise on these new deterministic parameters. Classical decidability is used internally. There is no new premise on `A`, the model, stable words, or integer budgets. In particular, the finite-count statements need not assume `0 ≤ alpha`.

## Six definitions

All displayed definitions are specifications, not new Lean implementation.

1. `profileExceptionalPositions (good : Fin D.K → ℕ → Prop)
   (v : ℕ) (x : Riffle.Word) : Finset (Fin D.K)` is `Finset.univ` filtered by

   `v ≤ j.val ∧ j.val < x.length ∧ ¬good j (Riffle.digit x j.val)`.

2. `profileGoodDigitCount (cell : Fin D.K → Fin c)
   (good : Fin D.K → ℕ → Prop) (v : ℕ) (x : Riffle.Word)
   (a : Fin c) (l : Fin D.k) : ℕ` is the cardinality of `Finset.univ` filtered by

   `v ≤ j.val ∧ j.val < x.length ∧ good j (Riffle.digit x j.val) ∧
    cell j = a ∧ Riffle.digit x j.val = l.val`.

   These are unnormalized natural counts. Division by `log N` is performed only when relating them to the source's real profile counts.

3. `exceptionalBudget (A : Riffle.Setup D) (alpha : ℝ) : ℕ` is

   `Nat.floor (alpha * Real.log (D.N : ℝ))`.

4. The actual source domain is:

   ```lean
   ProfileWord (A : Riffle.Setup D) (good : Fin D.K → ℕ → Prop)
       (alpha : ℝ) : Type :=
     {t : Riffle.Word × Riffle.Word × Riffle.Word //
       Riffle.AdmissiblePair A t.1 t.2.1 ∧
       t.2.2 ∈ Riffle.Stable A t.1 t.2.1 ∧
       ((profileExceptionalPositions good
           (Riffle.join t.1 t.2.1).length t.2.2).card : ℝ) ≤
         alpha * Real.log (D.N : ℝ)}
   ```

   Thus the triple is `(y,z,x)`. The cutoff is the original real inequality. Do not replace this domain condition by the floor inequality alone: for negative `alpha`, the original domain is empty, whereas a zero-exception word could satisfy the floor inequality. Deriving the floor bound from this domain is valid without any sign premise.

   An extra `Retained` field is unnecessary: `Riffle.admissiblePair_retained` already derives it from actual admissibility and compatibility. Omitting that redundant field does not change the collection of retained admissible source pairs. The full `Stable` definition, including fallback, is used literally.

5. With `route : ProfileWord A good alpha → Fin 4`, define

   ```lean
   encodeProfile (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
       (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
       (route : ProfileWord A good alpha → Fin 4) :
       ProfileWord A good alpha →
         ProfileKey D.K D.k (boundaryBudget A) (exceptionalBudget A alpha)
           (c * D.k)
   ```

   For a domain element `(y,z,x)`, set `v = (Riffle.join y z).length`. Its key fields, in the already frozen order, are:

   * `encodeBoundary A .left y` and `encodeBoundary A .right z`, with their actual admissibility proofs;
   * `x.length : Fin (D.K + 1)`, using legality derived from `Riffle.stable_desc`;
   * the function `Fin (c * D.k) → Fin (D.K + 1)` whose value at `h` is the good-digit count at `(finProdFinEquiv.symm h).1` and `(finProdFinEquiv.symm h).2`;
   * the frozen `SparseAssignment` with support `profileExceptionalPositions good v x`, actual digit labels in `Fin D.k`, and the floor budget derived from the original real cutoff;
   * `route t`.

   Here trusted `finProdFinEquiv : Fin c × Fin D.k ≃ Fin (c * D.k)` fixes the flattening convention. No division by `c` or a separately assumed positive `c` is required in the statement. Counts are at most `D.K` because they count a subset of `Fin D.K`.

6. Define the type of realized refined classes by

   ```lean
   ProfileClass (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
       (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
       (route : ProfileWord A good alpha → Fin 4) : Type :=
     ↥(Set.range (encodeProfile A cell good alpha route))
   ```

   Every class has an actual source-word witness by its range membership. Two domain elements represent the same class exactly when their encoded keys agree. There is no need to construct a quotient implementation or to prove the word map injective.

## Four theorem interfaces

The following common parameters are understood in the displayed signatures:

```lean
{D : Riffle.Model} {c : ℕ}
(A : Riffle.Setup D) (cell : Fin D.K → Fin c)
(good : Fin D.K → ℕ → Prop) (alpha : ℝ)
(route : ProfileWord A good alpha → Fin 4)
```

**P1: actual exceptional budget.** No extra hypothesis beyond membership of the actual domain:

```lean
theorem profileWord_exceptional_le_budget
    (t : ProfileWord A good alpha) :
    (profileExceptionalPositions good
      (Riffle.join t.val.1 t.val.2.1).length t.val.2.2).card ≤
        exceptionalBudget A alpha
```

Only `A`, `good`, and `alpha` are parameters of P1; `cell`, `c`, and `route` do not occur. Its proof is directly `Nat.le_floor` applied to the domain's real bound.

**P2: bounded good counts.** This holds for any word and lower endpoint, with no legality or ordering premise:

```lean
theorem profileGoodDigitCount_le (v : ℕ) (x : Riffle.Word)
    (a : Fin c) (l : Fin D.k) :
    profileGoodDigitCount cell good v x a l ≤ D.K
```

Only `D`, `c`, `cell`, and `good` are parameters of P2. It follows from the cardinality of the ambient finite column type.

**P3: equal keys determine the source descriptor.** For `t,u : ProfileWord A good alpha`, equality

`encodeProfile A cell good alpha route t = encodeProfile A cell good alpha route u`

implies the following exact conjunction, where `v_t := (join t.val.1 t.val.2.1).length`, `x_t := t.val.2.2`, and similarly for `u`:

```lean
t.val.1 = u.val.1 ∧
t.val.2.1 = u.val.2.1 ∧
x_t.length = x_u.length ∧
(∀ a : Fin c, ∀ l : Fin D.k,
  profileGoodDigitCount cell good v_t x_t a l =
    profileGoodDigitCount cell good v_u x_u a l) ∧
profileExceptionalPositions good v_t x_t =
  profileExceptionalPositions good v_u x_u ∧
(∀ j ∈ profileExceptionalPositions good v_t x_t,
  Riffle.digit x_t j.val = Riffle.digit x_u j.val) ∧
route t = route u
```

Suggested name: `encodeProfile_eq_sourceData`. The abbreviations above can be proof-local `let`s in the statement or expanded literally before freeze. They are not additional exported definitions. Boundary equality uses the already proved `encodeBoundary_injective`. The count coordinate is read at `finProdFinEquiv (a,l)`. For exceptional labels, a proof-local total lookup with a sentinel outside the support avoids transporting equality of dependent label functions explicitly.

These projection facts are enough to identify original boundaries, times/length, normalized counts, exceptional support and its actual digit values inside a class. A reverse implication is true by construction but is not necessary for the requested range-based counting theorem. No implication `x_t = x_u` is asserted.

**P4: actual refined class count.** No finiteness or integer-budget premise:

```lean
theorem profileClass_card_le :
    Nat.card (ProfileClass A cell good alpha route) ≤
      profileCountBound D.K D.k (boundaryBudget A) (exceptionalBudget A alpha)
        (c * D.k)
```

The subtype-value map from `ProfileClass` into the existing finite `ProfileKey` is injective. It gives an actual finite instance even if no finite enumeration of `ProfileWord` has yet been built. The frozen `card_profileKey` or `profile_card_le_of_injective` then gives exactly the displayed bound. No count of source words is inferred from this argument.

P1/P2 could instead remain proof-local if reducing the exported theorem count is more important than exposing the bounds used to construct the key. The recommended public list fixes them explicitly so the key construction has named reviewed prerequisites.

## Source instantiation obligations

The generic deterministic data must be explicitly identified with the source before claiming the source count.

1. Convert the fixed columns to the existing `TimeProfile` simplex model, preserving actual legal digits. Take `c = R * P.cellCount`, where `R` is the chosen time-mesh cell count and `P` is the chosen regular Borel partition. Set

   `cell j = finProdFinEquiv (timeClass j, P.classify (p j))`.

   The time-cell membership theorem must use source time `(j.val+1)/log N` and the prescribed half-open cells with the final closed cell.

2. Make `good` a total predicate on natural digits: `good j a` holds exactly when `a < D.k` and the representative mass of digit `a` in `P.classify (p j)` is greater than `2*A.chi`. This can be expressed with an existential bound proof and a `Fin D.k` digit. On legal words it agrees with `TimeProfile.BorelPartition.IsGoodDigit`.

3. Identify the index interval `[join(y,z).length,x.length)` with the source one-based condition `s*log N < j ≤ u*log N`, using the actual prefix-time definitions. Verify equality with `TimeProfile.exceptionalPositions` and that `profileGoodDigitCount / log N` is `TimeProfile.digitCount`, under the stated flattening of the joint cell.

4. Take the actual source cutoff `alpha = (log(1/chi))^(-1/2)`. Positivity of `log N` follows from `D.one_lt_N`, so the source condition `R_x ≤ alpha` is equivalent to the real cardinal inequality retained in `ProfileWord`. The generic finite theorem itself does not need an independently asserted `alpha ≥ 0`.

5. The initial profile definition lists exceptional positions; the later counting and first-moment proof explicitly include exceptional digit values. The proposed key implements that later refined class definition. Its length and `Fin 4` fields refine the class further by at most the already frozen factors. If original coarser classes are used elsewhere, the projection onto them must be identified; the refined-class count is an upper bound for their count as well.

6. `route` may be arbitrary for counting, because there are only four values. For application to edge-density bounds, its four values must separately be proved to match the actual terminal/large/small-singleton/small-nonsingleton classification. This counting interface does not supply that classification or remove the terminal fallback family.

7. To derive the asymptotic source bound from `profileCount_eventually`, keep the alphabet size, chosen partition/time-mesh sizes, `C`, and `chi` fixed before `N` grows. Use the source horizon `K = floor(T*log N)` to obtain `K ≤ T*log N`, `qb ≤ (C/log(1/chi))*log N`, and `qe ≤ alpha*log N`. The source positivity facts justify the floor upper bounds. No equality `K/log N = T` is allowed. The choices of the generating-function parameters and small `chi` must then make the existing exponent less than the requested epsilon.

## Pitfalls excluded by this interface

* Good-digit rearrangements within a cell can share the key. The key map on words is intentionally not injective.
* The actual `cL` need not be identical within a coarse or refined key class: different good positions in the same regular cell can have slightly different actual pile masses. Equality of representative counts does give the same representative `S` and `H`, and labeled exceptional positions determine `Q`; uniform replacement estimates handle actual costs.
* Counts range up to `K`, hence `Fin (K+1)`, not `Fin K`. Their number of coordinates is `c*k`, not just `c`.
* Exception positions start strictly after the boundary join in one-based source notation, which becomes the inclusive lower bound `join.length ≤ j.val` in zero-based Lean columns. No boundary-prefix exception is counted a second time.
* Terminal singleton and stopped-root words have an empty continuation interval, so all continuation counts and exceptional positions are zero. They remain admissible for the positive source cutoff.
* The range class type is finite without a word-injectivity theorem. The finite first-moment assembly's separate word index type still needs its own derived finite enumeration; this can be constructed from legal bounded words and is not a new model assumption.
* Counting does not establish a discarded-mass estimate, an entropy bound for each actual class, or stochastic localization. For the actual class entropy bridge, its fixed exceptional support/labels and boundary prefix leave a fixed set of good positions; words in the class can then be injected into the existing type-class family on those positions. That is a separate reviewed application of the entropy theorem.

No missing model hypothesis was found for the finite descriptor count itself. The remaining items are identification and application theorems, not assumptions to add to the frozen model.
