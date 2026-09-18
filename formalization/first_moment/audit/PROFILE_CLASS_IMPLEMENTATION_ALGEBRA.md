# Independent algebra/source review of the profile-class implementation

Decision: **PASS**. All six definitions and four theorem interfaces in the frozen `PROFILE_CLASS_CONTRACT.md` are implemented exactly in `FirstMomentModel/ProfileClasses.lean`. No correction is requested.

Reviewed hashes:

- frozen contract: `6b62d3b2f3968864b58614bfdf2626c5162c725ac9b537a85793a749f445d612`;
- implementation: `09ac6696d61400096f60b5ebe168304b672e819e388b18513fa14f6921368887`.

This is an independent source/interface/proof inspection. The root agent is separately running compilation and the kernel-dependency audit. This review makes no claim to have rerun those checks.

## Exact definitions and assumptions

`exceptionalPositions` uses precisely the zero-based extension range `[length(join y z),length x)` inside `Fin K`, together with the negation of `good` applied to the actual digit. It does not include the whole interval following the ambient prefix.

`goodDigitCount` uses the same range, the prescribed joint cell, the specified digit value, and the actual good predicate. Its output is the natural count, not a normalized real count. All universally quantified cell/good/route data remain arbitrary; no measurability, regularity, positivity, or source-specialization premise has been added.

`exceptionalBudget` is exactly `Nat.floor (alpha * Real.log N)`. `ProfileWord` retains the original real inequality and only the three frozen fields: admissible boundary pair, membership in its stable family, and the real exceptional cutoff. In particular it does not substitute the floor inequality into the domain or add a nonnegative-alpha premise.

`encodeProfile` stores the two existing boundary codes, the actual stable-word length, the good counts flattened by the inverse of `finProdFinEquiv`, the entire labeled exceptional support, and the specified route. The existing `admissiblePair_rawPair` and `stable_desc` theorems supply legality and length/digit bounds. The stored exceptional value is the actual digit, not a representative probability, cardinality, or sentinel.

`ProfileClass` is exactly the subtype of the finite key type lying in the encoder's range. No injectivity of stable words is asserted or used.

## The four proofs

P1 applies `Nat.le_floor` directly to the real subtype inequality. This is valid without assuming alpha is nonnegative; an impossible negative-cutoff domain simply has no elements.

P2 bounds a filtered finite universe by `card (Fin K)=K`. It works for arbitrary words, including lengths greater than K, with no hidden legality or length premise.

P3 has all seven frozen conclusions, with no stable-word equality or exact-size-exponent conclusion. It obtains the two boundary word equalities from the already proved boundary encoders' injectivity. Length and route follow by projection. The count proof evaluates the flattened vector at `finProdFinEquiv (a,l)` and uses the inverse identity, so every cell/digit count is recovered.

The dependent exceptional labels are handled correctly. Equality of the sparse assignments first yields equality of the actual support finsets. A proof-local total lookup evaluates a supported digit and returns k outside the support. Membership is transported to the second support, so both lookups are evaluated on their supported branch. Equality therefore yields equality of the actual digits at every position in the first support. This does not weaken labeled support equality to equality of support cardinalities, and it introduces no exported lookup declaration.

P4 injects the range subtype into the existing finite key type using `Subtype.val`. It uses the proved exact `card_profileKey` formula. It does not assume a `Finite` or `Fintype` instance for the stable-word domain. Finiteness of the class follows from its being a subtype of the finite key type.

The resulting coefficient is exactly

    4 * (k+1)^2 * (K+1)^(c*k+3)
      * sparseCount K k qb^2 * sparseCount K k qe.

The three length factors come from the two boundary codes and the stable-word length; the vector contributes c*k further factors; the two boundary tags give `(k+1)^2`; the route gives 4. Both boundary supports and the exceptional labeled support are counted once in their prescribed factors.

## Edge cases and source correspondence

- At `K=0`, all supports and counts are empty and all length fields are zero. The proofs use no positive-length premise.
- `c=0` needs no added premise: providing `cell : Fin K -> Fin 0` already forces the relevant empty situation, and the empty flattened vector is well-defined.
- Negative alpha cannot introduce zero-exception words because the real domain bound is retained and the existing model has `N>1`.
- Budgets larger than K are allowed by the existing sparse-assignment type/count theorem.
- Zero piles create no encoding issue: stable-word legality supplies a valid digit at every actual position. No positivity premise is added for arbitrary non-realized codes.
- For `x=join y z`, both filters are empty. Terminal singleton and fallback words are retained exactly as the frozen domain specifies; the numerical argument is still responsible for excluding fallback cases when appropriate.
- With the source choice of joint cells and representative good predicate, these counts are the counts in TeX `def:space-time-digit-profile`, before division by positive `log N`. Retaining exceptional **values** is the previously reviewed refinement explicitly used in the first-moment counting paragraph. Arbitrary routing makes at most four classes but is not asserted to prove a density estimate.

There are exactly the six frozen top-level definitions and four frozen top-level theorems. Inspection found no additional exported mathematical claim, placeholder, `axiom`, `sorry`, or `admit` in this implementation.

This completes the actual class-count bridge. It does not prove the separate word-fiber entropy bound, model-to-profile numerical estimates, stochastic density/localization inputs, or the final shuffle first-moment theorem.
