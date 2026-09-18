# Profile classes: independent implementation audit

Reviewer: `inequality_audit`. Decision: **approved against the exact frozen
contract**. No interface correction or model-assumption change is needed.

Reviewed source:
`FirstMomentModel/ProfileClasses.lean`, SHA-256
`09ac6696d61400096f60b5ebe168304b672e819e388b18513fa14f6921368887`.

Frozen `PROFILE_CLASS_CONTRACT.md` SHA-256:
`6b62d3b2f3968864b58614bfdf2626c5162c725ac9b537a85793a749f445d612`.

The earlier model-bridge and original contracts retain hashes
`7d04c06ab51c086bf97d60e3b52caac9b798cdb07b7b0cb5b99ea7a78042cbc5`
and
`5ba1c21dc9933186ebff72f9c502b286d15787db29d6d62961a9ea8bfe866f0b`.

This review read the actual implementation and frozen contract. Compilation
was already reported by the implementing agent; the root agent's active
trust verification was not rerun or interrupted. No code, contract, or
earlier review report was edited.

## Definition preservation

All six definitions match the freeze.

- `exceptionalPositions` uses precisely the zero-based interval from
  `join y z` through the final stable-word position and the negation of
  the actual good predicate. It does not start at the ambient prefix or
  omit the final position.
- `goodDigitCount` filters that same interval by the actual cell, digit,
  and good predicate. Its counts are natural, with no normalization or
  approximation inserted.
- `exceptionalBudget` is the exact natural floor of `alpha*log N`.
- `ProfileWord` retains the original real cutoff. Its only fields beyond
  the triple are admissible-pair membership, stable membership, and that
  cutoff. No extra sign, legality, retention, nonterminal, or finite-domain
  premise is present.
- `encodeProfile` stores both actual boundary encodings, the stable-word
  length, the `c*k` natural good counts using `finProdFinEquiv.symm`, the
  complete labeled exceptional assignment, and the supplied route.
  Legality is derived with `stable_desc` and `admissiblePair_rawPair`.
- `ProfileClass` is literally the subtype of `Set.range encodeProfile`
  inside the frozen finite key type. It is not the stable-word domain and
  does not assert that words are uniquely encoded.

## Theorem preservation and proof checks

**P1.** `profileWord_exceptional_budget` has exactly the frozen domain and
conclusion. Its proof applies `Nat.le_floor` directly to the real cutoff
from the subtype. No `alpha>=0` hypothesis is introduced.

**P2.** `goodDigitCount_le` is stated for arbitrary raw words without
legality or length assumptions. It bounds a filtered subset of `Fin K`
by the universe cardinality, exactly as reviewed.

**P3.** `encodeProfile_eq_data` concludes all seven frozen data equalities.
Boundary words are recovered with the already proved boundary injections;
length and route are the corresponding key projections. Count equality
evaluates the stored vector at `finProdFinEquiv (a,l)`, cancelling its
inverse in the encoder, so neither count coordinate is lost.

The exceptional support equality is equality of the actual finsets, not
just equality of cardinalities. The digit-equality proof projects equality
of the entire sparse assignments through a proof-local lookup function.
For every index in the first support, the proved support equality supplies
membership in the second; both lookups therefore evaluate their stored
actual digits. The lookup's off-support sentinel cannot mask a mismatch.
There is no word-equality or exact `cL`-equality conclusion.

**P4.** `profileClass_card_le` has no source or class `Finite`/`Fintype`
premise. It applies `Finite.card_le_of_injective` to the actual subtype
value map into `ProfileKey`, then uses the frozen `card_profileKey`.
This is a genuine finite-subset cardinality argument. It does not use
the totalized value `Nat.card=0` for infinite types to bypass an injection,
and it does not pretend to prove word-level injectivity. The counted type
is exactly the realized-class subtype specified in the freeze.

## Degenerate cases and scope

- Negative alpha is not converted into a permissive zero budget in the
  source domain; the real cutoff remains mandatory.
- `K=0`, `c=0`, empty cells, empty extension ranges, and oversized budgets
  introduce no hidden nonemptiness assumptions.
- Empty supports cause the exceptional-label statement to be vacuous,
  as specified; nonempty supports retain every label.
- The supplied route remains arbitrary deterministic data. No density
  property is inferred from its value.
- This module proves neither a within-fiber entropy bound nor the eventual
  subpower count without the later parameter choices. It adds no such
  claim implicitly.

The file contains exactly the six planned definitions and four planned
theorems. All intermediate facts and lookup functions are proof-local.
A static scan found no `axiom`, `sorry`, `admit`, `native_decide`, or
`unsafe` token. The root verification remains responsible for the compiled
dependency audit.
