# Independent Lean 4.33 compatibility review

Reviewer: algebra reconstruction agent. Scope: the compatibility copies of the eleven `Riffle` modules and the three `FirstMomentModel` modules, compared with their original project files. No original, compatibility copy, frozen contract, or earlier frozen review was edited.

## Verdict

Approved. Every difference is an import or proof-body API adaptation. There is no change to a definition, declaration binder, theorem hypothesis, theorem conclusion, namespace, or exported declaration inventory. In particular, the frozen boundary, actual-profile-class, and profile-fibre interfaces remain unchanged.

## Independent checks

- Recomputed SHA-256 values for all fourteen original files and all fourteen compatibility copies. All twenty-eight values match the corresponding `PROVENANCE.json` entries.
- Regenerated unified diffs from the actual files, with the paths used by the saved patches. Both generated diffs agree byte-for-byte with their respective `COMPATIBILITY.patch` files. Thus the patches describe every on-disk difference, rather than selected changes.
- Inspected each changed line in its original declaration context. All changes after the single import replacement occur strictly inside theorem proofs.
- The compatibility tree contains exactly the eleven recorded stable-block modules (153 theorem declarations and 51 definition-like declarations) and the three recorded model modules (15 theorem declarations and 15 definitions). No compatibility-only declaration was introduced.
- A token scan of these fourteen compatibility source files found no `axiom`, `sorry`, or `admit` occurrence.

The parent task is separately running compilation, combined imports, and kernel dependency audits. This report verifies source and interface preservation; it does not substitute a textual scan for those trust checks.

## Complete change inventory

### Stable-block modules

Eight modules are byte-for-byte identical: `Cost`, `Definitions`, `Global`, `Model`, `Retention`, `SourceStable`, `Stopping`, and `Words`.

The three changed modules contain only these four line replacements:

1. `Boundary.incompatible_boundary_fiber_empty`: use the renamed `Set.eq_empty_iff_forall_notMem` instead of `Set.eq_empty_iff_forall_not_mem` in the proof. The set, incompatibility hypothesis, and equality to the empty set are unchanged.
2. `Mass.expectedCount_pos`: replace `zero_le _` by `zero_le` in the nonnegativity proof supplied to `Finset.single_le_sum`. The summand and the positivity statement are unchanged.
3. `Pieces.pieceEvent_iff`, forward implication: explicitly split on the existing `Side` argument and unfold `crossDigit` before applying the same digit equality.
4. `Pieces.pieceEvent_iff`, reverse implication: the same explicit split and unfolding, now using `digit_take`. Neither case split imposes a condition on the caller: both constructors of the already quantified side are proved.

### First-moment model modules

1. `BoundaryEncoding`: replace the import `Mathlib.Data.Finite.Card` by `Mathlib.SetTheory.Cardinal.Finite`.
2. `BoundaryEncoding.admissible_boundary_card_le` and `admissible_pair_card_le`: use `Nat.card_le_card_of_injective` in place of `Finite.card_le_of_injective`, with the identical encoder and identical injectivity proof. The finite target instances and the subsequent cardinal computations are unchanged.
3. `ProfileClasses.profileClass_card_le`: the same theorem-name replacement, with the same subtype-value injection into the same `ProfileKey`. Add `ProfileClass` to the proof's `simpa only` unfolding list. This does not alter the definition of classes as the encoder's range or insert any finiteness assumption.
4. `ProfileFibreEntropy.profileFibre_card_le_exp_entropy`: the same theorem-name replacement, applied to the identical restriction injection into the identical finite type class. The finite support, exception labels, literal prefix reconstruction, entropy quantity, and empty-fibre branch are unchanged.

No changes affect the sentinel/crossing distinction, real exceptional cutoff, labelled exceptional support, actual finite-domain derivation, type-class cardinality, or power normalization. All mathematical content and all caller-visible assumptions are preserved.
