# LB02 compatibility component receipt

The seven source ports and the new all-positive-s subset transform are checked under Lean 4.33.1 and pinned mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. No original source or freeze was changed. This component does not by itself prove the frozen permutation-law target, successive thinning, or the concrete prefix theorem.

Import `RiffleLowerV2.Thinning.Compat.SubsetTransform`. All declarations formerly in `Shuffle` now live in `RiffleLowerV2.Thinning.Compat`, including `FiniteLaw`, `HypergeomParams`, `Sample`, and `sampleLaw`.

New checked declarations:

```lean
RiffleLowerV2.Thinning.Compat.HypergeomParams.expect_pow_le_all
  (p : HypergeomParams) {s : ℝ} (hs : 0 < s) :
  p.law.expect (fun q => s ^ q.val) ≤
    (1 - (p.draws : ℝ) / p.population +
      ((p.draws : ℝ) / p.population) * s) ^ p.marked

RiffleLowerV2.Thinning.Compat.sample_expect_intersection_eq_hypergeom
  {α : Type*} [DecidableEq α] (V A : Finset α) (m : ℕ)
  (hm : m ≤ V.card) (hA : A ⊆ V) (f : ℕ → ℝ) :
  (sampleLaw V m hm).expect (fun S => f (A ∩ S.val).card) =
    (samplingParams V A m hA hm).law.expect (fun q => f q.val)

RiffleLowerV2.Thinning.Compat.sample_expect_pow_intersection_le
  {α : Type*} [DecidableEq α] (V A : Finset α) (m : ℕ)
  (hm : m ≤ V.card) (hA : A ⊆ V) {s : ℝ} (hs : 0 < s) :
  (sampleLaw V m hm).expect (fun S => s ^ (A ∩ S.val).card) ≤
    (1 - (m : ℝ) / V.card + ((m : ℝ) / V.card) * s) ^ A.card
```

These bounds have no s≤1 premise. They use the retained finite positive-u factorial-moment proof for s≥1 and the retained hypergeometric complement argument for 0<s≤1. The arbitrary-marked-set subset result transfers through the proved exact `sample_intersection_law` and `FiniteLaw.expect_eq_of_count_law`, so its uniform-sampling premise is discharged. The helper also covers an empty population; the frozen concrete target's M>0 domain is unchanged.

The port preserves every retained public mathematical signature apart from namespace relocation. Documented implementation changes are: the pinned `Nat.choose_mul` signature; explicit common Fin sum domains and reverse values in the complement proof; explicit positive-event arguments in two conditioned-law rewrites; a case split to reconcile distinct decision procedures in the product-rectangle identity; explicit pair-map reduction in a finite inverse proof; and the renamed `Finset.card_sdiff_of_subset` API. None changes a mathematical hypothesis or conclusion.

Two unrelated portions are intentionally omitted: `FiniteLaw.variance_toPMF` and its direct variance import; and the analytic concentration suffix of `HypergeometricConcentration.lean` starting at the old private `expect_exp_le`. The latter required an unregistered direct exponential module, and root-owned generic PMF tails handle that work. Finite variance, hypergeometric moments, conditioning, residual subset laws, and finite-PMF expectation adapters remain present.

Successful command from the package directory:

```text
python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Compat.Check
```

The complete successful output is `compat_build_v6.log`. Earlier failed runs remain in `compat_build_v1.log` through `compat_build_v5.log`; they are development records, not receipts. The check rebuilds dependencies solely in the LB02 lane output and examines all 274 elaborated declarations in the compatibility namespace and its private namespace. The dependency closure union is exactly `propext`, `Classical.choice`, and `Quot.sound`; the check rejects anything else. No proof placeholder or native proof oracle was used. Nonfatal upstream-style lint warnings remain in the source ports.

`compat_receipt_v1.json` records each original source hash, final port hash, exact signature/implementation changes, new helper hashes, runtime, successful build, and closure result. `compat_declarations_v1.json` records every inspected exact type and individual closure. Original hashes were recomputed after the successful build and matched the saved pre-port hashes.

The next required bridge is uniform permutations and fixed-histogram columns to these actual subset laws. That bridge is separate work; this receipt does not presume it.
