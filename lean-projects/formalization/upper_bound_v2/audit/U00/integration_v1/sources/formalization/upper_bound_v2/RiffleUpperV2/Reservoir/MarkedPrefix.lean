import RiffleUpperV2.Reservoir.PrefixConditional
import RiffleLowerV2.Thinning.Residual.Prefix

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile RiffleLowerV2.Thinning

/-- Every prescribed-disjoint marked tuple has its actual embedding into the
remaining population; no enumeration assumption is needed by callers. -/
theorem existsMarkedComplement {k n L b m : ℕ}
    (r : RiffleLowerV2.RowPrescription n k L b) (hr : Function.Injective r.row)
    (f : Fin m ↪ Fin n) (hf : ∀ i q, r.row i ≠ f q) :
    ∃ e : Fin (n-b) → Fin n, Function.Injective e ∧
      (∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) ∧
      ∃ a : Fin m ↪ Fin (n-b), ∀ q, e (a q) = f q := by
  obtain ⟨e,he,hc⟩ := existsComplementEnumeration r hr
  have hx (q : Fin m) : ∃ i, e i=f q := (hc _).mpr (by rintro ⟨i,hi⟩; exact hf i q hi)
  let a : Fin m → Fin (n-b) := fun q => Classical.choose (hx q)
  have ha (q) : e (a q)=f q := Classical.choose_spec (hx q)
  refine ⟨e,he,hc,⟨a,?_⟩,ha⟩
  intro q s h
  apply f.injective
  rw [← ha q, ← ha s, h]

theorem residual_prefixWeight_marked {k n L b m : ℕ} (cuts : Cuts k n (L+1))
    (r : RiffleLowerV2.RowPrescription n k (L+1) b) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r))
    (f : Fin m ↪ Fin n) (hf : ∀ i q, r.row i ≠ f q)
    (J : Finset (Fin (L+1))) (hJ : (0 : Fin (L+1)) ∉ J)
    (a : Fin (L+1) → Fin k) (p : Fin k)
    (hcount : m ≤ cuts.count 0 p - RiffleLowerV2.usedCount r 0 p) :
    conditionalProbability (fixedCountPMF cuts) (commonDigits f J a)
      (fun ω => RiffleLowerV2.prescriptionEvent r ω ∧
        ∀ q, sampleEntry ω (f q) 0 = p) =
    ∏ j ∈ J, RiffleLowerV2.falling (cuts.count j (a j) - RiffleLowerV2.usedCount r j (a j)) m /
      RiffleLowerV2.falling (n-b) m := by
  obtain ⟨e,he,hc,a',ha⟩ := existsMarkedComplement r hr f hf
  have h := residual_prefixWeight_given_pile cuts r hr hp e he hc a' J hJ a p hcount
  convert h using 1
  congr 1 <;> funext ω <;> simp only [commonDigits, ha]

/-- Reindexing the selected columns retains their original time order and
sums out every other column. -/
theorem residual_coordinatesWeight_marked {k n L b m t : ℕ} (cuts : Cuts k n (L+1))
    (r : RiffleLowerV2.RowPrescription n k (L+1) b) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r))
    (f : Fin m ↪ Fin n) (hf : ∀ i q, r.row i ≠ f q)
    (d : Fin t ↪ Fin (L+1)) (hd : ∀ j, d j ≠ 0)
    (a : Fin t → Fin k) (p : Fin k)
    (hcount : m ≤ cuts.count 0 p - RiffleLowerV2.usedCount r 0 p) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => ∀ j q, sampleEntry ω (f q) (d j) = a j)
      (fun ω => RiffleLowerV2.prescriptionEvent r ω ∧
        ∀ q, sampleEntry ω (f q) 0 = p) =
    ∏ j : Fin t, RiffleLowerV2.falling (cuts.count (d j) (a j) - RiffleLowerV2.usedCount r (d j) (a j)) m /
      RiffleLowerV2.falling (n-b) m := by
  let J := Finset.univ.map d
  let a' := Function.extend d a (fun _ => p)
  have he (j) : a' (d j) = a j := d.injective.extend_apply a (fun _ => p) j
  have hJ : (0 : Fin (L+1)) ∉ J := by
    simp only [J, Finset.mem_map, Finset.mem_univ, true_and, not_exists]
    exact hd
  have hh := residual_prefixWeight_marked cuts r hr hp f hf J hJ a' p hcount
  have hE : commonDigits (cuts := cuts) f J a' =
      (fun ω => ∀ j q, sampleEntry ω (f q) (d j) = a j) := by
    funext ω
    apply propext
    simp only [commonDigits, J, Finset.mem_map, Finset.mem_univ, true_and,
      forall_exists_index, forall_apply_eq_imp_iff, he]
  rw [hE] at hh
  simpa only [J, Finset.prod_map, he] using hh

/-- Exact probability of a common short tail prefix, conditional on the
actual exposed rows and the marked first digits. -/
theorem residual_tailPrefixWeight_marked {k n L b m : ℕ} (cuts : Cuts k n (L+1))
    (r : RiffleLowerV2.RowPrescription n k (L+1) b) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r))
    (f : Fin m ↪ Fin n) (hf : ∀ i q, r.row i ≠ f q)
    (D : ℕ) (v : Word k (min D L)) (p : Fin k)
    (hcount : m ≤ cuts.count 0 p - RiffleLowerV2.usedCount r 0 p) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => ∀ q, tailPrefix D (rowWord ω (f q)) = v)
      (fun ω => RiffleLowerV2.prescriptionEvent r ω ∧
        ∀ q, sampleEntry ω (f q) 0 = p) =
    ∏ j : Fin (min D L), RiffleLowerV2.falling
      (cuts.count ⟨j.val+1, by have := j.isLt; omega⟩ (v.get j) -
        RiffleLowerV2.usedCount r ⟨j.val+1, by have := j.isLt; omega⟩ (v.get j)) m /
      RiffleLowerV2.falling (n-b) m := by
  let d : Fin (min D L) ↪ Fin (L+1) :=
    ⟨fun j => ⟨j.val+1, by have := j.isLt; omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  have h := residual_coordinatesWeight_marked cuts r hr hp f hf d
    (fun j h => by have hh := congrArg Fin.val h; change j.val+1=0 at hh; omega) v.get p hcount
  have he : (fun ω : Sample cuts => ∀ q, tailPrefix D (rowWord ω (f q)) = v) =
      (fun ω => ∀ j q, sampleEntry ω (f q) (d j) = v.get j) := by
    funext ω
    apply propext
    constructor
    · intro h j q
      simpa only [tailPrefix, List.Vector.get_ofFn, RiffleLowerV2.rowWord_get, d, Function.Embedding.coeFn_mk] using congrArg (fun w => w.get j) (h q)
    · intro h q
      apply List.Vector.ext
      intro j
      simpa only [tailPrefix, List.Vector.get_ofFn, RiffleLowerV2.rowWord_get, d, Function.Embedding.coeFn_mk] using h j q
  rw [he]
  exact h

end RiffleUpperV2.Reservoir
