import RiffleLowerV2.Localization.Endpoints.Means
import RiffleLowerV2.Localization.Endpoints.Counts

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Localization
open TimeProfile

/-- A finite disjoint-cylinder family inherits the ambient square-root error bound. -/
theorem finite_weight_error {ι : Type*} (S : Finset ι) (mu value : ι → ℝ)
    (A M D : ℝ) (hA : 0 ≤ A) (_hM : 0 ≤ M) (_hD : 0 ≤ D)
    (hmu : ∀ i, 0 ≤ mu i) (hcard : (S.card : ℝ) ≤ D)
    (hsum : ∑ i ∈ S, mu i ≤ M)
    (herr : ∀ i ∈ S, |value i - mu i| ≤ A*(Real.sqrt (mu i)+1)) :
    |∑ i ∈ S, (value i-mu i)| ≤ A*(Real.sqrt D*Real.sqrt M+D) := by
  have hcs := Real.sum_sqrt_mul_sqrt_le (f := fun _ : ι => (1 : ℝ)) (g := mu)
    S (fun _ => by norm_num) hmu
  have hsq : (∑ i ∈ S, Real.sqrt (mu i)) ≤ Real.sqrt D*Real.sqrt M := by
    calc
      _ ≤ Real.sqrt (S.card : ℝ)*Real.sqrt (∑ i ∈ S, mu i) := by simpa using hcs
      _ ≤ Real.sqrt D*Real.sqrt M := mul_le_mul (Real.sqrt_le_sqrt hcard)
        (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ ∑ i ∈ S, |value i-mu i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, A*(Real.sqrt (mu i)+1) := Finset.sum_le_sum herr
    _ = A*((∑ i ∈ S, Real.sqrt (mu i)) + S.card) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp
    _ ≤ A*(Real.sqrt D*Real.sqrt M+D) := mul_le_mul_of_nonneg_left (add_le_add hsq hcard) hA

theorem side_error_bound {k N K l m : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K) (x : WordOn k (columnSet K l m))
    (omega : Sample cuts) (A : ℝ) (hA : 0 < A)
    (hconc : ∀ v : Prefix k K, |(prefixCount v omega : ℝ)-prefixMean cuts v| ≤
      A*(Real.sqrt (prefixMean cuts v)+1))
    (R : Fin k → Fin k → Prop) (hR : ∀ d e, R d e → d ≠ e) :
    |∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d => R d (x j)),
      ((prefixCount (sidePrefix a l m x j d) omega : ℝ)-prefixMean cuts (sidePrefix a l m x j d))| ≤
      A*(Real.sqrt ((k : ℝ)*K)*Real.sqrt (prefixMean cuts (prefixAt l a))+(k : ℝ)*K) := by
  let S : Finset ((columnSet K l m) × Fin k) :=
    Finset.univ.filter (fun p => R p.2 (x p.1))
  have hmem (p : (columnSet K l m) × Fin k) : p ∈ S ↔ R p.2 (x p.1) := by simp [S]
  have hsum (f : (columnSet K l m) × Fin k → ℝ) :
      (∑ p ∈ S, f p) = ∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d => R d (x j)), f (j,d) := by
    have he : S = Finset.univ.filter (fun p => R p.2 (x p.1)) := by ext p; simp [hmem]
    rw [he, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_filter]
  have hcard : (S.card : ℝ) ≤ (k : ℝ)*K := by
    have h1 : S.card ≤ Fintype.card ((columnSet K l m) × Fin k) := Finset.card_le_univ S
    have h2 : (columnSet K l m).card ≤ K := by
      simpa using (Finset.card_le_univ (columnSet K l m))
    have h3 : S.card ≤ k*K := calc
      S.card ≤ (columnSet K l m).card*k := by simpa [Fintype.card_prod] using h1
      _ ≤ K*k := Nat.mul_le_mul_right k h2
      _ = k*K := Nat.mul_comm _ _
    exact_mod_cast h3
  have hmu (p : (columnSet K l m) × Fin k) :
      0 ≤ prefixMean cuts (sidePrefix a l m x p.1 p.2) := by
    unfold prefixMean prefixMass
    positivity
  have htotal : (∑ p ∈ S, prefixMean cuts (sidePrefix a l m x p.1 p.2)) ≤
      prefixMean cuts (prefixAt l a) := by
    rw [hsum]
    exact sideMean_sum_le cuts hN a hlm hm x R hR
  have he := finite_weight_error S
    (fun p => prefixMean cuts (sidePrefix a l m x p.1 p.2))
    (fun p => (prefixCount (sidePrefix a l m x p.1 p.2) omega : ℝ))
    A (prefixMean cuts (prefixAt l a)) ((k : ℝ)*K) hA.le
    (by unfold prefixMean prefixMass; positivity) (by positivity) hmu hcard htotal
    (fun p _ => hconc (sidePrefix a l m x p.1 p.2))
  rwa [hsum] at he

end RiffleLowerV2.Localization
