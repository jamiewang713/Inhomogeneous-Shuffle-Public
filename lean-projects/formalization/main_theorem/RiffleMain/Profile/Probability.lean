import RiffleMain.Profile.Definitions
import RiffleLowerV2.Occupancy.FiniteProbability

set_option autoImplicit false

noncomputable section
open Filter
open scoped BigOperators
namespace RiffleMain.Profile

theorem probability_inter_lower {Ω : Type*} [Fintype Ω]
    (Q : PMF Ω) (A B : Ω → Prop) :
    RiffleUpperV2.probability Q A + RiffleUpperV2.probability Q B - 1 ≤
      RiffleUpperV2.probability Q (fun x => A x ∧ B x) := by
  classical
  have h := RiffleLowerV2.Factorial.expect_mono Q
    (f := fun x => (if A x then (1 : ℝ) else 0) + (if B x then 1 else 0) - 1)
    (g := fun x => if A x ∧ B x then 1 else 0) (by
      intro x
      by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb])
  simp only [RiffleLowerV2.Factorial.expect_sub,
    RiffleLowerV2.Factorial.expect_add, RiffleLowerV2.Factorial.expect_const] at h
  simpa [RiffleUpperV2.probability, RiffleLowerV2.probability,
    RiffleLowerV2.expect] using h

theorem probability_inter_tendsto_one
    {Ω : ℕ → Type*} [∀ N, Fintype (Ω N)]
    (Q : ∀ N, PMF (Ω N)) (A B : ∀ N, Ω N → Prop)
    (hA : Tendsto (fun N => RiffleUpperV2.probability (Q N) (A N)) atTop (nhds 1))
    (hB : Tendsto (fun N => RiffleUpperV2.probability (Q N) (B N)) atTop (nhds 1)) :
    Tendsto (fun N => RiffleUpperV2.probability (Q N) (fun x => A N x ∧ B N x))
      atTop (nhds 1) := by
  have hlow := (hA.add hB).sub_const 1
  norm_num only at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hlow) tendsto_const_nhds
    (fun N => probability_inter_lower (Q N) (A N) (B N))
    (fun N => RiffleLowerV2.Occupancy.probability_le_one (Q N) _)

/-- An event containing an asymptotically certain event is asymptotically certain. -/
theorem probability_tendsto_one_mono
    {Ω : ℕ → Type*} [∀ N, Fintype (Ω N)]
    (Q : ∀ N, PMF (Ω N)) (A B : ∀ N, Ω N → Prop)
    (hA : Tendsto (fun N => RiffleUpperV2.probability (Q N) (A N)) atTop (nhds 1))
    (hAB : ∀ᶠ N in atTop, ∀ x, A N x → B N x) :
    Tendsto (fun N => RiffleUpperV2.probability (Q N) (B N)) atTop (nhds 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hA.eventually (eventually_gt_nhds ha), hAB] with N hN hABN
    exact hN.trans_le (RiffleLowerV2.Occupancy.probability_mono (Q N) hABN)
  · intro a ha
    exact Filter.Eventually.of_forall fun N =>
      (RiffleLowerV2.Occupancy.probability_le_one (Q N) (B N)).trans_lt ha

/-- Finitely many convergences in probability hold jointly; no independence is used. -/
theorem probability_tendsto_one_finset
    {Ω : ℕ → Type*} [∀ N, Fintype (Ω N)] {ι : Type*}
    (Q : ∀ N, PMF (Ω N)) (s : Finset ι) (A : ι → ∀ N, Ω N → Prop)
    (hA : ∀ i ∈ s,
      Tendsto (fun N => RiffleUpperV2.probability (Q N) (A i N)) atTop (nhds 1)) :
    Tendsto (fun N => RiffleUpperV2.probability (Q N)
      (fun x => ∀ i ∈ s, A i N x)) atTop (nhds 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa [RiffleUpperV2.probability, RiffleLowerV2.probability,
        RiffleLowerV2.Factorial.expect_const] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  | @insert i s hi ih =>
      have hAi := hA i (Finset.mem_insert_self i s)
      have hAs := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.mem_insert, forall_eq_or_imp] using
        probability_inter_tendsto_one Q (A i)
          (fun N x => ∀ j ∈ s, A j N x) hAi hAs

end RiffleMain.Profile
