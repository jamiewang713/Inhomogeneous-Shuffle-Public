import RiffleUpperV2.Conditional.PairReduction
import RiffleUpperV2.Reservoir.Denominator

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional

 theorem conditionalProbability_nonneg {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (E H : Ω → Prop) : 0≤conditionalProbability P E H := by
  exact div_nonneg (RiffleLowerV2.Thinning.probability_nonneg P _)
    (RiffleLowerV2.Thinning.probability_nonneg P _)

theorem conditionalProbability_le_one {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (E H : Ω → Prop) : conditionalProbability P E H≤1 := by
  have hn := RiffleLowerV2.Thinning.probability_nonneg P H
  by_cases hz : probability P H=0
  · simp [conditionalProbability,RiffleLowerV2.conditionalProbability,hz]
  · have hp : 0<probability P H := lt_of_le_of_ne hn (Ne.symm hz)
    apply (div_le_one hp).mpr
    exact RiffleLowerV2.Thinning.probability_mono P (fun _ h => h.2)

/-- An assignment fixed by the conditioning information incurs no factor
for the number of blocks when squares are summed. -/
theorem conditionalSquare_partition {Ω E I : Type*}
    [Fintype Ω] [Fintype E] [Fintype I] (P : PMF Ω) (H : Ω → Prop)
    (event current : E → Ω → Prop) (block : I → E → Ω → Prop)
    (assign : E → Option I)
    (hpart : ∀e ω,H ω → event e ω →
      match assign e with | none => current e ω | some a => block a e ω) :
    (∑e,(conditionalProbability P (event e) H)^2)≤
      conditionalExpect P (fun ω => ((Finset.univ.filter fun e => current e ω).card:ℝ)) H +
        ∑a,∑e,(conditionalProbability P (block a e) H)^2 := by
  rw [conditionalExpect_card]
  have h (e : E) : (conditionalProbability P (event e) H)^2≤
      conditionalProbability P (current e) H+∑a,(conditionalProbability P (block a e) H)^2 := by
    have hnon := conditionalProbability_nonneg P (event e) H
    cases ha : assign e with
    | none =>
      have hm := Reservoir.conditionalProbability_mono_on P (event e) (current e) H
        (fun ω hH he => by simpa only [ha] using hpart e ω hH he)
      have hone := conditionalProbability_le_one P (event e) H
      have hs : 0≤∑a,(conditionalProbability P (block a e) H)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      nlinarith
    | some a =>
      have hm := Reservoir.conditionalProbability_mono_on P (event e) (block a e) H
        (fun ω hH he => by simpa only [ha] using hpart e ω hH he)
      have hsq : (conditionalProbability P (event e) H)^2≤(conditionalProbability P (block a e) H)^2 := by
        nlinarith [conditionalProbability_nonneg P (block a e) H]
      have hs := Finset.single_le_sum (fun b (_:b∈(Finset.univ:Finset I)) =>
        sq_nonneg (conditionalProbability P (block b e) H)) (Finset.mem_univ a)
      linarith [conditionalProbability_nonneg P (current e) H]
  have hh := Finset.sum_le_sum (fun e (_:e∈(Finset.univ:Finset E)) => h e)
  rw [Finset.sum_add_distrib,Finset.sum_comm] at hh
  exact hh

/-- Replacing squares by probabilities gives the expected number of block
edges. This is used only in the tiny and intermediate regimes. -/
theorem conditionalSquares_le_card {Ω E : Type*} [Fintype Ω] [Fintype E]
    (P : PMF Ω) (H : Ω → Prop) (event : E → Ω → Prop) :
    (∑e,(conditionalProbability P (event e) H)^2)≤
      conditionalExpect P (fun ω => ((Finset.univ.filter fun e => event e ω).card:ℝ)) H := by
  rw [conditionalExpect_card]
  apply Finset.sum_le_sum
  intro e _
  have h0 := conditionalProbability_nonneg P (event e) H
  have h1 := conditionalProbability_le_one P (event e) H
  nlinarith

end RiffleUpperV2.Conditional
