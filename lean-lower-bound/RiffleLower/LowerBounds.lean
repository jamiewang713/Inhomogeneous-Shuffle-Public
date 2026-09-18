import RiffleLower.FixedColumns
import RiffleLower.Sorting
import RiffleLower.UniformPermutation
import RiffleLower.Profiles
import RiffleLower.Cold
import Mathlib.Order.PiLex

/-! The frozen finite deterministic and random-environment lower bounds.
The observable permutation maps sorted positions to original row labels. -/

noncomputable section
namespace RiffleLower
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def inverseShuffle {N K k : ℕ} (c : ColumnArray N K k) (ω : ColumnRandomness N K) :
    Equiv.Perm (Fin N) :=
  stableSort (fun i => (toLex (rowWord c ω i) : Lex (Fin K → Fin k)))

def shuffleLaw {N K k : ℕ} (c : ColumnArray N K k) : FiniteLaw (Equiv.Perm (Fin N)) :=
  mapLaw (uniformLaw (ColumnRandomness N K)) (inverseShuffle c)

/-- L01: a complete word with large mean produces a finite observable-run TV bound. -/
theorem deterministic_lower_bound {N K k : ℕ} (c : ColumnArray N K k)
    (w : Fin K → Fin k) (m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N)
    (hmean : (m : ℝ) < wordMean c w) :
    1 - wordMean c w / (wordMean c w - (m : ℝ)) ^ 2 -
      (((N - m + 1 : ℕ) : ℝ) / (m.factorial : ℝ)) ≤
      tv (shuffleLaw c) (uniformLaw (Equiv.Perm (Fin N))) := by
  let A := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => HasIncreasingRun σ m
  have hsuccess : 1 - wordMean c w / (wordMean c w - (m : ℝ)) ^ 2 ≤
      prob (shuffleLaw c) A := by
    rw [shuffleLaw, prob_map]
    apply (wordCount_lower_tail c w hN m hmean).trans
    apply prob_mono
    intro ω hω
    have hc : m ≤ wordCount c w ω := (Finset.mem_filter.mp hω).2
    have hr : HasIncreasingRun (inverseShuffle c ω) m := by
      apply full_word_forces_run
        (fun i => (toLex (rowWord c ω i) : Lex (Fin K → Fin k))) (toLex w) m hm
      simpa only [keyCount, wordCount, toLex_inj] using hc
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hr
  exact tv_test (shuffleLaw c) (uniformLaw (Equiv.Perm (Fin N))) A
    (wordMean c w / (wordMean c w - (m : ℝ)) ^ 2)
    (((N - m + 1 : ℕ) : ℝ) / (m.factorial : ℝ))
    hsuccess (prob_increasingRun_le hmN)

/-- L02: arbitrary random pile environments use one common increasing-run event. -/
theorem random_pile_lower_bound {E : Type*} [Fintype E] {N K k : ℕ}
    (ρ : FiniteLaw E) (c : E → ColumnArray N K k) (w : E → Fin K → Fin k)
    (G : Finset E) (m : ℕ) (ε δ : ℝ)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hG : 1 - ε ≤ prob ρ G)
    (hmean : ∀ e ∈ G, (m : ℝ) < wordMean (c e) (w e))
    (herr : ∀ e ∈ G,
      wordMean (c e) (w e) / (wordMean (c e) (w e) - (m : ℝ)) ^ 2 ≤ δ) :
    1 - ε - δ - (((N - m + 1 : ℕ) : ℝ) / (m.factorial : ℝ)) ≤
      tv (mixture ρ (fun e => shuffleLaw (c e))) (uniformLaw (Equiv.Perm (Fin N))) := by
  let A := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => HasIncreasingRun σ m
  have htest : ∀ e ∈ G, 1 - δ ≤ prob (shuffleLaw (c e)) A := by
    intro e he
    have hsuccess : 1 - wordMean (c e) (w e) / (wordMean (c e) (w e) - (m : ℝ)) ^ 2 ≤
        prob (shuffleLaw (c e)) A := by
      rw [shuffleLaw, prob_map]
      apply (wordCount_lower_tail (c e) (w e) hN m (hmean e he)).trans
      apply prob_mono
      intro ω hω
      have hc : m ≤ wordCount (c e) (w e) ω := (Finset.mem_filter.mp hω).2
      have hr : HasIncreasingRun (inverseShuffle (c e) ω) m := by
        apply full_word_forces_run
          (fun i => (toLex (rowWord (c e) ω i) : Lex (Fin K → Fin k))) (toLex (w e)) m hm
        simpa only [keyCount, wordCount, toLex_inj] using hc
      simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hr
    linarith [herr e he]
  have hmix := mixture_common_event ρ (fun e => shuffleLaw (c e)) G A ε δ hε hδ hG htest
  have h := tv_test (mixture ρ (fun e => shuffleLaw (c e)))
    (uniformLaw (Equiv.Perm (Fin N))) A (ε + δ)
    (((N - m + 1 : ℕ) : ℝ) / (m.factorial : ℝ)) (by linarith) (prob_increasingRun_le hmN)
  linarith

end RiffleLower
