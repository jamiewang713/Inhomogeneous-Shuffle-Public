import RiffleUpperV2.EmpiricalUpper.FiniteTV
import RiffleUpperV2.Margins.Suffix
import RiffleLowerV2.Model.Physical

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.EmpiricalUpper
open TimeProfile RiffleLowerV2.Model

def tailCuts {k N K : ℕ} (cuts : Cuts k N (K+1)) : Cuts k N K where
  count j := cuts.count j.succ
  sum_count j := cuts.sum_count j.succ

theorem cuts_heq {k N L L' : ℕ} (h : L = L') (c : Cuts k N L) (d : Cuts k N L')
    (hc : ∀ (j : Fin L) (j' : Fin L'), j.val = j'.val → ∀ l, c.count j l = d.count j' l) :
    HEq c d := by
  subst L'
  have he : c = d := by
    cases c with
    | mk cc cs =>
      cases d with
      | mk dc ds =>
        congr 1
        funext j l
        exact hc j j rfl l
  exact heq_of_eq he

/-- The first physical column and the following columns, in their original order. -/
def sampleHeadEquiv {k N K : ℕ} (cuts : Cuts k N (K+1)) :
    Sample cuts ≃ ColumnAssignments cuts 0 × Sample (tailCuts cuts) where
  toFun ω := (ω 0, fun j => ω j.succ)
  invFun v := Fin.cases v.1 v.2
  left_inv ω := by funext j; exact Fin.cases rfl (fun _ => rfl) j
  right_inv v := by rfl

theorem uniformProduct {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    (PMF.uniformOfFintype α).bind (fun a =>
      (PMF.uniformOfFintype β).map (fun b => (a,b))) =
        PMF.uniformOfFintype (α × β) := by
  ext ⟨x,y⟩
  simp [PMF.bind_apply, PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply,
    Fintype.card_prod, ENNReal.mul_inv, Prod.mk.injEq, ite_and]

theorem physicalInverse_head {k N K : ℕ} (cuts : Cuts k N (K+1))
    (ω : Sample cuts) :
    RiffleLowerV2.physicalInverse ω =
      (Tuple.sort (ω 0).val).trans
        (RiffleLowerV2.physicalInverse ((sampleHeadEquiv cuts ω).2)) := by
  rw [← physicalInverseList_full, List.finRange_succ]
  rw [← physicalInverseList_full]
  simp only [physicalInverseList, List.foldr_cons, List.foldr_map]
  rfl

def transLeftEquiv {N : ℕ} (s : Permutation N) : Permutation N ≃ Permutation N where
  toFun t := s.trans t
  invFun t := s.symm.trans t
  left_inv t := by simp [← Equiv.trans_assoc]
  right_inv t := by simp [← Equiv.trans_assoc]

/-- Exact convolution identity, with the inverse of the first chronological
column composed before the inverse retained suffix. -/
theorem physicalInverseLaw_head {k N K : ℕ} (cuts : Cuts k N (K+1)) :
    physicalInverseLaw cuts = (columnPMF cuts 0).bind (fun a =>
      (physicalInverseLaw (tailCuts cuts)).map (transLeftEquiv (Tuple.sort a.val))) := by
  have he := map_uniform_equiv (sampleHeadEquiv cuts)
  have hp : fixedCountPMF cuts =
      (PMF.uniformOfFintype (ColumnAssignments cuts 0 × Sample (tailCuts cuts))).map
        (sampleHeadEquiv cuts).symm := by
    simpa only [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id,
      fixedCountPMF, TimeProfile.fixedCountPMF] using
      (congrArg (fun P => P.map (sampleHeadEquiv cuts).symm) he)
  change (fixedCountPMF cuts).map RiffleLowerV2.physicalInverse = _
  rw [hp, ← uniformProduct]
  simp only [PMF.map_bind, PMF.map_comp]
  congr 1
  funext a
  change _ = ((fixedCountPMF (tailCuts cuts)).map RiffleLowerV2.physicalInverse).map _
  rw [PMF.map_comp]
  congr 1
  funext ω
  exact physicalInverse_head cuts ((sampleHeadEquiv cuts).symm (a,ω))

theorem deleteFirstTVContraction {k N K : ℕ} (cuts : Cuts k N (K+1)) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      tv (physicalInverseLaw (tailCuts cuts)) (uniformPermutation N) := by
  rw [physicalInverseLaw_head]
  exact randomEquivTVContraction (columnPMF cuts 0) (physicalInverseLaw (tailCuts cuts))
    (fun a => transLeftEquiv (Tuple.sort a.val))

/-- Discard any initial segment of independent physical shuffles. The retained
array is the literal suffix, so this result preserves all chronological indices. -/
theorem deletedPrefixTVContraction {k N K : ℕ} (cuts : Cuts k N K)
    (r : ℕ) (hr : r ≤ K) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      tv (physicalInverseLaw (Margins.suffixCuts cuts r)) (uniformPermutation N) := by
  induction r generalizing K with
  | zero =>
    have he : Margins.suffixCuts cuts 0 = cuts := by
      simp only [Margins.suffixCuts, Margins.suffixIndex, Nat.zero_add]
      rfl
    rw [he]
  | succ r ih =>
    cases K with
    | zero => omega
    | succ K =>
      have hh := ih (tailCuts cuts) (by omega)
      apply (deleteFirstTVContraction cuts).trans
      convert hh using 1 <;> try rfl
      simp only [Margins.suffixCuts, tailCuts, Margins.suffixIndex, Fin.succ,
        Nat.add_right_comm]
      congr 2
      · omega
      · apply cuts_heq (by omega)
        intro j j' hj l
        dsimp only
        congr 2
        omega

end RiffleUpperV2.EmpiricalUpper
