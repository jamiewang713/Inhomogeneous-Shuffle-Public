import RiffleUpperV2.FirstMoment.Partition

noncomputable section
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization
attribute [local instance] Classical.propDecidable

abbrev RetainedAtPile {k n d : ℕ} (hk : 0 < k) (N : ℕ) (cuts : Cuts k n d) (hn : 0 < n)
    (R : Fin k → Finset (Fin n)) (C chi delta : ℝ) (hchi : chi ≤ 1/(k : ℝ)) :=
  Σ pile : Fin k, {b : BlockTriple k d // ValidBlock N cuts (R pile) chi delta b ∧
    RetainedBlock hk N cuts hn C chi hchi b}

/-- Every retained actual block has the prescribed finite key, with the bin bound
proved from the horizon rather than supplied as a premise of the class model. -/
def retainedDescriptor {k n d N : ℕ} (hk : 0 < k) (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Fin k → Finset (Fin n))
    (T C chi delta width : ℝ) (hchi : 0 < chi) (hchi1 : chi ≤ 1)
    (hchiK : chi ≤ 1/(k : ℝ)) (hwidth : 0 < width) (hd : (d : ℝ) ≤ T*logScale N)
    (t : RetainedAtPile hk N cuts hn R C chi delta hchiK) :
    EmpiricalKey k d (boundaryBudget N C chi) (extensionBudget N chi) (empiricalBinCount T chi width) :=
  let b := t.2.1
  empiricalDescriptor cuts hn (leftDefault hk cuts hn chi hchiK)
    (rightDefault hk cuts hn chi hchiK) t.1
    ⟨b.1,t.2.2.2.1⟩ ⟨b.2.1,t.2.2.2.2.1⟩ b.2.2 chi width delta (R t.1)
    t.2.2.2.2.2
    (goodCost_bin_bound hN cuts hn _ chi width hchi hchi1 hwidth _ hd)

def retainedClasses {k n d N : ℕ} (hk : 0 < k) (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Fin k → Finset (Fin n))
    (T C chi delta width : ℝ) (hchi : 0 < chi) (hchi1 : chi ≤ 1)
    (hchiK : chi ≤ 1/(k : ℝ)) (hwidth : 0 < width) (hd : (d : ℝ) ≤ T*logScale N) :
    Finset (EmpiricalKey k d (boundaryBudget N C chi) (extensionBudget N chi)
      (empiricalBinCount T chi width)) := by
  classical
  exact Finset.univ.image (retainedDescriptor hk hN cuts hn R T C chi delta width
    hchi hchi1 hchiK hwidth hd)

/-- Uniform bound on the actual realized retained classes, not an abstract
assumption about an externally supplied encoding. -/
theorem retainedClasses_uniform_count (k : ℕ) (T C epsilon : ℝ)
    (hk : 2 ≤ k) (hT : 0 ≤ T) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 < min 1 (1/(k : ℝ)) ∧
      ∀ chi : ℝ, ∀ hchi : 0 < chi, chi < chi0 → ∀ width : ℝ, ∀ hwidth : 0 < width,
        ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N n d : ℕ, N0 ≤ N → ∀ hN : 2 ≤ N,
          ∀ hn : 0 < n, ∀ hd : (d : ℝ) ≤ T*logScale N,
          ∀ hchi1 : chi ≤ 1, ∀ hchiK : chi ≤ 1/(k : ℝ),
          ∀ cuts : Cuts k n d, ∀ R : Fin k → Finset (Fin n), ∀ delta : ℝ,
          ((retainedClasses (by omega) hN cuts hn R T C chi delta width
            hchi hchi1 hchiK hwidth hd).card : ℝ) ≤ (N : ℝ)^epsilon := by
  obtain ⟨chi0,hchi0,hchi0k,hcount⟩ := empiricalCostClassCount k T C epsilon hk hT hC hepsilon
  refine ⟨chi0,hchi0,hchi0k,?_⟩
  intro chi hchi hchilt width hwidth
  obtain ⟨N0,hN0,hbound⟩ := hcount chi hchi hchilt width hwidth
  refine ⟨N0,hN0,?_⟩
  intro N n d hN0N hN hn hd hchi1 hchiK cuts R delta
  classical
  exact (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hbound N d hN0N hd)

/-- Literal coverage by retained block cylinders or discarded full-word rows. -/
theorem fullWord_retained_or_discarded {k n d N : ℕ} (hk : 0 < k)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Fin k → Finset (Fin n)) (pile : Fin k)
    (C chi delta : ℝ) (hchiK : chi ≤ 1/(k : ℝ)) (w : Fin d → Fin k)
    (hw : Legal cuts (R pile) (RiffleLowerV2.fullPrefix (List.Vector.ofFn w))) :
    (∃ t : RetainedAtPile hk N cuts hn R C chi delta hchiK,
      t.1 = pile ∧ IsPrefix t.2.1.2.2 (RiffleLowerV2.fullPrefix (List.Vector.ofFn w))) ∨
      w ∈ discardedWords hk N cuts hn (R pile) C chi delta hchiK := by
  obtain ⟨b,hb,_⟩ := blockPartition N cuts hn (R pile) chi delta
    (RiffleLowerV2.fullPrefix (List.Vector.ofFn w)) hw rfl
  by_cases hret : RetainedBlock hk N cuts hn C chi hchiK b.1
  · exact Or.inl ⟨⟨pile,⟨b.1,b.2,hret⟩⟩,rfl,hb⟩
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hb,hret⟩)

end RiffleUpperV2.FirstMoment
