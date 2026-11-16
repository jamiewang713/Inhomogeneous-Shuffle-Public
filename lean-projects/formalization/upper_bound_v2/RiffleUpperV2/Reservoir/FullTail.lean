import RiffleUpperV2.Reservoir.PrefixCount

noncomputable section
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

theorem tailBinPrefix_full {k L : ℕ} (s : Word k (L+1)) :
    tailBinPrefix L (s.get 0) (tailPrefix L s)=RiffleLowerV2.fullPrefix s := by
  have hs := (tailBinPrefix_word L (s.get 0) (tailPrefix L s) s).mpr ⟨rfl,rfl⟩
  have ht : s.toList.take (min L L+1)=s.toList := by
    rw [Nat.min_self]
    exact List.take_of_length_le (by simp)
  rw [ht] at hs
  apply Sigma.ext
  · apply Fin.ext
    simp [tailBinPrefix,RiffleLowerV2.fullPrefix]
  · exact (Subtype.heq_iff_coe_eq (fun x => by simp [tailBinPrefix,RiffleLowerV2.fullPrefix])).mpr hs.symm

theorem word_eq_of_head_tail_full {k L : ℕ} (w s : Word k (L+1))
    (hhead : w.get 0=s.get 0) (htail : tailPrefix L w=tailPrefix L s) : w=s := by
  have hw := (tailBinPrefix_word L (s.get 0) (tailPrefix L s) w).mpr ⟨hhead,htail⟩
  have hs := (tailBinPrefix_word L (s.get 0) (tailPrefix L s) s).mpr ⟨rfl,rfl⟩
  have ht (z : Word k (L+1)) : z.toList.take (min L L+1)=z.toList := by
    rw [Nat.min_self]
    exact List.take_of_length_le (by simp)
  rw [ht] at hw hs
  exact List.Vector.toList_injective (hw.trans hs.symm)

end RiffleUpperV2.Reservoir
