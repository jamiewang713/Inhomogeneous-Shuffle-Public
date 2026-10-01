import RiffleLowerV2.Types.Construction
import RiffleLowerV2.Types.Approximation
import RiffleLowerV2.Types.Empty
import RiffleLowerV2.Types.Partition
import Contracts.v1.WitnessGeometry

noncomputable section
open TimeProfile
namespace RiffleLowerV2.Types

/-- Manuscript `lem:type-estimates`, with the exact frozen uniform quantifiers. -/
theorem roundedType : RiffleLowerV2.Targets.RoundedTypeTarget := by
  intro k hk C hC
  refine ⟨typeConstant k C, typeConstant_pos k hC, ?_⟩
  intro T xi hT hxi hxiK m
  have hB : 0 ≤ Real.log (1/xi) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (cutoff_log_ge_one hxi (cutoff_small hk hxi hxiK).1)
  refine ⟨roundConstant k m T (Real.log (1/xi)), roundConstant_pos k m hT hB,
    typeThreshold, typeThreshold_ge_two, ?_⟩
  intro N K hlarge P hm hreg cuts hN I hsize alpha ha
  let D := constructedTypeData cuts hN hk P I hxi hxiK alpha
  have hspec : TypeDataSpec cuts hN P I xi alpha D :=
    constructedTypeData_spec cuts hN (typeThreshold_ge_two.trans hlarge) hk P I hxi hxiK hreg alpha
  refine ⟨D, hspec, ?_⟩
  simpa only [hm] using
    type_approximation_uniform hk cuts hN hlarge P I hxi hxiK hC hT hreg ha hsize D hspec

end RiffleLowerV2.Types
