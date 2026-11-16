import RiffleLowerV2.Types.Truncation
import RiffleTimeProfile.Analysis

noncomputable section
open TimeProfile
namespace RiffleLowerV2.Types

/-- The internal partition has regularity constant one for every admissible cutoff. -/
theorem exists_type_partition {k : ℕ} (hk : 2 ≤ k) {xi : ℝ}
    (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ))) :
    ∃ P : BorelPartition k, P.IsRegular xi 1 := by
  apply exists_regular_partition hk hxi
  have hsmall := (cutoff_small hk hxi hxiK).2.1
  linarith

end RiffleLowerV2.Types
