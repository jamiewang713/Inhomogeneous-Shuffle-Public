import RiffleTimeProfile.FixedCountModel
import RiffleShuffle.Graphs

namespace RiffleLowerV2
/-- Tests the canonical dependent fixed-count sample, including empty decks. -/
theorem sample_exists {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) :
    Nonempty (TimeProfile.ShuffleSample cuts) := inferInstance
end RiffleLowerV2
