import ProximityPrize.SubmissionLower.ContactGCDCumulativeFlags
import ProximityPrize.SubmissionLower.ContactRobustFixedMeet
namespace ProximityPrize.SubmissionLower.ContactGCDCumulativeLedger

open scoped Classical BigOperators
open ContactFlagBezout ContactGCDCumulativeFlags
open  ContactRobustFixedMeet
open ContactRegularFactorFlag ContactOriginalRegularSeedCount
open ContactResidualSupportParameters ContactInterpolation ContactTranslation

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

theorem linear_cost_cumulative (cz cy ca : ℕ) (f : FlagDegree)
    (hzy : cz ≤ cy) (hya : cy ≤ ca) :
    f.zOnly * cz + f.yz * cy + f.all * ca =
      cz * (f.zOnly + f.yz + f.all) +
        (cy - cz) * (f.yz + f.all) + (ca - cy) * f.all := by
  have hy : cz + (cy - cz) = cy := by omega
  have ha : cz + (cy - cz) + (ca - cy) = ca := by omega
  calc
    f.zOnly * cz + f.yz * cy + f.all * ca =
        f.zOnly * cz + f.yz * (cz + (cy - cz)) +
          f.all * (cz + (cy - cz) + (ca - cy)) := by rw [ha, hy]
    _ = _ := by ring

variable {K : Type} [Field K]

end
end ProximityPrize.SubmissionLower.ContactGCDCumulativeLedger
