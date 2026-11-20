import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

theorem terminal_profile_graphScale (i : Fin contactProfiles.size) :
    3*contactProfiles[i].k+3 ∣ graphScale := by
  change Fin 38 at i
  fin_cases i <;> decide +kernel

theorem terminal_profile_total (i : Fin contactProfiles.size) :
    contactProfiles[i].L + contactProfiles[i].q ≤ 3873 := by
  change Fin 38 at i
  fin_cases i <;> decide +kernel

end ProximityPrize.SubmissionLower.Koala6844Receipts
