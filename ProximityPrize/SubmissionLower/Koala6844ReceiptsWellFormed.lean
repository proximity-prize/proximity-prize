import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

theorem terminal_profile_wellFormed (i : Fin contactProfiles.size) :
    sourceWellFormed contactProfiles[i] = true := by
  change Fin 34 at i
  fin_cases i <;> decide +kernel

end ProximityPrize.SubmissionLower.Koala6844Receipts
