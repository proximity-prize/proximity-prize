import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03Band02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_03 : RowReceipt 3 := by
  intro cy
  by_cases h₀ : cy.val < 7
  · exact receipt_row_03_band_00 cy (Nat.zero_le _) h₀
  by_cases h₁ : cy.val < 14
  · exact receipt_row_03_band_01 cy (by omega) h₁
  · exact receipt_row_03_band_02 cy (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
