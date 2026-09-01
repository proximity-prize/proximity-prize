import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Hot05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_fast : FastRowReceipt 4 := by
  intro cy
  by_cases h₀ : cy.val < 7
  · exact receipt_row_04_band_00 cy (Nat.zero_le _) h₀
  by_cases h₁ : cy.val < 14
  · exact receipt_row_04_band_01 cy (by omega) h₁
  · exact receipt_row_04_band_02 cy (by omega) (by omega)

theorem receipt_row_04 : RowReceipt 4 :=
  fastRowReceipt_to_rowReceipt 4 receipt_row_04_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
