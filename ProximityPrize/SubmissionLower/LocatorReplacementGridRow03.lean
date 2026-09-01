import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03Band02
import ProximityPrize.SubmissionLower.LocatorReplacementGridY22

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_fast : FastRowReceipt 3 := by
  intro cy
  by_cases h₀ : cy.val < 7
  · exact receipt_row_03_band_00 cy (Nat.zero_le _) h₀
  by_cases h₁ : cy.val < 14
  · exact receipt_row_03_band_01 cy (by omega) h₁
  by_cases h₂ : cy.val < 22
  · exact receipt_row_03_band_02 cy (by omega) h₂
  · exact receipt_y_22 3 cy (by omega) (by simpa [coarseYCells, ysCap] using cy.isLt)

theorem receipt_row_03 : RowReceipt 3 :=
  fastRowReceipt_to_rowReceipt 3 receipt_row_03_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
