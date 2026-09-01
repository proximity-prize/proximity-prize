import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_05_band_00 : RowBandReceipt 5 0 3 := by decide +kernel

theorem receipt_row_05_band_01 : RowBandReceipt 5 3 6 := by decide +kernel

theorem receipt_row_05_band_02 : RowBandReceipt 5 6 9 := by decide +kernel

theorem receipt_row_05_band_03 : RowBandReceipt 5 9 12 := by decide +kernel

theorem receipt_row_05_band_04 : RowBandReceipt 5 12 15 := by decide +kernel

theorem receipt_row_05_band_05 : RowBandReceipt 5 15 18 := by decide +kernel

theorem receipt_row_05_band_06 : RowBandReceipt 5 18 22 := by decide +kernel

theorem receipt_row_05 : RowReceipt 5 := by
  intro cy
  by_cases h₀ : cy.val < 3
  · exact receipt_row_05_band_00 cy (Nat.zero_le _) h₀
  by_cases h₁ : cy.val < 6
  · exact receipt_row_05_band_01 cy (by omega) h₁
  by_cases h₂ : cy.val < 9
  · exact receipt_row_05_band_02 cy (by omega) h₂
  by_cases h₃ : cy.val < 12
  · exact receipt_row_05_band_03 cy (by omega) h₃
  by_cases h₄ : cy.val < 15
  · exact receipt_row_05_band_04 cy (by omega) h₄
  by_cases h₅ : cy.val < 18
  · exact receipt_row_05_band_05 cy (by omega) h₅
  · exact receipt_row_05_band_06 cy (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
