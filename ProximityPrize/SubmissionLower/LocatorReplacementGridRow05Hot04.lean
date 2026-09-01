import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Hot03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_band_05_y_17_fixed :
    FixedYReceipt 5 ⟨17, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_05_band_05_y_17 : RowBandReceipt 5 17 18 :=
  fixedYReceipt_to_rowBand 5 ⟨17, by decide⟩ receipt_row_05_band_05_y_17_fixed

theorem receipt_row_05_band_05 : RowBandReceipt 5 15 18 := by
  intro cy hylo hyhi
  by_cases h₁₆ : cy.val < 16
  · exact receipt_row_05_band_05_y_15 cy hylo h₁₆
  by_cases h₁₇ : cy.val < 17
  · exact receipt_row_05_band_05_y_16 cy (by omega) h₁₇
  · exact receipt_row_05_band_05_y_17 cy (by omega) hyhi

theorem receipt_row_05_band_06 : RowBandReceipt 5 18 22 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
