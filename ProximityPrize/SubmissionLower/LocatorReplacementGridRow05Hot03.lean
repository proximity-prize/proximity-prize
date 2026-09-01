import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Hot02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_05_band_04 : RowBandReceipt 5 12 15 := by
  intro cy hylo hyhi
  by_cases h_13 : cy.val < 13
  · exact receipt_row_05_band_04_a cy hylo h_13
  by_cases h_14 : cy.val < 14
  · exact receipt_row_05_band_04_b cy (by omega) h_14
  · exact receipt_row_05_band_04_c cy (by omega) hyhi

private theorem receipt_row_05_band_05_y_15_fixed :
    FixedYReceipt 5 ⟨15, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_05_band_05_y_15 : RowBandReceipt 5 15 16 :=
  fixedYReceipt_to_rowBand 5 ⟨15, by decide⟩ receipt_row_05_band_05_y_15_fixed

private theorem receipt_row_05_band_05_y_16_fixed :
    FixedYReceipt 5 ⟨16, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_05_band_05_y_16 : RowBandReceipt 5 16 17 :=
  fixedYReceipt_to_rowBand 5 ⟨16, by decide⟩ receipt_row_05_band_05_y_16_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
