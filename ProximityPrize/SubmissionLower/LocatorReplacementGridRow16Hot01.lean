import ProximityPrize.SubmissionLower.LocatorReplacementGridRow16Hot00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_16_band_00 : RowBandReceipt 16 0 3 := by
  intro cy hylo hyhi
  by_cases h_1 : cy.val < 1
  · exact receipt_row_16_band_00_a cy hylo h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_16_band_00_b cy (by omega) h_2
  · exact receipt_row_16_band_00_c cy (by omega) hyhi

theorem receipt_row_16_band_01 : RowBandReceipt 16 3 4 := by decide +kernel

theorem receipt_row_16_band_02 : RowBandReceipt 16 4 5 := by decide +kernel

theorem receipt_row_16_band_03 : RowBandReceipt 16 5 6 := by decide +kernel

theorem receipt_row_16_band_04 : RowBandReceipt 16 6 7 := by decide +kernel

theorem receipt_row_16_band_05 : RowBandReceipt 16 7 8 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
