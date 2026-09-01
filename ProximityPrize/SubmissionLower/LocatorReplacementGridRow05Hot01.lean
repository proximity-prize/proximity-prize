import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Hot00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_band_03_b_fixed :
    FixedYReceipt 5 ⟨10, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_05_band_03_b : RowBandReceipt 5 10 11 :=
  fixedYReceipt_to_rowBand 5 ⟨10, by decide⟩ receipt_row_05_band_03_b_fixed

private theorem receipt_row_05_band_03_c_fixed :
    FixedYReceipt 5 ⟨11, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_05_band_03_c : RowBandReceipt 5 11 12 :=
  fixedYReceipt_to_rowBand 5 ⟨11, by decide⟩ receipt_row_05_band_03_c_fixed

theorem receipt_row_05_band_03 : RowBandReceipt 5 9 12 := by
  intro cy hylo hyhi
  by_cases h_10 : cy.val < 10
  · exact receipt_row_05_band_03_a cy hylo h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_05_band_03_b cy (by omega) h_11
  · exact receipt_row_05_band_03_c cy (by omega) hyhi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
