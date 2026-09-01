import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot06BPart02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_10 : RowBandReceipt 8 12 13 := by
  intro cy hylo hyhi
  exact receipt_row_08_band_tail_a cy hylo (by omega)

theorem receipt_row_08_band_11 : RowBandReceipt 8 13 14 := by
  intro cy hylo hyhi
  exact receipt_row_08_band_tail_a cy (by omega) hyhi

theorem receipt_row_08_band_12 : RowBandReceipt 8 14 22 := by
  intro cy hylo hyhi
  by_cases h_16 : cy.val < 16
  · exact receipt_row_08_band_tail_b cy hylo h_16
  by_cases h_18 : cy.val < 18
  · exact receipt_row_08_band_tail_c cy (by omega) h_18
  by_cases h_20 : cy.val < 20
  · exact receipt_row_08_band_tail_d cy (by omega) h_20
  · exact receipt_row_08_band_tail_e cy (by omega) hyhi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
