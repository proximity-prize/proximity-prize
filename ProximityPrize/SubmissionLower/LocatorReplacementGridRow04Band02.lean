import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Band02Y01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_04_band_02 : RowBandReceipt 4 14 21 := by
  intro cy hylo hyhi
  by_cases h : cy.val < 18
  · exact receipt_row_04_band_02_y_00 cy hylo h
  · exact receipt_row_04_band_02_y_01 cy (by omega) hyhi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
