import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Band02Y00Z01
namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_row_04_band_02_y_00 : RowBandReceipt 4 14 18 := by
  intro cy hylo hyhi
  by_cases h : cy.val < 16
  · exact receipt_row_04_band_02_y_00_z_00 cy hylo h
  · exact receipt_row_04_band_02_y_00_z_01 cy (by omega) hyhi
end ProximityPrize.SubmissionLower.LocatorReplacementGridData
