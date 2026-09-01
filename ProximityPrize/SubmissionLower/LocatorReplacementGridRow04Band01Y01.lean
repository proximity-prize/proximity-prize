import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Band01Y01Z03
namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_row_04_band_01_y_01 : RowBandReceipt 4 10 14 := by
  intro cy hylo hyhi
  by_cases h₀ : cy.val < 11
  · exact receipt_row_04_band_01_y_01_z_00 cy hylo h₀
  by_cases h₁ : cy.val < 12
  · exact receipt_row_04_band_01_y_01_z_01 cy (by omega) h₁
  by_cases h₂ : cy.val < 13
  · exact receipt_row_04_band_01_y_01_z_02 cy (by omega) h₂
  · exact receipt_row_04_band_01_y_01_z_03 cy (by omega) hyhi
end ProximityPrize.SubmissionLower.LocatorReplacementGridData
