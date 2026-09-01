import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Hot01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_band_01_y_12_fixed :
    FixedYReceipt 4 ⟨12, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_04_band_01_y_12 : RowBandReceipt 4 12 13 :=
  fixedYReceipt_to_rowBand 4 ⟨12, by decide⟩ receipt_row_04_band_01_y_12_fixed

private theorem receipt_row_04_band_01_y_13_fixed :
    FixedYReceipt 4 ⟨13, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_04_band_01_y_13 : RowBandReceipt 4 13 14 :=
  fixedYReceipt_to_rowBand 4 ⟨13, by decide⟩ receipt_row_04_band_01_y_13_fixed

theorem receipt_row_04_band_01 : RowBandReceipt 4 7 14 := by
  intro cy hylo hyhi ct
  by_cases h₈ : cy.val < 8
  · exact receipt_row_04_band_01_y_07 cy hylo h₈ ct
  by_cases h₉ : cy.val < 9
  · exact receipt_row_04_band_01_y_08 cy (by omega) h₉ ct
  by_cases h₁₀ : cy.val < 10
  · exact receipt_row_04_band_01_y_09 cy (by omega) h₁₀ ct
  by_cases h₁₁ : cy.val < 11
  · exact receipt_row_04_band_01_y_10 cy (by omega) h₁₁ ct
  by_cases h₁₂ : cy.val < 12
  · exact receipt_row_04_band_01_y_11 cy (by omega) h₁₂ ct
  by_cases h₁₃ : cy.val < 13
  · exact receipt_row_04_band_01_y_12 cy (by omega) h₁₃ ct
  · exact receipt_row_04_band_01_y_13 cy (by omega) hyhi ct

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
