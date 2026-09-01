import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot07Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_band_12_y_21_fixed :
    FixedYReceipt 6 ⟨21, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_band_12_y_21 : RowBandReceipt 6 21 22 :=
  fixedYReceipt_to_rowBand 6 ⟨21, by decide⟩ receipt_row_06_band_12_y_21_fixed

theorem receipt_row_06_band_12 : RowBandReceipt 6 14 22 := by
  intro cy hylo hyhi ct
  by_cases h₁₅ : cy.val < 15
  · exact receipt_row_06_band_12_y_14 cy hylo h₁₅ ct
  by_cases h₁₆ : cy.val < 16
  · exact receipt_row_06_band_12_y_15 cy (by omega) h₁₆ ct
  by_cases h₁₇ : cy.val < 17
  · exact receipt_row_06_band_12_y_16 cy (by omega) h₁₇ ct
  by_cases h₁₈ : cy.val < 18
  · exact receipt_row_06_band_12_y_17 cy (by omega) h₁₈ ct
  by_cases h₁₉ : cy.val < 19
  · exact receipt_row_06_band_12_y_18 cy (by omega) h₁₉ ct
  by_cases h₂₀ : cy.val < 20
  · exact receipt_row_06_band_12_y_19 cy (by omega) h₂₀ ct
  by_cases h₂₁ : cy.val < 21
  · exact receipt_row_06_band_12_y_20 cy (by omega) h₂₁ ct
  · exact receipt_row_06_band_12_y_21 cy (by omega) hyhi ct

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
