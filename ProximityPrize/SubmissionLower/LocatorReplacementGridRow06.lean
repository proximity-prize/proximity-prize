import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06B
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06C

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

theorem receipt_row_06_band_06 : RowBandReceipt 6 8 9 := by
  intro cy hylo hyhi ct
  by_cases h₀ : ct.val < 4
  · exact receipt_row_06_band_06_t_00 cy hylo hyhi ct (Nat.zero_le _) h₀
  by_cases h₁ : ct.val < 8
  · exact receipt_row_06_band_06_t_01 cy hylo hyhi ct (by omega) h₁
  by_cases h₂ : ct.val < 12
  · exact receipt_row_06_band_06_t_02 cy hylo hyhi ct (by omega) h₂
  by_cases h₃ : ct.val < 16
  · exact receipt_row_06_band_06_t_03 cy hylo hyhi ct (by omega) h₃
  by_cases h₄ : ct.val < 20
  · exact receipt_row_06_band_06_t_04 cy hylo hyhi ct (by omega) h₄
  · exact receipt_row_06_band_06_t_05 cy hylo hyhi ct (by omega) (by omega)

theorem receipt_row_06 : RowReceipt 6 := by
  intro cy
  by_cases h₀ : cy.val < 3
  · exact receipt_row_06_band_00 cy (Nat.zero_le _) h₀
  by_cases h_4 : cy.val < 4
  · exact receipt_row_06_band_01 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_06_band_02 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_06_band_03 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_06_band_04 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_06_band_05 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_06_band_06 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_06_band_07 cy (by omega) h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_06_band_08 cy (by omega) h_11
  by_cases h_12 : cy.val < 12
  · exact receipt_row_06_band_09 cy (by omega) h_12
  by_cases h_13 : cy.val < 13
  · exact receipt_row_06_band_10 cy (by omega) h_13
  by_cases h_14 : cy.val < 14
  · exact receipt_row_06_band_11 cy (by omega) h_14
  · exact receipt_row_06_band_12 cy (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
