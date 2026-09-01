import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_band_07_t_05_fixed :
    FixedYReceipt 6 ⟨9, by decide⟩ 20 22 := by decide +kernel

theorem receipt_row_06_band_07_t_05 : RowTileReceipt 6 9 10 20 22 :=
  fixedYReceipt_to_rowTile 6 ⟨9, by decide⟩ 20 22
    receipt_row_06_band_07_t_05_fixed

theorem receipt_row_06_band_07 : RowBandReceipt 6 9 10 := by
  intro cy hylo hyhi ct
  by_cases h₄ : ct.val < 4
  · exact receipt_row_06_band_07_t_00 cy hylo hyhi ct (Nat.zero_le _) h₄
  by_cases h₈ : ct.val < 8
  · exact receipt_row_06_band_07_t_01 cy hylo hyhi ct (by omega) h₈
  by_cases h₁₂ : ct.val < 12
  · exact receipt_row_06_band_07_t_02 cy hylo hyhi ct (by omega) h₁₂
  by_cases h₁₆ : ct.val < 16
  · exact receipt_row_06_band_07_t_03 cy hylo hyhi ct (by omega) h₁₆
  by_cases h₂₀ : ct.val < 20
  · exact receipt_row_06_band_07_t_04 cy hylo hyhi ct (by omega) h₂₀
  · exact receipt_row_06_band_07_t_05 cy hylo hyhi ct (by omega) ct.isLt

theorem receipt_row_06_band_08 : RowBandReceipt 6 10 11 := by decide +kernel

theorem receipt_row_06_band_09 : RowBandReceipt 6 11 12 := by decide +kernel

theorem receipt_row_06_band_10 : RowBandReceipt 6 12 13 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
