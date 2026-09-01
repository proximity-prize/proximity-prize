import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Band06T05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

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

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
