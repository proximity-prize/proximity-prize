import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Band02T03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_band_02 : RowBandReceipt 9 4 5 := by
  intro cy hylo hyhi ct
  by_cases h₀ : ct.val < 1
  · exact receipt_row_09_band_02_t_00 cy hylo hyhi ct (Nat.zero_le _) h₀
  by_cases h₁ : ct.val < 6
  · exact receipt_row_09_band_02_t_01 cy hylo hyhi ct (by omega) h₁
  by_cases h₂ : ct.val < 14
  · exact receipt_row_09_band_02_t_02 cy hylo hyhi ct (by omega) h₂
  · exact receipt_row_09_band_02_t_03 cy hylo hyhi ct (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
