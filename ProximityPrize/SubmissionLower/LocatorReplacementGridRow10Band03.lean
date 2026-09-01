import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10Band03T01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_10_band_03 : RowBandReceipt 10 5 6 := by
  intro cy hylo hyhi ct
  by_cases h : ct.val < 11
  · exact receipt_row_10_band_03_t_00 cy hylo hyhi ct (Nat.zero_le _) h
  · exact receipt_row_10_band_03_t_01 cy hylo hyhi ct (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
