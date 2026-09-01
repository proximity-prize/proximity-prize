import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10Band08T01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_10_band_08 : RowBandReceipt 10 10 11 := by
  intro cy hylo hyhi ct
  by_cases h : ct.val < 11
  · exact receipt_row_10_band_08_t_00 cy hylo hyhi ct (Nat.zero_le _) h
  · exact receipt_row_10_band_08_t_01 cy hylo hyhi ct (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
