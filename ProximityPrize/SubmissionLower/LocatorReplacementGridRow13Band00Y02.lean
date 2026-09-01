import ProximityPrize.SubmissionLower.LocatorReplacementGridRow13Band00Y02T01
namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_row_13_band_00_y_02 : RowBandReceipt 13 2 3 := by
  intro cy hylo hyhi ct
  by_cases h : ct.val < 11
  · exact receipt_row_13_band_00_y_02_t_00 cy hylo hyhi ct (Nat.zero_le _) h
  · exact receipt_row_13_band_00_y_02_t_01 cy hylo hyhi ct (by omega) (by omega)
end ProximityPrize.SubmissionLower.LocatorReplacementGridData
