import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Band04T03A
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Band04T03B

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_04_t_03 : RowTileReceipt 8 6 7 3 8 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h : ct.val < 5
  · exact receipt_row_08_band_04_t_03_a cy hylo hyhi ct htlo h
  · exact receipt_row_08_band_04_t_03_b cy hylo hyhi ct (by omega) hthi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
