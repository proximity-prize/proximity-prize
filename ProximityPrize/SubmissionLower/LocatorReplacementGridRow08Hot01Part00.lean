import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_03_t_03 : RowTileReceipt 8 5 6 3 7 := by decide +kernel

theorem receipt_row_08_band_03_t_04 : RowTileReceipt 8 5 6 7 11 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
