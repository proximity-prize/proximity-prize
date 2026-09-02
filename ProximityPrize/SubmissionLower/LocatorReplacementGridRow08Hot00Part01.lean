import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot00Part00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_02 : RowBandReceipt 8 4 5 := by decide +kernel

theorem receipt_row_08_band_03_t_00 : RowTileReceipt 8 5 6 0 1 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
