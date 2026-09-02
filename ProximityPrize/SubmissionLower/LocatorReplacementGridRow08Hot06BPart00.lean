import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot06

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_tail_a : RowBandReceipt 8 12 14 := by decide +kernel

theorem receipt_row_08_band_tail_b : RowBandReceipt 8 14 16 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
