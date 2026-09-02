import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_15_17 : RowBandReceipt 8 15 17 := by decide +kernel

theorem receipt_row_08_band_17_19 : RowBandReceipt 8 17 19 := by decide +kernel

theorem receipt_row_08_band_19_23 : RowBandReceipt 8 19 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
