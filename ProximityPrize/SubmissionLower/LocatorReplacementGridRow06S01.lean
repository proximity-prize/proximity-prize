import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_15_17 : RowBandReceipt 6 15 17 := by decide +kernel

theorem receipt_row_06_band_17_19 : RowBandReceipt 6 17 19 := by decide +kernel

theorem receipt_row_06_band_19_21 : RowBandReceipt 6 19 21 := by decide +kernel

theorem receipt_row_06_band_21_23 : RowBandReceipt 6 21 23 := by decide +kernel

theorem receipt_row_06_band_23_25 : RowBandReceipt 6 23 25 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
