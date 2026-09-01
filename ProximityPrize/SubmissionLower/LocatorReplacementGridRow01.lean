import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_01 : RowReceipt 1 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
