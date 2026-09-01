import ProximityPrize.SubmissionLower.LocatorReplacementGridRow01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_02_fast : FastRowReceipt 2 := by decide +kernel

theorem receipt_row_02 : RowReceipt 2 :=
  fastRowReceipt_to_rowReceipt 2 receipt_row_02_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
