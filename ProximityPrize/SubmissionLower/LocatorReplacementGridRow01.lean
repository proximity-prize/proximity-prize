import ProximityPrize.SubmissionLower.LocatorReplacementGridRow00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_01_fast : FastRowReceipt 1 := by decide +kernel

theorem receipt_row_01 : RowReceipt 1 :=
  fastRowReceipt_to_rowReceipt 1 receipt_row_01_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
