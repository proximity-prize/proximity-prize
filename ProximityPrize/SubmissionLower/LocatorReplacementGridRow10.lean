import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_10_fast : FastRowReceipt 10 := by decide +kernel

theorem receipt_row_10 : RowReceipt 10 :=
  fastRowReceipt_to_rowReceipt 10 receipt_row_10_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
