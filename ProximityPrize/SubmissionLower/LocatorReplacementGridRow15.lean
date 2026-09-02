import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_15_fast : FastRowReceipt 15 := by decide +kernel

theorem receipt_row_15 : RowReceipt 15 :=
  fastRowReceipt_to_rowReceipt 15 receipt_row_15_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
