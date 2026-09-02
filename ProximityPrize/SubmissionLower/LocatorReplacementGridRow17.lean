import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_17_fast : FastRowReceipt 17 := by decide +kernel

theorem receipt_row_17 : RowReceipt 17 :=
  fastRowReceipt_to_rowReceipt 17 receipt_row_17_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
