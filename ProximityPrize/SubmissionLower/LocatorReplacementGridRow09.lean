import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_09_fast : FastRowReceipt 9 := by decide +kernel

theorem receipt_row_09 : RowReceipt 9 :=
  fastRowReceipt_to_rowReceipt 9 receipt_row_09_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
