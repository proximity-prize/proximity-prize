import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_13_fast : FastRowReceipt 13 := by decide +kernel

theorem receipt_row_13 : RowReceipt 13 :=
  fastRowReceipt_to_rowReceipt 13 receipt_row_13_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
