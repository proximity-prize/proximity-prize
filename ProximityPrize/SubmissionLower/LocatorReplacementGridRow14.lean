import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_14_fast : FastRowReceipt 14 := by decide +kernel

theorem receipt_row_14 : RowReceipt 14 :=
  fastRowReceipt_to_rowReceipt 14 receipt_row_14_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
