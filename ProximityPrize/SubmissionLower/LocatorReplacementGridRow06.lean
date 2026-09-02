import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_06_fast : FastRowReceipt 6 := by decide +kernel

theorem receipt_row_06 : RowReceipt 6 :=
  fastRowReceipt_to_rowReceipt 6 receipt_row_06_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
