import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_05_fast : FastRowReceipt 5 := by decide +kernel

theorem receipt_row_05 : RowReceipt 5 :=
  fastRowReceipt_to_rowReceipt 5 receipt_row_05_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
