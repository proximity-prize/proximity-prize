import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_03_fast : FastRowReceipt 3 := by decide +kernel

theorem receipt_row_03 : RowReceipt 3 :=
  fastRowReceipt_to_rowReceipt 3 receipt_row_03_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
