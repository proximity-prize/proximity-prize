import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_12_fast : FastRowReceipt 12 := by decide +kernel

theorem receipt_row_12 : RowReceipt 12 :=
  fastRowReceipt_to_rowReceipt 12 receipt_row_12_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
