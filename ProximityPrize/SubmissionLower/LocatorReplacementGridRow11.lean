import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_11_fast : FastRowReceipt 11 := by decide +kernel

theorem receipt_row_11 : RowReceipt 11 :=
  fastRowReceipt_to_rowReceipt 11 receipt_row_11_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
