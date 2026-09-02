import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_18_fast : FastRowReceipt 18 := by decide +kernel

theorem receipt_row_18 : RowReceipt 18 :=
  fastRowReceipt_to_rowReceipt 18 receipt_row_18_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
