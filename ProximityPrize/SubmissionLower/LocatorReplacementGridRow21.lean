import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_21_fast : FastRowReceipt 21 := by decide +kernel

theorem receipt_row_21 : RowReceipt 21 :=
  fastRowReceipt_to_rowReceipt 21 receipt_row_21_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
