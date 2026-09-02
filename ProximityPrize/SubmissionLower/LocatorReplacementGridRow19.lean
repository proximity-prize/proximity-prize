import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_19_fast : FastRowReceipt 19 := by decide +kernel

theorem receipt_row_19 : RowReceipt 19 :=
  fastRowReceipt_to_rowReceipt 19 receipt_row_19_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
