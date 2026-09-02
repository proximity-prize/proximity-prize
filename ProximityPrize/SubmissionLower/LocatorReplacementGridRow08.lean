import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_08_fast : FastRowReceipt 8 := by decide +kernel

theorem receipt_row_08 : RowReceipt 8 :=
  fastRowReceipt_to_rowReceipt 8 receipt_row_08_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
