import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_20_fast : FastRowReceipt 20 := by decide +kernel

theorem receipt_row_20 : RowReceipt 20 :=
  fastRowReceipt_to_rowReceipt 20 receipt_row_20_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
