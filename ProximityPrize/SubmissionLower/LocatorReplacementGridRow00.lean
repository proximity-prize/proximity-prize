import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_00_fast : FastRowReceipt 0 := by decide +kernel

theorem receipt_row_00 : RowReceipt 0 :=
  fastRowReceipt_to_rowReceipt 0 receipt_row_00_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
