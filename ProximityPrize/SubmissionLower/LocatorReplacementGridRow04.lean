import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_04_fast : FastRowReceipt 4 := by decide +kernel

theorem receipt_row_04 : RowReceipt 4 :=
  fastRowReceipt_to_rowReceipt 4 receipt_row_04_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
