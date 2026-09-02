import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem receipt_row_16_fast : FastRowReceipt 16 := by decide +kernel

theorem receipt_row_16 : RowReceipt 16 :=
  fastRowReceipt_to_rowReceipt 16 receipt_row_16_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
