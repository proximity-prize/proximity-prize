import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_y04 : FixedYReceipt 7 ⟨4, by decide⟩ 0 27 := by decide +kernel

theorem receipt_row_07_band_y04 : RowBandReceipt 7 4 5 :=
  fixedYReceipt_to_rowBand 7 ⟨4, by decide⟩ receipt_row_07_y04

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
