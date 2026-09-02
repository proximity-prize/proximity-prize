import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_y04 : FixedYReceipt 8 ⟨4, by decide⟩ 0 30 := by decide +kernel

theorem receipt_row_08_band_y04 : RowBandReceipt 8 4 5 :=
  fixedYReceipt_to_rowBand 8 ⟨4, by decide⟩ receipt_row_08_y04

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
