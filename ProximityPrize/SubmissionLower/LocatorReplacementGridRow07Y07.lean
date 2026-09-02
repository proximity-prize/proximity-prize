import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_y07 : FixedYReceipt 7 ⟨7, by decide⟩ 0 27 := by decide +kernel

theorem receipt_row_07_band_y07 : RowBandReceipt 7 7 8 :=
  fixedYReceipt_to_rowBand 7 ⟨7, by decide⟩ receipt_row_07_y07

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
