import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_y06 : FixedYReceipt 7 ⟨6, by decide⟩ 0 29 := by decide +kernel

theorem receipt_row_07_band_y06 : RowBandReceipt 7 6 7 :=
  fixedYReceipt_to_rowBand 7 ⟨6, by decide⟩ receipt_row_07_y06

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
