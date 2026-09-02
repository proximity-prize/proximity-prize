import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_y06 : FixedYReceipt 6 ⟨6, by decide⟩ 0 27 := by decide +kernel

theorem receipt_row_06_band_y06 : RowBandReceipt 6 6 7 :=
  fixedYReceipt_to_rowBand 6 ⟨6, by decide⟩ receipt_row_06_y06

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
