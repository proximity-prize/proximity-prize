import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_y06 : FixedYReceipt 8 ⟨6, by decide⟩ 0 29 := by decide +kernel

theorem receipt_row_08_band_y06 : RowBandReceipt 8 6 7 :=
  fixedYReceipt_to_rowBand 8 ⟨6, by decide⟩ receipt_row_08_y06

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
