import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_y02 : FixedYReceipt 9 ⟨2, by decide⟩ 0 27 := by decide +kernel

theorem receipt_row_09_band_y02 : RowBandReceipt 9 2 3 :=
  fixedYReceipt_to_rowBand 9 ⟨2, by decide⟩ receipt_row_09_y02

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
