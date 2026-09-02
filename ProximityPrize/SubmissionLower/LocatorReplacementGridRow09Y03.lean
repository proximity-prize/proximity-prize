import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_y03 : FixedYReceipt 9 ⟨3, by decide⟩ 0 29 := by decide +kernel

theorem receipt_row_09_band_y03 : RowBandReceipt 9 3 4 :=
  fixedYReceipt_to_rowBand 9 ⟨3, by decide⟩ receipt_row_09_y03

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
