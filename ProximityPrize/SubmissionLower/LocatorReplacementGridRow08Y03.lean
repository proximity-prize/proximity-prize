import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_y03 : FixedYReceipt 8 ⟨3, by decide⟩ 0 27 := by decide +kernel

theorem receipt_row_08_band_y03 : RowBandReceipt 8 3 4 :=
  fixedYReceipt_to_rowBand 8 ⟨3, by decide⟩ receipt_row_08_y03

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
