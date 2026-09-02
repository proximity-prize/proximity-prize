import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_y05 : FixedYReceipt 7 ⟨5, by decide⟩ 0 27 := by decide +kernel

theorem receipt_row_07_band_y05 : RowBandReceipt 7 5 6 :=
  fixedYReceipt_to_rowBand 7 ⟨5, by decide⟩ receipt_row_07_y05

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
