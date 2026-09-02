import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_y05 : FixedYReceipt 6 ⟨5, by decide⟩ 0 30 := by decide +kernel

theorem receipt_row_06_band_y05 : RowBandReceipt 6 5 6 :=
  fixedYReceipt_to_rowBand 6 ⟨5, by decide⟩ receipt_row_06_y05

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
