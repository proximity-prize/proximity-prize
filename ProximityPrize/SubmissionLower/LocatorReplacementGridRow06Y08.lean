import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_y08 : FixedYReceipt 6 ⟨8, by decide⟩ 0 29 := by decide +kernel

theorem receipt_row_06_band_y08 : RowBandReceipt 6 8 9 :=
  fixedYReceipt_to_rowBand 6 ⟨8, by decide⟩ receipt_row_06_y08

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
