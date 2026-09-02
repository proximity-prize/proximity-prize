import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_05_y09 : FixedYReceipt 5 ⟨9, by decide⟩ 0 27 := by decide +kernel

theorem receipt_row_05_band_y09 : RowBandReceipt 5 9 10 :=
  fixedYReceipt_to_rowBand 5 ⟨9, by decide⟩ receipt_row_05_y09

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
