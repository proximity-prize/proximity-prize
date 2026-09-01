import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Hot00Single02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_band_03_a_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_05_band_03_a : RowBandReceipt 5 9 10 :=
  fixedYReceipt_to_rowBand 5 ⟨9, by decide⟩ receipt_row_05_band_03_a_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
