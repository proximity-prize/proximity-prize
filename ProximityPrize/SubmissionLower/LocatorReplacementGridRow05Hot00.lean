import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_05_band_00 : RowBandReceipt 5 0 3 := by decide +kernel

theorem receipt_row_05_band_01 : RowBandReceipt 5 3 6 := by decide +kernel

theorem receipt_row_05_band_02 : RowBandReceipt 5 6 9 := by decide +kernel

private theorem receipt_row_05_band_03_a_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_05_band_03_a : RowBandReceipt 5 9 10 :=
  fixedYReceipt_to_rowBand 5 ⟨9, by decide⟩ receipt_row_05_band_03_a_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
