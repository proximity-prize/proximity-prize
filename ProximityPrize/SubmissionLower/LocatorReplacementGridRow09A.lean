import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_band_00 : RowBandReceipt 9 0 3 := by decide +kernel

theorem receipt_row_09_band_01 : RowBandReceipt 9 3 4 := by decide +kernel

theorem receipt_row_09_band_02 : RowBandReceipt 9 4 5 := by decide +kernel

private theorem receipt_row_09_band_03_fixed :
    FixedYReceipt 9 ⟨5, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_09_band_03 : RowBandReceipt 9 5 6 :=
  fixedYReceipt_to_rowBand 9 ⟨5, by decide⟩ receipt_row_09_band_03_fixed

theorem receipt_row_09_band_04 : RowBandReceipt 9 6 7 := by decide +kernel

theorem receipt_row_09_band_05 : RowBandReceipt 9 7 8 := by decide +kernel

theorem receipt_row_09_band_06 : RowBandReceipt 9 8 9 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
