import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Hot01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_band_04_a_fixed :
    FixedYReceipt 5 ⟨12, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_05_band_04_a : RowBandReceipt 5 12 13 :=
  fixedYReceipt_to_rowBand 5 ⟨12, by decide⟩ receipt_row_05_band_04_a_fixed

private theorem receipt_row_05_band_04_b_fixed :
    FixedYReceipt 5 ⟨13, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_05_band_04_b : RowBandReceipt 5 13 14 :=
  fixedYReceipt_to_rowBand 5 ⟨13, by decide⟩ receipt_row_05_band_04_b_fixed

private theorem receipt_row_05_band_04_c_fixed :
    FixedYReceipt 5 ⟨14, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_05_band_04_c : RowBandReceipt 5 14 15 :=
  fixedYReceipt_to_rowBand 5 ⟨14, by decide⟩ receipt_row_05_band_04_c_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
