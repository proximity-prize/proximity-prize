import ProximityPrize.SubmissionLower.LocatorReplacementGridRow16Seg01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_16_y_04_fixed :
    FixedYReceipt 16 ⟨4, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_16_y_04 : RowBandReceipt 16 4 5 :=
  fixedYReceipt_to_rowBand 16 ⟨4, by decide⟩ receipt_row_16_y_04_fixed

private theorem receipt_row_16_y_05_fixed :
    FixedYReceipt 16 ⟨5, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_16_y_05 : RowBandReceipt 16 5 6 :=
  fixedYReceipt_to_rowBand 16 ⟨5, by decide⟩ receipt_row_16_y_05_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
