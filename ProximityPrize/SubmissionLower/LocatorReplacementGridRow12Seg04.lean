import ProximityPrize.SubmissionLower.LocatorReplacementGridRow12Seg03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_12_y_08_fixed :
    FixedYReceipt 12 ⟨8, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_12_y_08 : RowBandReceipt 12 8 9 :=
  fixedYReceipt_to_rowBand 12 ⟨8, by decide⟩ receipt_row_12_y_08_fixed

private theorem receipt_row_12_y_09_fixed :
    FixedYReceipt 12 ⟨9, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_12_y_09 : RowBandReceipt 12 9 10 :=
  fixedYReceipt_to_rowBand 12 ⟨9, by decide⟩ receipt_row_12_y_09_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
