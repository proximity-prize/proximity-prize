import ProximityPrize.SubmissionLower.LocatorReplacementGridRow13Seg03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_13_y_08_fixed :
    FixedYReceipt 13 ⟨8, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_13_y_08 : RowBandReceipt 13 8 9 :=
  fixedYReceipt_to_rowBand 13 ⟨8, by decide⟩ receipt_row_13_y_08_fixed

private theorem receipt_row_13_y_09_fixed :
    FixedYReceipt 13 ⟨9, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_13_y_09 : RowBandReceipt 13 9 10 :=
  fixedYReceipt_to_rowBand 13 ⟨9, by decide⟩ receipt_row_13_y_09_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
