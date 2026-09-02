import ProximityPrize.SubmissionLower.LocatorReplacementGridRow14Seg03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_14_y_08_fixed :
    FixedYReceipt 14 ⟨8, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_14_y_08 : RowBandReceipt 14 8 9 :=
  fixedYReceipt_to_rowBand 14 ⟨8, by decide⟩ receipt_row_14_y_08_fixed

private theorem receipt_row_14_y_09_fixed :
    FixedYReceipt 14 ⟨9, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_14_y_09 : RowBandReceipt 14 9 10 :=
  fixedYReceipt_to_rowBand 14 ⟨9, by decide⟩ receipt_row_14_y_09_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
