import ProximityPrize.SubmissionLower.LocatorReplacementGridRow18Seg03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_18_y_08_fixed :
    FixedYReceipt 18 ⟨8, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_18_y_08 : RowBandReceipt 18 8 9 :=
  fixedYReceipt_to_rowBand 18 ⟨8, by decide⟩ receipt_row_18_y_08_fixed

private theorem receipt_row_18_y_09_fixed :
    FixedYReceipt 18 ⟨9, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_18_y_09 : RowBandReceipt 18 9 10 :=
  fixedYReceipt_to_rowBand 18 ⟨9, by decide⟩ receipt_row_18_y_09_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
