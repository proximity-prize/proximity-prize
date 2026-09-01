import ProximityPrize.SubmissionLower.LocatorReplacementGridRow11Seg01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_11_y_04_fixed :
    FixedYReceipt 11 ⟨4, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_11_y_04 : RowBandReceipt 11 4 5 :=
  fixedYReceipt_to_rowBand 11 ⟨4, by decide⟩ receipt_row_11_y_04_fixed

private theorem receipt_row_11_y_05_fixed :
    FixedYReceipt 11 ⟨5, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_11_y_05 : RowBandReceipt 11 5 6 :=
  fixedYReceipt_to_rowBand 11 ⟨5, by decide⟩ receipt_row_11_y_05_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
