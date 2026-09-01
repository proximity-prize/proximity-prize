import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Hot03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_band_02_y_17_fixed :
    FixedYReceipt 4 ⟨17, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_04_band_02_y_17 : RowBandReceipt 4 17 18 :=
  fixedYReceipt_to_rowBand 4 ⟨17, by decide⟩ receipt_row_04_band_02_y_17_fixed

private theorem receipt_row_04_band_02_y_18_fixed :
    FixedYReceipt 4 ⟨18, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_04_band_02_y_18 : RowBandReceipt 4 18 19 :=
  fixedYReceipt_to_rowBand 4 ⟨18, by decide⟩ receipt_row_04_band_02_y_18_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
