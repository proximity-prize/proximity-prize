import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03Band02Y16

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_band_02_y_17_fixed :
    FixedYReceipt 3 ⟨17, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_03_band_02_y_17 : RowBandReceipt 3 17 18 :=
  fixedYReceipt_to_rowBand 3 ⟨17, by decide⟩ receipt_row_03_band_02_y_17_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
