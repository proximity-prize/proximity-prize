import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09A

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_09_band_03_fixed :
    FixedYReceipt 9 ⟨5, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_09_band_03 : RowBandReceipt 9 5 6 :=
  fixedYReceipt_to_rowBand 9 ⟨5, by decide⟩ receipt_row_09_band_03_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
