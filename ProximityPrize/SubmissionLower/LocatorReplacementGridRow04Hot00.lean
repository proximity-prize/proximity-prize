import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Hot00Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_band_01_y_08_fixed :
    FixedYReceipt 4 ⟨8, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_04_band_01_y_08 : RowBandReceipt 4 8 9 :=
  fixedYReceipt_to_rowBand 4 ⟨8, by decide⟩ receipt_row_04_band_01_y_08_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
