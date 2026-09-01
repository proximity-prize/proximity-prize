import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Hot03Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_band_02_y_16_fixed :
    FixedYReceipt 4 ⟨16, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_04_band_02_y_16 : RowBandReceipt 4 16 17 :=
  fixedYReceipt_to_rowBand 4 ⟨16, by decide⟩ receipt_row_04_band_02_y_16_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
