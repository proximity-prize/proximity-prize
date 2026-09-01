import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Hot04Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_band_02_y_19_fixed :
    FixedYReceipt 4 ⟨19, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_04_band_02_y_19 : RowBandReceipt 4 19 20 :=
  fixedYReceipt_to_rowBand 4 ⟨19, by decide⟩ receipt_row_04_band_02_y_19_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
