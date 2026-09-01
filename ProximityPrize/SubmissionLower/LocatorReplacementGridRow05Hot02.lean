import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Hot02Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_band_04_c_fixed :
    FixedYReceipt 5 ⟨14, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_05_band_04_c : RowBandReceipt 5 14 15 :=
  fixedYReceipt_to_rowBand 5 ⟨14, by decide⟩ receipt_row_05_band_04_c_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
