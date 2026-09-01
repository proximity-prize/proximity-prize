import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Hot00Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_band_02 : RowBandReceipt 9 4 5 := by decide +kernel

private theorem receipt_row_09_band_03_t_00_fixed : FixedYReceipt 9 ⟨5, by decide⟩ 0 4 := by decide +kernel
theorem receipt_row_09_band_03_t_00 : RowTileReceipt 9 5 6 0 4 :=
  fixedYReceipt_to_rowTile 9 ⟨5, by decide⟩ 0 4 receipt_row_09_band_03_t_00_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
