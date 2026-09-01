import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Hot01Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_09_band_03_t_03_fixed : FixedYReceipt 9 ⟨5, by decide⟩ 12 16 := by decide +kernel
theorem receipt_row_09_band_03_t_03 : RowTileReceipt 9 5 6 12 16 :=
  fixedYReceipt_to_rowTile 9 ⟨5, by decide⟩ 12 16 receipt_row_09_band_03_t_03_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
