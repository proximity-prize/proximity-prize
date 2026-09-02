import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Hot00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_09_band_03_t_01_fixed : FixedYReceipt 9 ⟨5, by decide⟩ 4 8 := by decide +kernel
theorem receipt_row_09_band_03_t_01 : RowTileReceipt 9 5 6 4 8 :=
  fixedYReceipt_to_rowTile 9 ⟨5, by decide⟩ 4 8 receipt_row_09_band_03_t_01_fixed

private theorem receipt_row_09_band_03_t_02_fixed : FixedYReceipt 9 ⟨5, by decide⟩ 8 12 := by decide +kernel
theorem receipt_row_09_band_03_t_02 : RowTileReceipt 9 5 6 8 12 :=
  fixedYReceipt_to_rowTile 9 ⟨5, by decide⟩ 8 12 receipt_row_09_band_03_t_02_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
