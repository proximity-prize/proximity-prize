import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Hot03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_09_band_07_t_02_fixed : FixedYReceipt 9 ⟨9, by decide⟩ 8 12 := by decide +kernel
theorem receipt_row_09_band_07_t_02 : RowTileReceipt 9 9 10 8 12 :=
  fixedYReceipt_to_rowTile 9 ⟨9, by decide⟩ 8 12 receipt_row_09_band_07_t_02_fixed

private theorem receipt_row_09_band_07_t_03_fixed : FixedYReceipt 9 ⟨9, by decide⟩ 12 16 := by decide +kernel
theorem receipt_row_09_band_07_t_03 : RowTileReceipt 9 9 10 12 16 :=
  fixedYReceipt_to_rowTile 9 ⟨9, by decide⟩ 12 16 receipt_row_09_band_07_t_03_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
