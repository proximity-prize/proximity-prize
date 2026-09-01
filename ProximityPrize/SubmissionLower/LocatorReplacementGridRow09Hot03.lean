import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Hot02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_band_05 : RowBandReceipt 9 7 8 := by decide +kernel

theorem receipt_row_09_band_06 : RowBandReceipt 9 8 9 := by decide +kernel

private theorem receipt_row_09_band_07_t_00_fixed : FixedYReceipt 9 ⟨9, by decide⟩ 0 4 := by decide +kernel
theorem receipt_row_09_band_07_t_00 : RowTileReceipt 9 9 10 0 4 :=
  fixedYReceipt_to_rowTile 9 ⟨9, by decide⟩ 0 4 receipt_row_09_band_07_t_00_fixed

private theorem receipt_row_09_band_07_t_01_fixed : FixedYReceipt 9 ⟨9, by decide⟩ 4 8 := by decide +kernel
theorem receipt_row_09_band_07_t_01 : RowTileReceipt 9 9 10 4 8 :=
  fixedYReceipt_to_rowTile 9 ⟨9, by decide⟩ 4 8 receipt_row_09_band_07_t_01_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
