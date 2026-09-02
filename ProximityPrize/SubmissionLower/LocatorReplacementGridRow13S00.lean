import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_13_y00_t00_24_fixed :
    FixedYReceipt 13 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_13_y00_t00_24 : RowTileReceipt 13 0 1 0 24 :=
  fixedYReceipt_to_rowTile 13 ⟨0, by decide⟩ 0 24 receipt_row_13_y00_t00_24_fixed

private theorem receipt_row_13_y00_t24_26_fixed :
    FixedYReceipt 13 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_13_y00_t24_26 : RowTileReceipt 13 0 1 24 26 :=
  fixedYReceipt_to_rowTile 13 ⟨0, by decide⟩ 24 26 receipt_row_13_y00_t24_26_fixed

private theorem receipt_row_13_y01_t00_24_fixed :
    FixedYReceipt 13 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_13_y01_t00_24 : RowTileReceipt 13 1 2 0 24 :=
  fixedYReceipt_to_rowTile 13 ⟨1, by decide⟩ 0 24 receipt_row_13_y01_t00_24_fixed

private theorem receipt_row_13_y01_t24_26_fixed :
    FixedYReceipt 13 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_13_y01_t24_26 : RowTileReceipt 13 1 2 24 26 :=
  fixedYReceipt_to_rowTile 13 ⟨1, by decide⟩ 24 26 receipt_row_13_y01_t24_26_fixed

private theorem receipt_row_13_y02_t00_24_fixed :
    FixedYReceipt 13 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_13_y02_t00_24 : RowTileReceipt 13 2 3 0 24 :=
  fixedYReceipt_to_rowTile 13 ⟨2, by decide⟩ 0 24 receipt_row_13_y02_t00_24_fixed

private theorem receipt_row_13_y02_t24_26_fixed :
    FixedYReceipt 13 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_13_y02_t24_26 : RowTileReceipt 13 2 3 24 26 :=
  fixedYReceipt_to_rowTile 13 ⟨2, by decide⟩ 24 26 receipt_row_13_y02_t24_26_fixed

theorem receipt_row_13_band_03_05 : RowBandReceipt 13 3 5 := by decide +kernel

theorem receipt_row_13_band_05_07 : RowBandReceipt 13 5 7 := by decide +kernel

theorem receipt_row_13_band_07_09 : RowBandReceipt 13 7 9 := by decide +kernel

theorem receipt_row_13_band_09_11 : RowBandReceipt 13 9 11 := by decide +kernel

theorem receipt_row_13_band_11_13 : RowBandReceipt 13 11 13 := by decide +kernel

theorem receipt_row_13_band_13_15 : RowBandReceipt 13 13 15 := by decide +kernel

theorem receipt_row_13_band_15_17 : RowBandReceipt 13 15 17 := by decide +kernel

theorem receipt_row_13_band_17_19 : RowBandReceipt 13 17 19 := by decide +kernel

theorem receipt_row_13_band_19_23 : RowBandReceipt 13 19 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
