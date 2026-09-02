import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_09_y00_t00_24_fixed :
    FixedYReceipt 9 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_09_y00_t00_24 : RowTileReceipt 9 0 1 0 24 :=
  fixedYReceipt_to_rowTile 9 ⟨0, by decide⟩ 0 24 receipt_row_09_y00_t00_24_fixed

private theorem receipt_row_09_y00_t24_26_fixed :
    FixedYReceipt 9 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_09_y00_t24_26 : RowTileReceipt 9 0 1 24 26 :=
  fixedYReceipt_to_rowTile 9 ⟨0, by decide⟩ 24 26 receipt_row_09_y00_t24_26_fixed

private theorem receipt_row_09_y01_t00_24_fixed :
    FixedYReceipt 9 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_09_y01_t00_24 : RowTileReceipt 9 1 2 0 24 :=
  fixedYReceipt_to_rowTile 9 ⟨1, by decide⟩ 0 24 receipt_row_09_y01_t00_24_fixed

private theorem receipt_row_09_y01_t24_26_fixed :
    FixedYReceipt 9 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_09_y01_t24_26 : RowTileReceipt 9 1 2 24 26 :=
  fixedYReceipt_to_rowTile 9 ⟨1, by decide⟩ 24 26 receipt_row_09_y01_t24_26_fixed

private theorem receipt_row_09_y02_t00_08_fixed :
    FixedYReceipt 9 ⟨2, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_09_y02_t00_08 : RowTileReceipt 9 2 3 0 8 :=
  fixedYReceipt_to_rowTile 9 ⟨2, by decide⟩ 0 8 receipt_row_09_y02_t00_08_fixed

private theorem receipt_row_09_y02_t08_26_fixed :
    FixedYReceipt 9 ⟨2, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_09_y02_t08_26 : RowTileReceipt 9 2 3 8 26 :=
  fixedYReceipt_to_rowTile 9 ⟨2, by decide⟩ 8 26 receipt_row_09_y02_t08_26_fixed

private theorem receipt_row_09_y03_t00_01_fixed :
    FixedYReceipt 9 ⟨3, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_09_y03_t00_01 : RowTileReceipt 9 3 4 0 1 :=
  fixedYReceipt_to_rowTile 9 ⟨3, by decide⟩ 0 1 receipt_row_09_y03_t00_01_fixed

private theorem receipt_row_09_y03_t01_09_fixed :
    FixedYReceipt 9 ⟨3, by decide⟩ 1 9 := by decide +kernel

theorem receipt_row_09_y03_t01_09 : RowTileReceipt 9 3 4 1 9 :=
  fixedYReceipt_to_rowTile 9 ⟨3, by decide⟩ 1 9 receipt_row_09_y03_t01_09_fixed

private theorem receipt_row_09_y03_t09_26_fixed :
    FixedYReceipt 9 ⟨3, by decide⟩ 9 26 := by decide +kernel

theorem receipt_row_09_y03_t09_26 : RowTileReceipt 9 3 4 9 26 :=
  fixedYReceipt_to_rowTile 9 ⟨3, by decide⟩ 9 26 receipt_row_09_y03_t09_26_fixed

private theorem receipt_row_09_y04_t00_02_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_09_y04_t00_02 : RowTileReceipt 9 4 5 0 2 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 0 2 receipt_row_09_y04_t00_02_fixed

private theorem receipt_row_09_y04_t02_04_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_09_y04_t02_04 : RowTileReceipt 9 4 5 2 4 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 2 4 receipt_row_09_y04_t02_04_fixed

private theorem receipt_row_09_y04_t04_12_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 4 12 := by decide +kernel

theorem receipt_row_09_y04_t04_12 : RowTileReceipt 9 4 5 4 12 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 4 12 receipt_row_09_y04_t04_12_fixed

private theorem receipt_row_09_y04_t12_26_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_09_y04_t12_26 : RowTileReceipt 9 4 5 12 26 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 12 26 receipt_row_09_y04_t12_26_fixed

theorem receipt_row_09_band_05_07 : RowBandReceipt 9 5 7 := by decide +kernel

theorem receipt_row_09_band_07_09 : RowBandReceipt 9 7 9 := by decide +kernel

theorem receipt_row_09_band_09_11 : RowBandReceipt 9 9 11 := by decide +kernel

theorem receipt_row_09_band_11_13 : RowBandReceipt 9 11 13 := by decide +kernel

theorem receipt_row_09_band_13_15 : RowBandReceipt 9 13 15 := by decide +kernel

theorem receipt_row_09_band_15_17 : RowBandReceipt 9 15 17 := by decide +kernel

theorem receipt_row_09_band_17_19 : RowBandReceipt 9 17 19 := by decide +kernel

theorem receipt_row_09_band_19_23 : RowBandReceipt 9 19 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
