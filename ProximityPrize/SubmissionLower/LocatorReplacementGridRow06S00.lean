import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_y00_t00_24_fixed :
    FixedYReceipt 6 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_y00_t00_24 : RowTileReceipt 6 0 1 0 24 :=
  fixedYReceipt_to_rowTile 6 ⟨0, by decide⟩ 0 24 receipt_row_06_y00_t00_24_fixed

private theorem receipt_row_06_y00_t24_26_fixed :
    FixedYReceipt 6 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_06_y00_t24_26 : RowTileReceipt 6 0 1 24 26 :=
  fixedYReceipt_to_rowTile 6 ⟨0, by decide⟩ 24 26 receipt_row_06_y00_t24_26_fixed

private theorem receipt_row_06_y01_t00_24_fixed :
    FixedYReceipt 6 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_y01_t00_24 : RowTileReceipt 6 1 2 0 24 :=
  fixedYReceipt_to_rowTile 6 ⟨1, by decide⟩ 0 24 receipt_row_06_y01_t00_24_fixed

private theorem receipt_row_06_y01_t24_26_fixed :
    FixedYReceipt 6 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_06_y01_t24_26 : RowTileReceipt 6 1 2 24 26 :=
  fixedYReceipt_to_rowTile 6 ⟨1, by decide⟩ 24 26 receipt_row_06_y01_t24_26_fixed

private theorem receipt_row_06_y02_t00_24_fixed :
    FixedYReceipt 6 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_y02_t00_24 : RowTileReceipt 6 2 3 0 24 :=
  fixedYReceipt_to_rowTile 6 ⟨2, by decide⟩ 0 24 receipt_row_06_y02_t00_24_fixed

private theorem receipt_row_06_y02_t24_26_fixed :
    FixedYReceipt 6 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_06_y02_t24_26 : RowTileReceipt 6 2 3 24 26 :=
  fixedYReceipt_to_rowTile 6 ⟨2, by decide⟩ 24 26 receipt_row_06_y02_t24_26_fixed

private theorem receipt_row_06_y03_t00_24_fixed :
    FixedYReceipt 6 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_y03_t00_24 : RowTileReceipt 6 3 4 0 24 :=
  fixedYReceipt_to_rowTile 6 ⟨3, by decide⟩ 0 24 receipt_row_06_y03_t00_24_fixed

private theorem receipt_row_06_y03_t24_26_fixed :
    FixedYReceipt 6 ⟨3, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_06_y03_t24_26 : RowTileReceipt 6 3 4 24 26 :=
  fixedYReceipt_to_rowTile 6 ⟨3, by decide⟩ 24 26 receipt_row_06_y03_t24_26_fixed

private theorem receipt_row_06_y04_t00_08_fixed :
    FixedYReceipt 6 ⟨4, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_06_y04_t00_08 : RowTileReceipt 6 4 5 0 8 :=
  fixedYReceipt_to_rowTile 6 ⟨4, by decide⟩ 0 8 receipt_row_06_y04_t00_08_fixed

private theorem receipt_row_06_y04_t08_26_fixed :
    FixedYReceipt 6 ⟨4, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_06_y04_t08_26 : RowTileReceipt 6 4 5 8 26 :=
  fixedYReceipt_to_rowTile 6 ⟨4, by decide⟩ 8 26 receipt_row_06_y04_t08_26_fixed

private theorem receipt_row_06_y05_t00_04_fixed :
    FixedYReceipt 6 ⟨5, by decide⟩ 0 4 := by decide +kernel

theorem receipt_row_06_y05_t00_04 : RowTileReceipt 6 5 6 0 4 :=
  fixedYReceipt_to_rowTile 6 ⟨5, by decide⟩ 0 4 receipt_row_06_y05_t00_04_fixed

private theorem receipt_row_06_y05_t04_26_fixed :
    FixedYReceipt 6 ⟨5, by decide⟩ 4 26 := by decide +kernel

theorem receipt_row_06_y05_t04_26 : RowTileReceipt 6 5 6 4 26 :=
  fixedYReceipt_to_rowTile 6 ⟨5, by decide⟩ 4 26 receipt_row_06_y05_t04_26_fixed

private theorem receipt_row_06_y06_t00_01_fixed :
    FixedYReceipt 6 ⟨6, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_06_y06_t00_01 : RowTileReceipt 6 6 7 0 1 :=
  fixedYReceipt_to_rowTile 6 ⟨6, by decide⟩ 0 1 receipt_row_06_y06_t00_01_fixed

private theorem receipt_row_06_y06_t01_03_fixed :
    FixedYReceipt 6 ⟨6, by decide⟩ 1 3 := by decide +kernel

theorem receipt_row_06_y06_t01_03 : RowTileReceipt 6 6 7 1 3 :=
  fixedYReceipt_to_rowTile 6 ⟨6, by decide⟩ 1 3 receipt_row_06_y06_t01_03_fixed

private theorem receipt_row_06_y06_t03_26_fixed :
    FixedYReceipt 6 ⟨6, by decide⟩ 3 26 := by decide +kernel

theorem receipt_row_06_y06_t03_26 : RowTileReceipt 6 6 7 3 26 :=
  fixedYReceipt_to_rowTile 6 ⟨6, by decide⟩ 3 26 receipt_row_06_y06_t03_26_fixed

private theorem receipt_row_06_y07_t00_01_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_06_y07_t00_01 : RowTileReceipt 6 7 8 0 1 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 0 1 receipt_row_06_y07_t00_01_fixed

private theorem receipt_row_06_y07_t01_03_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 1 3 := by decide +kernel

theorem receipt_row_06_y07_t01_03 : RowTileReceipt 6 7 8 1 3 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 1 3 receipt_row_06_y07_t01_03_fixed

private theorem receipt_row_06_y07_t03_05_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 3 5 := by decide +kernel

theorem receipt_row_06_y07_t03_05 : RowTileReceipt 6 7 8 3 5 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 3 5 receipt_row_06_y07_t03_05_fixed

private theorem receipt_row_06_y07_t05_07_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 5 7 := by decide +kernel

theorem receipt_row_06_y07_t05_07 : RowTileReceipt 6 7 8 5 7 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 5 7 receipt_row_06_y07_t05_07_fixed

private theorem receipt_row_06_y07_t07_15_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 7 15 := by decide +kernel

theorem receipt_row_06_y07_t07_15 : RowTileReceipt 6 7 8 7 15 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 7 15 receipt_row_06_y07_t07_15_fixed

private theorem receipt_row_06_y07_t15_26_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 15 26 := by decide +kernel

theorem receipt_row_06_y07_t15_26 : RowTileReceipt 6 7 8 15 26 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 15 26 receipt_row_06_y07_t15_26_fixed

private theorem receipt_row_06_y08_t00_01_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_06_y08_t00_01 : RowTileReceipt 6 8 9 0 1 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 0 1 receipt_row_06_y08_t00_01_fixed

private theorem receipt_row_06_y08_t01_02_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 1 2 := by decide +kernel

theorem receipt_row_06_y08_t01_02 : RowTileReceipt 6 8 9 1 2 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 1 2 receipt_row_06_y08_t01_02_fixed

private theorem receipt_row_06_y08_t02_03_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 2 3 := by decide +kernel

theorem receipt_row_06_y08_t02_03 : RowTileReceipt 6 8 9 2 3 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 2 3 receipt_row_06_y08_t02_03_fixed

private theorem receipt_row_06_y08_t03_05_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 3 5 := by decide +kernel

theorem receipt_row_06_y08_t03_05 : RowTileReceipt 6 8 9 3 5 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 3 5 receipt_row_06_y08_t03_05_fixed

private theorem receipt_row_06_y08_t05_07_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 5 7 := by decide +kernel

theorem receipt_row_06_y08_t05_07 : RowTileReceipt 6 8 9 5 7 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 5 7 receipt_row_06_y08_t05_07_fixed

private theorem receipt_row_06_y08_t07_09_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 7 9 := by decide +kernel

theorem receipt_row_06_y08_t07_09 : RowTileReceipt 6 8 9 7 9 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 7 9 receipt_row_06_y08_t07_09_fixed

private theorem receipt_row_06_y08_t09_11_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 9 11 := by decide +kernel

theorem receipt_row_06_y08_t09_11 : RowTileReceipt 6 8 9 9 11 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 9 11 receipt_row_06_y08_t09_11_fixed

private theorem receipt_row_06_y08_t11_13_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 11 13 := by decide +kernel

theorem receipt_row_06_y08_t11_13 : RowTileReceipt 6 8 9 11 13 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 11 13 receipt_row_06_y08_t11_13_fixed

private theorem receipt_row_06_y08_t13_15_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 13 15 := by decide +kernel

theorem receipt_row_06_y08_t13_15 : RowTileReceipt 6 8 9 13 15 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 13 15 receipt_row_06_y08_t13_15_fixed

private theorem receipt_row_06_y08_t15_17_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 15 17 := by decide +kernel

theorem receipt_row_06_y08_t15_17 : RowTileReceipt 6 8 9 15 17 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 15 17 receipt_row_06_y08_t15_17_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
