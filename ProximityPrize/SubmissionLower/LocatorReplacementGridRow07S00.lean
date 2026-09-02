import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y00_t00_24_fixed :
    FixedYReceipt 7 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_07_y00_t00_24 : RowTileReceipt 7 0 1 0 24 :=
  fixedYReceipt_to_rowTile 7 ⟨0, by decide⟩ 0 24 receipt_row_07_y00_t00_24_fixed

private theorem receipt_row_07_y00_t24_26_fixed :
    FixedYReceipt 7 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_07_y00_t24_26 : RowTileReceipt 7 0 1 24 26 :=
  fixedYReceipt_to_rowTile 7 ⟨0, by decide⟩ 24 26 receipt_row_07_y00_t24_26_fixed

private theorem receipt_row_07_y01_t00_24_fixed :
    FixedYReceipt 7 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_07_y01_t00_24 : RowTileReceipt 7 1 2 0 24 :=
  fixedYReceipt_to_rowTile 7 ⟨1, by decide⟩ 0 24 receipt_row_07_y01_t00_24_fixed

private theorem receipt_row_07_y01_t24_26_fixed :
    FixedYReceipt 7 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_07_y01_t24_26 : RowTileReceipt 7 1 2 24 26 :=
  fixedYReceipt_to_rowTile 7 ⟨1, by decide⟩ 24 26 receipt_row_07_y01_t24_26_fixed

private theorem receipt_row_07_y02_t00_24_fixed :
    FixedYReceipt 7 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_07_y02_t00_24 : RowTileReceipt 7 2 3 0 24 :=
  fixedYReceipt_to_rowTile 7 ⟨2, by decide⟩ 0 24 receipt_row_07_y02_t00_24_fixed

private theorem receipt_row_07_y02_t24_26_fixed :
    FixedYReceipt 7 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_07_y02_t24_26 : RowTileReceipt 7 2 3 24 26 :=
  fixedYReceipt_to_rowTile 7 ⟨2, by decide⟩ 24 26 receipt_row_07_y02_t24_26_fixed

private theorem receipt_row_07_y03_t00_08_fixed :
    FixedYReceipt 7 ⟨3, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_07_y03_t00_08 : RowTileReceipt 7 3 4 0 8 :=
  fixedYReceipt_to_rowTile 7 ⟨3, by decide⟩ 0 8 receipt_row_07_y03_t00_08_fixed

private theorem receipt_row_07_y03_t08_26_fixed :
    FixedYReceipt 7 ⟨3, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_07_y03_t08_26 : RowTileReceipt 7 3 4 8 26 :=
  fixedYReceipt_to_rowTile 7 ⟨3, by decide⟩ 8 26 receipt_row_07_y03_t08_26_fixed

private theorem receipt_row_07_y04_t00_04_fixed :
    FixedYReceipt 7 ⟨4, by decide⟩ 0 4 := by decide +kernel

theorem receipt_row_07_y04_t00_04 : RowTileReceipt 7 4 5 0 4 :=
  fixedYReceipt_to_rowTile 7 ⟨4, by decide⟩ 0 4 receipt_row_07_y04_t00_04_fixed

private theorem receipt_row_07_y04_t04_26_fixed :
    FixedYReceipt 7 ⟨4, by decide⟩ 4 26 := by decide +kernel

theorem receipt_row_07_y04_t04_26 : RowTileReceipt 7 4 5 4 26 :=
  fixedYReceipt_to_rowTile 7 ⟨4, by decide⟩ 4 26 receipt_row_07_y04_t04_26_fixed

private theorem receipt_row_07_y05_t00_01_fixed :
    FixedYReceipt 7 ⟨5, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_07_y05_t00_01 : RowTileReceipt 7 5 6 0 1 :=
  fixedYReceipt_to_rowTile 7 ⟨5, by decide⟩ 0 1 receipt_row_07_y05_t00_01_fixed

private theorem receipt_row_07_y05_t01_03_fixed :
    FixedYReceipt 7 ⟨5, by decide⟩ 1 3 := by decide +kernel

theorem receipt_row_07_y05_t01_03 : RowTileReceipt 7 5 6 1 3 :=
  fixedYReceipt_to_rowTile 7 ⟨5, by decide⟩ 1 3 receipt_row_07_y05_t01_03_fixed

private theorem receipt_row_07_y05_t03_26_fixed :
    FixedYReceipt 7 ⟨5, by decide⟩ 3 26 := by decide +kernel

theorem receipt_row_07_y05_t03_26 : RowTileReceipt 7 5 6 3 26 :=
  fixedYReceipt_to_rowTile 7 ⟨5, by decide⟩ 3 26 receipt_row_07_y05_t03_26_fixed

private theorem receipt_row_07_y06_t00_01_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_07_y06_t00_01 : RowTileReceipt 7 6 7 0 1 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 0 1 receipt_row_07_y06_t00_01_fixed

private theorem receipt_row_07_y06_t01_02_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 1 2 := by decide +kernel

theorem receipt_row_07_y06_t01_02 : RowTileReceipt 7 6 7 1 2 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 1 2 receipt_row_07_y06_t01_02_fixed

private theorem receipt_row_07_y06_t02_04_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_07_y06_t02_04 : RowTileReceipt 7 6 7 2 4 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 2 4 receipt_row_07_y06_t02_04_fixed

private theorem receipt_row_07_y06_t04_06_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 4 6 := by decide +kernel

theorem receipt_row_07_y06_t04_06 : RowTileReceipt 7 6 7 4 6 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 4 6 receipt_row_07_y06_t04_06_fixed

private theorem receipt_row_07_y06_t06_08_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 6 8 := by decide +kernel

theorem receipt_row_07_y06_t06_08 : RowTileReceipt 7 6 7 6 8 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 6 8 receipt_row_07_y06_t06_08_fixed

private theorem receipt_row_07_y06_t08_10_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 8 10 := by decide +kernel

theorem receipt_row_07_y06_t08_10 : RowTileReceipt 7 6 7 8 10 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 8 10 receipt_row_07_y06_t08_10_fixed

private theorem receipt_row_07_y06_t10_18_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 10 18 := by decide +kernel

theorem receipt_row_07_y06_t10_18 : RowTileReceipt 7 6 7 10 18 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 10 18 receipt_row_07_y06_t10_18_fixed

private theorem receipt_row_07_y06_t18_26_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 18 26 := by decide +kernel

theorem receipt_row_07_y06_t18_26 : RowTileReceipt 7 6 7 18 26 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 18 26 receipt_row_07_y06_t18_26_fixed

private theorem receipt_row_07_y07_t00_01_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_07_y07_t00_01 : RowTileReceipt 7 7 8 0 1 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 0 1 receipt_row_07_y07_t00_01_fixed

private theorem receipt_row_07_y07_t01_02_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 1 2 := by decide +kernel

theorem receipt_row_07_y07_t01_02 : RowTileReceipt 7 7 8 1 2 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 1 2 receipt_row_07_y07_t01_02_fixed

private theorem receipt_row_07_y07_t02_03_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 2 3 := by decide +kernel

theorem receipt_row_07_y07_t02_03 : RowTileReceipt 7 7 8 2 3 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 2 3 receipt_row_07_y07_t02_03_fixed

private theorem receipt_row_07_y07_t03_04_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 3 4 := by decide +kernel

theorem receipt_row_07_y07_t03_04 : RowTileReceipt 7 7 8 3 4 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 3 4 receipt_row_07_y07_t03_04_fixed

private theorem receipt_row_07_y07_t04_05_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 4 5 := by decide +kernel

theorem receipt_row_07_y07_t04_05 : RowTileReceipt 7 7 8 4 5 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 4 5 receipt_row_07_y07_t04_05_fixed

private theorem receipt_row_07_y07_t05_06_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 5 6 := by decide +kernel

theorem receipt_row_07_y07_t05_06 : RowTileReceipt 7 7 8 5 6 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 5 6 receipt_row_07_y07_t05_06_fixed

private theorem receipt_row_07_y07_t06_07_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 6 7 := by decide +kernel

theorem receipt_row_07_y07_t06_07 : RowTileReceipt 7 7 8 6 7 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 6 7 receipt_row_07_y07_t06_07_fixed

private theorem receipt_row_07_y07_t07_08_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 7 8 := by decide +kernel

theorem receipt_row_07_y07_t07_08 : RowTileReceipt 7 7 8 7 8 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 7 8 receipt_row_07_y07_t07_08_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
