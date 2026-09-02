import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_y00_t00_24_fixed :
    FixedYReceipt 8 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_08_y00_t00_24 : RowTileReceipt 8 0 1 0 24 :=
  fixedYReceipt_to_rowTile 8 ⟨0, by decide⟩ 0 24 receipt_row_08_y00_t00_24_fixed

private theorem receipt_row_08_y00_t24_26_fixed :
    FixedYReceipt 8 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_08_y00_t24_26 : RowTileReceipt 8 0 1 24 26 :=
  fixedYReceipt_to_rowTile 8 ⟨0, by decide⟩ 24 26 receipt_row_08_y00_t24_26_fixed

private theorem receipt_row_08_y01_t00_24_fixed :
    FixedYReceipt 8 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_08_y01_t00_24 : RowTileReceipt 8 1 2 0 24 :=
  fixedYReceipt_to_rowTile 8 ⟨1, by decide⟩ 0 24 receipt_row_08_y01_t00_24_fixed

private theorem receipt_row_08_y01_t24_26_fixed :
    FixedYReceipt 8 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_08_y01_t24_26 : RowTileReceipt 8 1 2 24 26 :=
  fixedYReceipt_to_rowTile 8 ⟨1, by decide⟩ 24 26 receipt_row_08_y01_t24_26_fixed

private theorem receipt_row_08_y02_t00_24_fixed :
    FixedYReceipt 8 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_08_y02_t00_24 : RowTileReceipt 8 2 3 0 24 :=
  fixedYReceipt_to_rowTile 8 ⟨2, by decide⟩ 0 24 receipt_row_08_y02_t00_24_fixed

private theorem receipt_row_08_y02_t24_26_fixed :
    FixedYReceipt 8 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_08_y02_t24_26 : RowTileReceipt 8 2 3 24 26 :=
  fixedYReceipt_to_rowTile 8 ⟨2, by decide⟩ 24 26 receipt_row_08_y02_t24_26_fixed

private theorem receipt_row_08_y03_t00_04_fixed :
    FixedYReceipt 8 ⟨3, by decide⟩ 0 4 := by decide +kernel

theorem receipt_row_08_y03_t00_04 : RowTileReceipt 8 3 4 0 4 :=
  fixedYReceipt_to_rowTile 8 ⟨3, by decide⟩ 0 4 receipt_row_08_y03_t00_04_fixed

private theorem receipt_row_08_y03_t04_26_fixed :
    FixedYReceipt 8 ⟨3, by decide⟩ 4 26 := by decide +kernel

theorem receipt_row_08_y03_t04_26 : RowTileReceipt 8 3 4 4 26 :=
  fixedYReceipt_to_rowTile 8 ⟨3, by decide⟩ 4 26 receipt_row_08_y03_t04_26_fixed

private theorem receipt_row_08_y04_t00_01_fixed :
    FixedYReceipt 8 ⟨4, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_08_y04_t00_01 : RowTileReceipt 8 4 5 0 1 :=
  fixedYReceipt_to_rowTile 8 ⟨4, by decide⟩ 0 1 receipt_row_08_y04_t00_01_fixed

private theorem receipt_row_08_y04_t01_03_fixed :
    FixedYReceipt 8 ⟨4, by decide⟩ 1 3 := by decide +kernel

theorem receipt_row_08_y04_t01_03 : RowTileReceipt 8 4 5 1 3 :=
  fixedYReceipt_to_rowTile 8 ⟨4, by decide⟩ 1 3 receipt_row_08_y04_t01_03_fixed

private theorem receipt_row_08_y04_t03_26_fixed :
    FixedYReceipt 8 ⟨4, by decide⟩ 3 26 := by decide +kernel

theorem receipt_row_08_y04_t03_26 : RowTileReceipt 8 4 5 3 26 :=
  fixedYReceipt_to_rowTile 8 ⟨4, by decide⟩ 3 26 receipt_row_08_y04_t03_26_fixed

private theorem receipt_row_08_y05_t00_01_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_08_y05_t00_01 : RowTileReceipt 8 5 6 0 1 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 0 1 receipt_row_08_y05_t00_01_fixed

private theorem receipt_row_08_y05_t01_02_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 1 2 := by decide +kernel

theorem receipt_row_08_y05_t01_02 : RowTileReceipt 8 5 6 1 2 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 1 2 receipt_row_08_y05_t01_02_fixed

private theorem receipt_row_08_y05_t02_04_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_08_y05_t02_04 : RowTileReceipt 8 5 6 2 4 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 2 4 receipt_row_08_y05_t02_04_fixed

private theorem receipt_row_08_y05_t04_06_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 4 6 := by decide +kernel

theorem receipt_row_08_y05_t04_06 : RowTileReceipt 8 5 6 4 6 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 4 6 receipt_row_08_y05_t04_06_fixed

private theorem receipt_row_08_y05_t06_08_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 6 8 := by decide +kernel

theorem receipt_row_08_y05_t06_08 : RowTileReceipt 8 5 6 6 8 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 6 8 receipt_row_08_y05_t06_08_fixed

private theorem receipt_row_08_y05_t08_10_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 8 10 := by decide +kernel

theorem receipt_row_08_y05_t08_10 : RowTileReceipt 8 5 6 8 10 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 8 10 receipt_row_08_y05_t08_10_fixed

private theorem receipt_row_08_y05_t10_18_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 10 18 := by decide +kernel

theorem receipt_row_08_y05_t10_18 : RowTileReceipt 8 5 6 10 18 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 10 18 receipt_row_08_y05_t10_18_fixed

private theorem receipt_row_08_y05_t18_26_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 18 26 := by decide +kernel

theorem receipt_row_08_y05_t18_26 : RowTileReceipt 8 5 6 18 26 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 18 26 receipt_row_08_y05_t18_26_fixed

private theorem receipt_row_08_y06_t00_01_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_08_y06_t00_01 : RowTileReceipt 8 6 7 0 1 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 0 1 receipt_row_08_y06_t00_01_fixed

private theorem receipt_row_08_y06_t01_02_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 1 2 := by decide +kernel

theorem receipt_row_08_y06_t01_02 : RowTileReceipt 8 6 7 1 2 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 1 2 receipt_row_08_y06_t01_02_fixed

private theorem receipt_row_08_y06_t02_03_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 2 3 := by decide +kernel

theorem receipt_row_08_y06_t02_03 : RowTileReceipt 8 6 7 2 3 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 2 3 receipt_row_08_y06_t02_03_fixed

private theorem receipt_row_08_y06_t03_11_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 3 11 := by decide +kernel

theorem receipt_row_08_y06_t03_11 : RowTileReceipt 8 6 7 3 11 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 3 11 receipt_row_08_y06_t03_11_fixed

private theorem receipt_row_08_y06_t11_26_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 11 26 := by decide +kernel

theorem receipt_row_08_y06_t11_26 : RowTileReceipt 8 6 7 11 26 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 11 26 receipt_row_08_y06_t11_26_fixed

theorem receipt_row_08_band_07_09 : RowBandReceipt 8 7 9 := by decide +kernel

theorem receipt_row_08_band_09_11 : RowBandReceipt 8 9 11 := by decide +kernel

theorem receipt_row_08_band_11_13 : RowBandReceipt 8 11 13 := by decide +kernel

theorem receipt_row_08_band_13_15 : RowBandReceipt 8 13 15 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
