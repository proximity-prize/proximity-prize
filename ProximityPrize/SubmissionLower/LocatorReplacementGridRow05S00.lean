import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_y00_t00_24_fixed :
    FixedYReceipt 5 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_05_y00_t00_24 : RowTileReceipt 5 0 1 0 24 :=
  fixedYReceipt_to_rowTile 5 ⟨0, by decide⟩ 0 24 receipt_row_05_y00_t00_24_fixed

private theorem receipt_row_05_y00_t24_26_fixed :
    FixedYReceipt 5 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_05_y00_t24_26 : RowTileReceipt 5 0 1 24 26 :=
  fixedYReceipt_to_rowTile 5 ⟨0, by decide⟩ 24 26 receipt_row_05_y00_t24_26_fixed

private theorem receipt_row_05_y01_t00_24_fixed :
    FixedYReceipt 5 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_05_y01_t00_24 : RowTileReceipt 5 1 2 0 24 :=
  fixedYReceipt_to_rowTile 5 ⟨1, by decide⟩ 0 24 receipt_row_05_y01_t00_24_fixed

private theorem receipt_row_05_y01_t24_26_fixed :
    FixedYReceipt 5 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_05_y01_t24_26 : RowTileReceipt 5 1 2 24 26 :=
  fixedYReceipt_to_rowTile 5 ⟨1, by decide⟩ 24 26 receipt_row_05_y01_t24_26_fixed

private theorem receipt_row_05_y02_t00_24_fixed :
    FixedYReceipt 5 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_05_y02_t00_24 : RowTileReceipt 5 2 3 0 24 :=
  fixedYReceipt_to_rowTile 5 ⟨2, by decide⟩ 0 24 receipt_row_05_y02_t00_24_fixed

private theorem receipt_row_05_y02_t24_26_fixed :
    FixedYReceipt 5 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_05_y02_t24_26 : RowTileReceipt 5 2 3 24 26 :=
  fixedYReceipt_to_rowTile 5 ⟨2, by decide⟩ 24 26 receipt_row_05_y02_t24_26_fixed

private theorem receipt_row_05_y03_t00_24_fixed :
    FixedYReceipt 5 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_05_y03_t00_24 : RowTileReceipt 5 3 4 0 24 :=
  fixedYReceipt_to_rowTile 5 ⟨3, by decide⟩ 0 24 receipt_row_05_y03_t00_24_fixed

private theorem receipt_row_05_y03_t24_26_fixed :
    FixedYReceipt 5 ⟨3, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_05_y03_t24_26 : RowTileReceipt 5 3 4 24 26 :=
  fixedYReceipt_to_rowTile 5 ⟨3, by decide⟩ 24 26 receipt_row_05_y03_t24_26_fixed

private theorem receipt_row_05_y04_t00_24_fixed :
    FixedYReceipt 5 ⟨4, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_05_y04_t00_24 : RowTileReceipt 5 4 5 0 24 :=
  fixedYReceipt_to_rowTile 5 ⟨4, by decide⟩ 0 24 receipt_row_05_y04_t00_24_fixed

private theorem receipt_row_05_y04_t24_26_fixed :
    FixedYReceipt 5 ⟨4, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_05_y04_t24_26 : RowTileReceipt 5 4 5 24 26 :=
  fixedYReceipt_to_rowTile 5 ⟨4, by decide⟩ 24 26 receipt_row_05_y04_t24_26_fixed

private theorem receipt_row_05_y05_t00_08_fixed :
    FixedYReceipt 5 ⟨5, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_05_y05_t00_08 : RowTileReceipt 5 5 6 0 8 :=
  fixedYReceipt_to_rowTile 5 ⟨5, by decide⟩ 0 8 receipt_row_05_y05_t00_08_fixed

private theorem receipt_row_05_y05_t08_26_fixed :
    FixedYReceipt 5 ⟨5, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_05_y05_t08_26 : RowTileReceipt 5 5 6 8 26 :=
  fixedYReceipt_to_rowTile 5 ⟨5, by decide⟩ 8 26 receipt_row_05_y05_t08_26_fixed

private theorem receipt_row_05_y06_t00_10_fixed :
    FixedYReceipt 5 ⟨6, by decide⟩ 0 10 := by decide +kernel

theorem receipt_row_05_y06_t00_10 : RowTileReceipt 5 6 7 0 10 :=
  fixedYReceipt_to_rowTile 5 ⟨6, by decide⟩ 0 10 receipt_row_05_y06_t00_10_fixed

private theorem receipt_row_05_y06_t10_26_fixed :
    FixedYReceipt 5 ⟨6, by decide⟩ 10 26 := by decide +kernel

theorem receipt_row_05_y06_t10_26 : RowTileReceipt 5 6 7 10 26 :=
  fixedYReceipt_to_rowTile 5 ⟨6, by decide⟩ 10 26 receipt_row_05_y06_t10_26_fixed

private theorem receipt_row_05_y07_t00_02_fixed :
    FixedYReceipt 5 ⟨7, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_05_y07_t00_02 : RowTileReceipt 5 7 8 0 2 :=
  fixedYReceipt_to_rowTile 5 ⟨7, by decide⟩ 0 2 receipt_row_05_y07_t00_02_fixed

private theorem receipt_row_05_y07_t02_26_fixed :
    FixedYReceipt 5 ⟨7, by decide⟩ 2 26 := by decide +kernel

theorem receipt_row_05_y07_t02_26 : RowTileReceipt 5 7 8 2 26 :=
  fixedYReceipt_to_rowTile 5 ⟨7, by decide⟩ 2 26 receipt_row_05_y07_t02_26_fixed

private theorem receipt_row_05_y08_t00_02_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_05_y08_t00_02 : RowTileReceipt 5 8 9 0 2 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 0 2 receipt_row_05_y08_t00_02_fixed

private theorem receipt_row_05_y08_t02_04_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_05_y08_t02_04 : RowTileReceipt 5 8 9 2 4 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 2 4 receipt_row_05_y08_t02_04_fixed

private theorem receipt_row_05_y08_t04_26_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 4 26 := by decide +kernel

theorem receipt_row_05_y08_t04_26 : RowTileReceipt 5 8 9 4 26 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 4 26 receipt_row_05_y08_t04_26_fixed

private theorem receipt_row_05_y09_t00_02_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_05_y09_t00_02 : RowTileReceipt 5 9 10 0 2 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 0 2 receipt_row_05_y09_t00_02_fixed

private theorem receipt_row_05_y09_t02_04_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_05_y09_t02_04 : RowTileReceipt 5 9 10 2 4 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 2 4 receipt_row_05_y09_t02_04_fixed

private theorem receipt_row_05_y09_t04_06_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 4 6 := by decide +kernel

theorem receipt_row_05_y09_t04_06 : RowTileReceipt 5 9 10 4 6 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 4 6 receipt_row_05_y09_t04_06_fixed

private theorem receipt_row_05_y09_t06_08_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 6 8 := by decide +kernel

theorem receipt_row_05_y09_t06_08 : RowTileReceipt 5 9 10 6 8 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 6 8 receipt_row_05_y09_t06_08_fixed

private theorem receipt_row_05_y09_t08_10_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 8 10 := by decide +kernel

theorem receipt_row_05_y09_t08_10 : RowTileReceipt 5 9 10 8 10 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 8 10 receipt_row_05_y09_t08_10_fixed

private theorem receipt_row_05_y09_t10_12_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 10 12 := by decide +kernel

theorem receipt_row_05_y09_t10_12 : RowTileReceipt 5 9 10 10 12 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 10 12 receipt_row_05_y09_t10_12_fixed

private theorem receipt_row_05_y09_t12_14_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 12 14 := by decide +kernel

theorem receipt_row_05_y09_t12_14 : RowTileReceipt 5 9 10 12 14 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 12 14 receipt_row_05_y09_t12_14_fixed

private theorem receipt_row_05_y09_t14_26_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 14 26 := by decide +kernel

theorem receipt_row_05_y09_t14_26 : RowTileReceipt 5 9 10 14 26 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 14 26 receipt_row_05_y09_t14_26_fixed

theorem receipt_row_05_band_10_12 : RowBandReceipt 5 10 12 := by decide +kernel

theorem receipt_row_05_band_12_14 : RowBandReceipt 5 12 14 := by decide +kernel

theorem receipt_row_05_band_14_16 : RowBandReceipt 5 14 16 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
