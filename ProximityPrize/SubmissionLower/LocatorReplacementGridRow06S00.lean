import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_00_02 : RowBandReceipt 6 0 2 := by decide +kernel

theorem receipt_row_06_band_02_03 : RowBandReceipt 6 2 3 := by decide +kernel

private theorem receipt_row_06_y03_t00_24_fixed :
    FixedYReceipt 6 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_y03_t00_24 : RowTileReceipt 6 3 4 0 24 :=
  fixedYReceipt_to_rowTile 6 ⟨3, by decide⟩ 0 24 receipt_row_06_y03_t00_24_fixed

private theorem receipt_row_06_y03_t24_29_fixed :
    FixedYReceipt 6 ⟨3, by decide⟩ 24 30 := by decide +kernel

theorem receipt_row_06_y03_t24_29 : RowTileReceipt 6 3 4 24 30 :=
  fixedYReceipt_to_rowTile 6 ⟨3, by decide⟩ 24 30 receipt_row_06_y03_t24_29_fixed

private theorem receipt_row_06_y04_t00_24_fixed :
    FixedYReceipt 6 ⟨4, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_y04_t00_24 : RowTileReceipt 6 4 5 0 24 :=
  fixedYReceipt_to_rowTile 6 ⟨4, by decide⟩ 0 24 receipt_row_06_y04_t00_24_fixed

private theorem receipt_row_06_y04_t24_29_fixed :
    FixedYReceipt 6 ⟨4, by decide⟩ 24 30 := by decide +kernel

theorem receipt_row_06_y04_t24_29 : RowTileReceipt 6 4 5 24 30 :=
  fixedYReceipt_to_rowTile 6 ⟨4, by decide⟩ 24 30 receipt_row_06_y04_t24_29_fixed

private theorem receipt_row_06_y05_t00_08_fixed :
    FixedYReceipt 6 ⟨5, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_06_y05_t00_08 : RowTileReceipt 6 5 6 0 8 :=
  fixedYReceipt_to_rowTile 6 ⟨5, by decide⟩ 0 8 receipt_row_06_y05_t00_08_fixed

private theorem receipt_row_06_y05_t08_29_fixed :
    FixedYReceipt 6 ⟨5, by decide⟩ 8 30 := by decide +kernel

theorem receipt_row_06_y05_t08_29 : RowTileReceipt 6 5 6 8 30 :=
  fixedYReceipt_to_rowTile 6 ⟨5, by decide⟩ 8 30 receipt_row_06_y05_t08_29_fixed

private theorem receipt_row_06_y06_t00_02_fixed :
    FixedYReceipt 6 ⟨6, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_06_y06_t00_02 : RowTileReceipt 6 6 7 0 2 :=
  fixedYReceipt_to_rowTile 6 ⟨6, by decide⟩ 0 2 receipt_row_06_y06_t00_02_fixed

private theorem receipt_row_06_y06_t02_10_fixed :
    FixedYReceipt 6 ⟨6, by decide⟩ 2 10 := by decide +kernel

theorem receipt_row_06_y06_t02_10 : RowTileReceipt 6 6 7 2 10 :=
  fixedYReceipt_to_rowTile 6 ⟨6, by decide⟩ 2 10 receipt_row_06_y06_t02_10_fixed

private theorem receipt_row_06_y06_t10_29_fixed :
    FixedYReceipt 6 ⟨6, by decide⟩ 10 30 := by decide +kernel

theorem receipt_row_06_y06_t10_29 : RowTileReceipt 6 6 7 10 30 :=
  fixedYReceipt_to_rowTile 6 ⟨6, by decide⟩ 10 30 receipt_row_06_y06_t10_29_fixed

private theorem receipt_row_06_y07_t00_02_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_06_y07_t00_02 : RowTileReceipt 6 7 8 0 2 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 0 2 receipt_row_06_y07_t00_02_fixed

private theorem receipt_row_06_y07_t02_04_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_06_y07_t02_04 : RowTileReceipt 6 7 8 2 4 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 2 4 receipt_row_06_y07_t02_04_fixed

private theorem receipt_row_06_y07_t04_06_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 4 6 := by decide +kernel

theorem receipt_row_06_y07_t04_06 : RowTileReceipt 6 7 8 4 6 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 4 6 receipt_row_06_y07_t04_06_fixed

private theorem receipt_row_06_y07_t06_08_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 6 8 := by decide +kernel

theorem receipt_row_06_y07_t06_08 : RowTileReceipt 6 7 8 6 8 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 6 8 receipt_row_06_y07_t06_08_fixed

private theorem receipt_row_06_y07_t08_10_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 8 10 := by decide +kernel

theorem receipt_row_06_y07_t08_10 : RowTileReceipt 6 7 8 8 10 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 8 10 receipt_row_06_y07_t08_10_fixed

private theorem receipt_row_06_y07_t10_12_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 10 12 := by decide +kernel

theorem receipt_row_06_y07_t10_12 : RowTileReceipt 6 7 8 10 12 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 10 12 receipt_row_06_y07_t10_12_fixed

private theorem receipt_row_06_y07_t12_14_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 12 14 := by decide +kernel

theorem receipt_row_06_y07_t12_14 : RowTileReceipt 6 7 8 12 14 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 12 14 receipt_row_06_y07_t12_14_fixed

private theorem receipt_row_06_y07_t14_16_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 14 16 := by decide +kernel

theorem receipt_row_06_y07_t14_16 : RowTileReceipt 6 7 8 14 16 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 14 16 receipt_row_06_y07_t14_16_fixed

private theorem receipt_row_06_y07_t16_24_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 16 24 := by decide +kernel

theorem receipt_row_06_y07_t16_24 : RowTileReceipt 6 7 8 16 24 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 16 24 receipt_row_06_y07_t16_24_fixed

private theorem receipt_row_06_y07_t24_29_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 24 30 := by decide +kernel

theorem receipt_row_06_y07_t24_29 : RowTileReceipt 6 7 8 24 30 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 24 30 receipt_row_06_y07_t24_29_fixed

private theorem receipt_row_06_y08_t00_02_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_06_y08_t00_02 : RowTileReceipt 6 8 9 0 2 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 0 2 receipt_row_06_y08_t00_02_fixed

private theorem receipt_row_06_y08_t02_04_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_06_y08_t02_04 : RowTileReceipt 6 8 9 2 4 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 2 4 receipt_row_06_y08_t02_04_fixed

private theorem receipt_row_06_y08_t04_12_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 4 12 := by decide +kernel

theorem receipt_row_06_y08_t04_12 : RowTileReceipt 6 8 9 4 12 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 4 12 receipt_row_06_y08_t04_12_fixed

private theorem receipt_row_06_y08_t12_29_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 12 30 := by decide +kernel

theorem receipt_row_06_y08_t12_29 : RowTileReceipt 6 8 9 12 30 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 12 30 receipt_row_06_y08_t12_29_fixed

theorem receipt_row_06_band_09_11 : RowBandReceipt 6 9 11 := by decide +kernel

theorem receipt_row_06_band_11_13 : RowBandReceipt 6 11 13 := by decide +kernel

theorem receipt_row_06_band_13_15 : RowBandReceipt 6 13 15 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
