import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_05_band_00_02 : RowBandReceipt 5 0 2 := by decide +kernel

theorem receipt_row_05_band_02_03 : RowBandReceipt 5 2 3 := by decide +kernel

private theorem receipt_row_05_y03_t00_24_fixed :
    FixedYReceipt 5 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_05_y03_t00_24 : RowTileReceipt 5 3 4 0 24 :=
  fixedYReceipt_to_rowTile 5 ⟨3, by decide⟩ 0 24 receipt_row_05_y03_t00_24_fixed

private theorem receipt_row_05_y03_t24_29_fixed :
    FixedYReceipt 5 ⟨3, by decide⟩ 24 30 := by decide +kernel

theorem receipt_row_05_y03_t24_29 : RowTileReceipt 5 3 4 24 30 :=
  fixedYReceipt_to_rowTile 5 ⟨3, by decide⟩ 24 30 receipt_row_05_y03_t24_29_fixed

private theorem receipt_row_05_y04_t00_24_fixed :
    FixedYReceipt 5 ⟨4, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_05_y04_t00_24 : RowTileReceipt 5 4 5 0 24 :=
  fixedYReceipt_to_rowTile 5 ⟨4, by decide⟩ 0 24 receipt_row_05_y04_t00_24_fixed

private theorem receipt_row_05_y04_t24_29_fixed :
    FixedYReceipt 5 ⟨4, by decide⟩ 24 30 := by decide +kernel

theorem receipt_row_05_y04_t24_29 : RowTileReceipt 5 4 5 24 30 :=
  fixedYReceipt_to_rowTile 5 ⟨4, by decide⟩ 24 30 receipt_row_05_y04_t24_29_fixed

private theorem receipt_row_05_y05_t00_24_fixed :
    FixedYReceipt 5 ⟨5, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_05_y05_t00_24 : RowTileReceipt 5 5 6 0 24 :=
  fixedYReceipt_to_rowTile 5 ⟨5, by decide⟩ 0 24 receipt_row_05_y05_t00_24_fixed

private theorem receipt_row_05_y05_t24_29_fixed :
    FixedYReceipt 5 ⟨5, by decide⟩ 24 30 := by decide +kernel

theorem receipt_row_05_y05_t24_29 : RowTileReceipt 5 5 6 24 30 :=
  fixedYReceipt_to_rowTile 5 ⟨5, by decide⟩ 24 30 receipt_row_05_y05_t24_29_fixed

private theorem receipt_row_05_y06_t00_10_fixed :
    FixedYReceipt 5 ⟨6, by decide⟩ 0 10 := by decide +kernel

theorem receipt_row_05_y06_t00_10 : RowTileReceipt 5 6 7 0 10 :=
  fixedYReceipt_to_rowTile 5 ⟨6, by decide⟩ 0 10 receipt_row_05_y06_t00_10_fixed

private theorem receipt_row_05_y06_t10_29_fixed :
    FixedYReceipt 5 ⟨6, by decide⟩ 10 30 := by decide +kernel

theorem receipt_row_05_y06_t10_29 : RowTileReceipt 5 6 7 10 30 :=
  fixedYReceipt_to_rowTile 5 ⟨6, by decide⟩ 10 30 receipt_row_05_y06_t10_29_fixed

private theorem receipt_row_05_y07_t00_02_fixed :
    FixedYReceipt 5 ⟨7, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_05_y07_t00_02 : RowTileReceipt 5 7 8 0 2 :=
  fixedYReceipt_to_rowTile 5 ⟨7, by decide⟩ 0 2 receipt_row_05_y07_t00_02_fixed

private theorem receipt_row_05_y07_t02_26_fixed :
    FixedYReceipt 5 ⟨7, by decide⟩ 2 26 := by decide +kernel

theorem receipt_row_05_y07_t02_26 : RowTileReceipt 5 7 8 2 26 :=
  fixedYReceipt_to_rowTile 5 ⟨7, by decide⟩ 2 26 receipt_row_05_y07_t02_26_fixed

private theorem receipt_row_05_y07_t26_29_fixed :
    FixedYReceipt 5 ⟨7, by decide⟩ 26 30 := by decide +kernel

theorem receipt_row_05_y07_t26_29 : RowTileReceipt 5 7 8 26 30 :=
  fixedYReceipt_to_rowTile 5 ⟨7, by decide⟩ 26 30 receipt_row_05_y07_t26_29_fixed

private theorem receipt_row_05_y08_t00_02_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_05_y08_t00_02 : RowTileReceipt 5 8 9 0 2 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 0 2 receipt_row_05_y08_t00_02_fixed

private theorem receipt_row_05_y08_t02_04_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_05_y08_t02_04 : RowTileReceipt 5 8 9 2 4 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 2 4 receipt_row_05_y08_t02_04_fixed

private theorem receipt_row_05_y08_t04_12_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 4 12 := by decide +kernel

theorem receipt_row_05_y08_t04_12 : RowTileReceipt 5 8 9 4 12 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 4 12 receipt_row_05_y08_t04_12_fixed

private theorem receipt_row_05_y08_t12_29_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 12 30 := by decide +kernel

theorem receipt_row_05_y08_t12_29 : RowTileReceipt 5 8 9 12 30 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 12 30 receipt_row_05_y08_t12_29_fixed

private theorem receipt_row_05_y09_t00_28_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 0 28 := by decide +kernel

theorem receipt_row_05_y09_t00_28 : RowTileReceipt 5 9 10 0 28 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 0 28 receipt_row_05_y09_t00_28_fixed

private theorem receipt_row_05_y09_t28_29_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 28 30 := by decide +kernel

theorem receipt_row_05_y09_t28_29 : RowTileReceipt 5 9 10 28 30 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 28 30 receipt_row_05_y09_t28_29_fixed

theorem receipt_row_05_band_10_12 : RowBandReceipt 5 10 12 := by decide +kernel

theorem receipt_row_05_band_12_14 : RowBandReceipt 5 12 14 := by decide +kernel

theorem receipt_row_05_band_14_16 : RowBandReceipt 5 14 16 := by decide +kernel

theorem receipt_row_05_band_16_18 : RowBandReceipt 5 16 18 := by decide +kernel

theorem receipt_row_05_band_18_20 : RowBandReceipt 5 18 20 := by decide +kernel

theorem receipt_row_05_band_20_22 : RowBandReceipt 5 20 22 := by decide +kernel

theorem receipt_row_05_band_22_25 : RowBandReceipt 5 22 25 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
