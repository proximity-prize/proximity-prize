import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_00_02 : RowBandReceipt 8 0 2 := by decide +kernel

private theorem receipt_row_08_y02_t00_24_fixed :
    FixedYReceipt 8 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_08_y02_t00_24 : RowTileReceipt 8 2 3 0 24 :=
  fixedYReceipt_to_rowTile 8 ⟨2, by decide⟩ 0 24 receipt_row_08_y02_t00_24_fixed

private theorem receipt_row_08_y02_t24_29_fixed :
    FixedYReceipt 8 ⟨2, by decide⟩ 24 29 := by decide +kernel

theorem receipt_row_08_y02_t24_29 : RowTileReceipt 8 2 3 24 29 :=
  fixedYReceipt_to_rowTile 8 ⟨2, by decide⟩ 24 29 receipt_row_08_y02_t24_29_fixed

private theorem receipt_row_08_y03_t00_24_fixed :
    FixedYReceipt 8 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_08_y03_t00_24 : RowTileReceipt 8 3 4 0 24 :=
  fixedYReceipt_to_rowTile 8 ⟨3, by decide⟩ 0 24 receipt_row_08_y03_t00_24_fixed

private theorem receipt_row_08_y03_t24_29_fixed :
    FixedYReceipt 8 ⟨3, by decide⟩ 24 29 := by decide +kernel

theorem receipt_row_08_y03_t24_29 : RowTileReceipt 8 3 4 24 29 :=
  fixedYReceipt_to_rowTile 8 ⟨3, by decide⟩ 24 29 receipt_row_08_y03_t24_29_fixed

private theorem receipt_row_08_y04_t00_02_fixed :
    FixedYReceipt 8 ⟨4, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_08_y04_t00_02 : RowTileReceipt 8 4 5 0 2 :=
  fixedYReceipt_to_rowTile 8 ⟨4, by decide⟩ 0 2 receipt_row_08_y04_t00_02_fixed

private theorem receipt_row_08_y04_t02_26_fixed :
    FixedYReceipt 8 ⟨4, by decide⟩ 2 26 := by decide +kernel

theorem receipt_row_08_y04_t02_26 : RowTileReceipt 8 4 5 2 26 :=
  fixedYReceipt_to_rowTile 8 ⟨4, by decide⟩ 2 26 receipt_row_08_y04_t02_26_fixed

private theorem receipt_row_08_y04_t26_29_fixed :
    FixedYReceipt 8 ⟨4, by decide⟩ 26 29 := by decide +kernel

theorem receipt_row_08_y04_t26_29 : RowTileReceipt 8 4 5 26 29 :=
  fixedYReceipt_to_rowTile 8 ⟨4, by decide⟩ 26 29 receipt_row_08_y04_t26_29_fixed

private theorem receipt_row_08_y05_t00_02_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_08_y05_t00_02 : RowTileReceipt 8 5 6 0 2 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 0 2 receipt_row_08_y05_t00_02_fixed

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

private theorem receipt_row_08_y05_t10_12_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 10 12 := by decide +kernel

theorem receipt_row_08_y05_t10_12 : RowTileReceipt 8 5 6 10 12 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 10 12 receipt_row_08_y05_t10_12_fixed

private theorem receipt_row_08_y05_t12_20_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 12 20 := by decide +kernel

theorem receipt_row_08_y05_t12_20 : RowTileReceipt 8 5 6 12 20 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 12 20 receipt_row_08_y05_t12_20_fixed

private theorem receipt_row_08_y05_t20_29_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 20 29 := by decide +kernel

theorem receipt_row_08_y05_t20_29 : RowTileReceipt 8 5 6 20 29 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 20 29 receipt_row_08_y05_t20_29_fixed

private theorem receipt_row_08_y06_t00_28_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 0 28 := by decide +kernel

theorem receipt_row_08_y06_t00_28 : RowTileReceipt 8 6 7 0 28 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 0 28 receipt_row_08_y06_t00_28_fixed

private theorem receipt_row_08_y06_t28_29_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 28 29 := by decide +kernel

theorem receipt_row_08_y06_t28_29 : RowTileReceipt 8 6 7 28 29 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 28 29 receipt_row_08_y06_t28_29_fixed

theorem receipt_row_08_band_07_09 : RowBandReceipt 8 7 9 := by decide +kernel

theorem receipt_row_08_band_09_11 : RowBandReceipt 8 9 11 := by decide +kernel

theorem receipt_row_08_band_11_13 : RowBandReceipt 8 11 13 := by decide +kernel

theorem receipt_row_08_band_13_15 : RowBandReceipt 8 13 15 := by decide +kernel

theorem receipt_row_08_band_15_17 : RowBandReceipt 8 15 17 := by decide +kernel

theorem receipt_row_08_band_17_19 : RowBandReceipt 8 17 19 := by decide +kernel

theorem receipt_row_08_band_19_21 : RowBandReceipt 8 19 21 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
