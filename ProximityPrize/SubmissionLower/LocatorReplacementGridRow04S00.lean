import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_04_band_00_02 : RowBandReceipt 4 0 2 := by decide +kernel

theorem receipt_row_04_band_02_04 : RowBandReceipt 4 2 4 := by decide +kernel

private theorem receipt_row_04_y04_t00_24_fixed :
    FixedYReceipt 4 ⟨4, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_04_y04_t00_24 : RowTileReceipt 4 4 5 0 24 :=
  fixedYReceipt_to_rowTile 4 ⟨4, by decide⟩ 0 24 receipt_row_04_y04_t00_24_fixed

private theorem receipt_row_04_y04_t24_29_fixed :
    FixedYReceipt 4 ⟨4, by decide⟩ 24 30 := by decide +kernel

theorem receipt_row_04_y04_t24_29 : RowTileReceipt 4 4 5 24 30 :=
  fixedYReceipt_to_rowTile 4 ⟨4, by decide⟩ 24 30 receipt_row_04_y04_t24_29_fixed

private theorem receipt_row_04_y05_t00_24_fixed :
    FixedYReceipt 4 ⟨5, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_04_y05_t00_24 : RowTileReceipt 4 5 6 0 24 :=
  fixedYReceipt_to_rowTile 4 ⟨5, by decide⟩ 0 24 receipt_row_04_y05_t00_24_fixed

private theorem receipt_row_04_y05_t24_29_fixed :
    FixedYReceipt 4 ⟨5, by decide⟩ 24 30 := by decide +kernel

theorem receipt_row_04_y05_t24_29 : RowTileReceipt 4 5 6 24 30 :=
  fixedYReceipt_to_rowTile 4 ⟨5, by decide⟩ 24 30 receipt_row_04_y05_t24_29_fixed

private theorem receipt_row_04_y06_t00_25_fixed :
    FixedYReceipt 4 ⟨6, by decide⟩ 0 25 := by decide +kernel

theorem receipt_row_04_y06_t00_25 : RowTileReceipt 4 6 7 0 25 :=
  fixedYReceipt_to_rowTile 4 ⟨6, by decide⟩ 0 25 receipt_row_04_y06_t00_25_fixed

private theorem receipt_row_04_y06_t25_29_fixed :
    FixedYReceipt 4 ⟨6, by decide⟩ 25 30 := by decide +kernel

theorem receipt_row_04_y06_t25_29 : RowTileReceipt 4 6 7 25 30 :=
  fixedYReceipt_to_rowTile 4 ⟨6, by decide⟩ 25 30 receipt_row_04_y06_t25_29_fixed

private theorem receipt_row_04_y07_t00_28_fixed :
    FixedYReceipt 4 ⟨7, by decide⟩ 0 28 := by decide +kernel

theorem receipt_row_04_y07_t00_28 : RowTileReceipt 4 7 8 0 28 :=
  fixedYReceipt_to_rowTile 4 ⟨7, by decide⟩ 0 28 receipt_row_04_y07_t00_28_fixed

private theorem receipt_row_04_y07_t28_29_fixed :
    FixedYReceipt 4 ⟨7, by decide⟩ 28 30 := by decide +kernel

theorem receipt_row_04_y07_t28_29 : RowTileReceipt 4 7 8 28 30 :=
  fixedYReceipt_to_rowTile 4 ⟨7, by decide⟩ 28 30 receipt_row_04_y07_t28_29_fixed

private theorem receipt_row_04_y08_t00_12_fixed :
    FixedYReceipt 4 ⟨8, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_04_y08_t00_12 : RowTileReceipt 4 8 9 0 12 :=
  fixedYReceipt_to_rowTile 4 ⟨8, by decide⟩ 0 12 receipt_row_04_y08_t00_12_fixed

private theorem receipt_row_04_y08_t12_29_fixed :
    FixedYReceipt 4 ⟨8, by decide⟩ 12 30 := by decide +kernel

theorem receipt_row_04_y08_t12_29 : RowTileReceipt 4 8 9 12 30 :=
  fixedYReceipt_to_rowTile 4 ⟨8, by decide⟩ 12 30 receipt_row_04_y08_t12_29_fixed

private theorem receipt_row_04_y09_t00_02_fixed :
    FixedYReceipt 4 ⟨9, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_04_y09_t00_02 : RowTileReceipt 4 9 10 0 2 :=
  fixedYReceipt_to_rowTile 4 ⟨9, by decide⟩ 0 2 receipt_row_04_y09_t00_02_fixed

private theorem receipt_row_04_y09_t02_26_fixed :
    FixedYReceipt 4 ⟨9, by decide⟩ 2 26 := by decide +kernel

theorem receipt_row_04_y09_t02_26 : RowTileReceipt 4 9 10 2 26 :=
  fixedYReceipt_to_rowTile 4 ⟨9, by decide⟩ 2 26 receipt_row_04_y09_t02_26_fixed

private theorem receipt_row_04_y09_t26_29_fixed :
    FixedYReceipt 4 ⟨9, by decide⟩ 26 30 := by decide +kernel

theorem receipt_row_04_y09_t26_29 : RowTileReceipt 4 9 10 26 30 :=
  fixedYReceipt_to_rowTile 4 ⟨9, by decide⟩ 26 30 receipt_row_04_y09_t26_29_fixed

private theorem receipt_row_04_y10_t00_12_fixed :
    FixedYReceipt 4 ⟨10, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_04_y10_t00_12 : RowTileReceipt 4 10 11 0 12 :=
  fixedYReceipt_to_rowTile 4 ⟨10, by decide⟩ 0 12 receipt_row_04_y10_t00_12_fixed

private theorem receipt_row_04_y10_t12_29_fixed :
    FixedYReceipt 4 ⟨10, by decide⟩ 12 30 := by decide +kernel

theorem receipt_row_04_y10_t12_29 : RowTileReceipt 4 10 11 12 30 :=
  fixedYReceipt_to_rowTile 4 ⟨10, by decide⟩ 12 30 receipt_row_04_y10_t12_29_fixed

theorem receipt_row_04_band_11_13 : RowBandReceipt 4 11 13 := by decide +kernel

theorem receipt_row_04_band_13_15 : RowBandReceipt 4 13 15 := by decide +kernel

theorem receipt_row_04_band_15_17 : RowBandReceipt 4 15 17 := by decide +kernel

theorem receipt_row_04_band_17_19 : RowBandReceipt 4 17 19 := by decide +kernel

theorem receipt_row_04_band_19_21 : RowBandReceipt 4 19 21 := by decide +kernel

theorem receipt_row_04_band_21_23 : RowBandReceipt 4 21 23 := by decide +kernel

theorem receipt_row_04_band_23_25 : RowBandReceipt 4 23 25 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
