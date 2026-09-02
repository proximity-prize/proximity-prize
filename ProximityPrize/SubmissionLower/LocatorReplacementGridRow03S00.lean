import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_03_band_00_02 : RowBandReceipt 3 0 2 := by decide +kernel

theorem receipt_row_03_band_02_04 : RowBandReceipt 3 2 4 := by decide +kernel

theorem receipt_row_03_band_04_06 : RowBandReceipt 3 4 6 := by decide +kernel

theorem receipt_row_03_band_06_07 : RowBandReceipt 3 6 7 := by decide +kernel

private theorem receipt_row_03_y07_t00_28_fixed :
    FixedYReceipt 3 ⟨7, by decide⟩ 0 28 := by decide +kernel

theorem receipt_row_03_y07_t00_28 : RowTileReceipt 3 7 8 0 28 :=
  fixedYReceipt_to_rowTile 3 ⟨7, by decide⟩ 0 28 receipt_row_03_y07_t00_28_fixed

private theorem receipt_row_03_y07_t28_29_fixed :
    FixedYReceipt 3 ⟨7, by decide⟩ 28 29 := by decide +kernel

theorem receipt_row_03_y07_t28_29 : RowTileReceipt 3 7 8 28 29 :=
  fixedYReceipt_to_rowTile 3 ⟨7, by decide⟩ 28 29 receipt_row_03_y07_t28_29_fixed

private theorem receipt_row_03_y08_t00_28_fixed :
    FixedYReceipt 3 ⟨8, by decide⟩ 0 28 := by decide +kernel

theorem receipt_row_03_y08_t00_28 : RowTileReceipt 3 8 9 0 28 :=
  fixedYReceipt_to_rowTile 3 ⟨8, by decide⟩ 0 28 receipt_row_03_y08_t00_28_fixed

private theorem receipt_row_03_y08_t28_29_fixed :
    FixedYReceipt 3 ⟨8, by decide⟩ 28 29 := by decide +kernel

theorem receipt_row_03_y08_t28_29 : RowTileReceipt 3 8 9 28 29 :=
  fixedYReceipt_to_rowTile 3 ⟨8, by decide⟩ 28 29 receipt_row_03_y08_t28_29_fixed

private theorem receipt_row_03_y09_t00_28_fixed :
    FixedYReceipt 3 ⟨9, by decide⟩ 0 28 := by decide +kernel

theorem receipt_row_03_y09_t00_28 : RowTileReceipt 3 9 10 0 28 :=
  fixedYReceipt_to_rowTile 3 ⟨9, by decide⟩ 0 28 receipt_row_03_y09_t00_28_fixed

private theorem receipt_row_03_y09_t28_29_fixed :
    FixedYReceipt 3 ⟨9, by decide⟩ 28 29 := by decide +kernel

theorem receipt_row_03_y09_t28_29 : RowTileReceipt 3 9 10 28 29 :=
  fixedYReceipt_to_rowTile 3 ⟨9, by decide⟩ 28 29 receipt_row_03_y09_t28_29_fixed

private theorem receipt_row_03_y10_t00_12_fixed :
    FixedYReceipt 3 ⟨10, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_03_y10_t00_12 : RowTileReceipt 3 10 11 0 12 :=
  fixedYReceipt_to_rowTile 3 ⟨10, by decide⟩ 0 12 receipt_row_03_y10_t00_12_fixed

private theorem receipt_row_03_y10_t12_29_fixed :
    FixedYReceipt 3 ⟨10, by decide⟩ 12 29 := by decide +kernel

theorem receipt_row_03_y10_t12_29 : RowTileReceipt 3 10 11 12 29 :=
  fixedYReceipt_to_rowTile 3 ⟨10, by decide⟩ 12 29 receipt_row_03_y10_t12_29_fixed

theorem receipt_row_03_band_11_13 : RowBandReceipt 3 11 13 := by decide +kernel

theorem receipt_row_03_band_13_15 : RowBandReceipt 3 13 15 := by decide +kernel

theorem receipt_row_03_band_15_17 : RowBandReceipt 3 15 17 := by decide +kernel

theorem receipt_row_03_band_17_19 : RowBandReceipt 3 17 19 := by decide +kernel

theorem receipt_row_03_band_19_21 : RowBandReceipt 3 19 21 := by decide +kernel

theorem receipt_row_03_band_21_23 : RowBandReceipt 3 21 23 := by decide +kernel

theorem receipt_row_03_band_23_25 : RowBandReceipt 3 23 25 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
