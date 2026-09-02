import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_y00_t00_24_fixed :
    FixedYReceipt 3 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y00_t00_24 : RowTileReceipt 3 0 1 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨0, by decide⟩ 0 24 receipt_row_03_y00_t00_24_fixed

private theorem receipt_row_03_y00_t24_26_fixed :
    FixedYReceipt 3 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y00_t24_26 : RowTileReceipt 3 0 1 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨0, by decide⟩ 24 26 receipt_row_03_y00_t24_26_fixed

private theorem receipt_row_03_y01_t00_24_fixed :
    FixedYReceipt 3 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y01_t00_24 : RowTileReceipt 3 1 2 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨1, by decide⟩ 0 24 receipt_row_03_y01_t00_24_fixed

private theorem receipt_row_03_y01_t24_26_fixed :
    FixedYReceipt 3 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y01_t24_26 : RowTileReceipt 3 1 2 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨1, by decide⟩ 24 26 receipt_row_03_y01_t24_26_fixed

private theorem receipt_row_03_y02_t00_24_fixed :
    FixedYReceipt 3 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y02_t00_24 : RowTileReceipt 3 2 3 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨2, by decide⟩ 0 24 receipt_row_03_y02_t00_24_fixed

private theorem receipt_row_03_y02_t24_26_fixed :
    FixedYReceipt 3 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y02_t24_26 : RowTileReceipt 3 2 3 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨2, by decide⟩ 24 26 receipt_row_03_y02_t24_26_fixed

private theorem receipt_row_03_y03_t00_24_fixed :
    FixedYReceipt 3 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y03_t00_24 : RowTileReceipt 3 3 4 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨3, by decide⟩ 0 24 receipt_row_03_y03_t00_24_fixed

private theorem receipt_row_03_y03_t24_26_fixed :
    FixedYReceipt 3 ⟨3, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y03_t24_26 : RowTileReceipt 3 3 4 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨3, by decide⟩ 24 26 receipt_row_03_y03_t24_26_fixed

private theorem receipt_row_03_y04_t00_24_fixed :
    FixedYReceipt 3 ⟨4, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y04_t00_24 : RowTileReceipt 3 4 5 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨4, by decide⟩ 0 24 receipt_row_03_y04_t00_24_fixed

private theorem receipt_row_03_y04_t24_26_fixed :
    FixedYReceipt 3 ⟨4, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y04_t24_26 : RowTileReceipt 3 4 5 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨4, by decide⟩ 24 26 receipt_row_03_y04_t24_26_fixed

private theorem receipt_row_03_y05_t00_24_fixed :
    FixedYReceipt 3 ⟨5, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y05_t00_24 : RowTileReceipt 3 5 6 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨5, by decide⟩ 0 24 receipt_row_03_y05_t00_24_fixed

private theorem receipt_row_03_y05_t24_26_fixed :
    FixedYReceipt 3 ⟨5, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y05_t24_26 : RowTileReceipt 3 5 6 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨5, by decide⟩ 24 26 receipt_row_03_y05_t24_26_fixed

private theorem receipt_row_03_y06_t00_24_fixed :
    FixedYReceipt 3 ⟨6, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y06_t00_24 : RowTileReceipt 3 6 7 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨6, by decide⟩ 0 24 receipt_row_03_y06_t00_24_fixed

private theorem receipt_row_03_y06_t24_26_fixed :
    FixedYReceipt 3 ⟨6, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y06_t24_26 : RowTileReceipt 3 6 7 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨6, by decide⟩ 24 26 receipt_row_03_y06_t24_26_fixed

private theorem receipt_row_03_y07_t00_26_fixed :
    FixedYReceipt 3 ⟨7, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_03_y07_t00_26 : RowTileReceipt 3 7 8 0 26 :=
  fixedYReceipt_to_rowTile 3 ⟨7, by decide⟩ 0 26 receipt_row_03_y07_t00_26_fixed

private theorem receipt_row_03_y08_t00_12_fixed :
    FixedYReceipt 3 ⟨8, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_03_y08_t00_12 : RowTileReceipt 3 8 9 0 12 :=
  fixedYReceipt_to_rowTile 3 ⟨8, by decide⟩ 0 12 receipt_row_03_y08_t00_12_fixed

private theorem receipt_row_03_y08_t12_26_fixed :
    FixedYReceipt 3 ⟨8, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_03_y08_t12_26 : RowTileReceipt 3 8 9 12 26 :=
  fixedYReceipt_to_rowTile 3 ⟨8, by decide⟩ 12 26 receipt_row_03_y08_t12_26_fixed

private theorem receipt_row_03_y09_t00_12_fixed :
    FixedYReceipt 3 ⟨9, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_03_y09_t00_12 : RowTileReceipt 3 9 10 0 12 :=
  fixedYReceipt_to_rowTile 3 ⟨9, by decide⟩ 0 12 receipt_row_03_y09_t00_12_fixed

private theorem receipt_row_03_y09_t12_26_fixed :
    FixedYReceipt 3 ⟨9, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_03_y09_t12_26 : RowTileReceipt 3 9 10 12 26 :=
  fixedYReceipt_to_rowTile 3 ⟨9, by decide⟩ 12 26 receipt_row_03_y09_t12_26_fixed

private theorem receipt_row_03_y10_t00_12_fixed :
    FixedYReceipt 3 ⟨10, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_03_y10_t00_12 : RowTileReceipt 3 10 11 0 12 :=
  fixedYReceipt_to_rowTile 3 ⟨10, by decide⟩ 0 12 receipt_row_03_y10_t00_12_fixed

private theorem receipt_row_03_y10_t12_26_fixed :
    FixedYReceipt 3 ⟨10, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_03_y10_t12_26 : RowTileReceipt 3 10 11 12 26 :=
  fixedYReceipt_to_rowTile 3 ⟨10, by decide⟩ 12 26 receipt_row_03_y10_t12_26_fixed

theorem receipt_row_03_band_11_13 : RowBandReceipt 3 11 13 := by decide +kernel

theorem receipt_row_03_band_13_15 : RowBandReceipt 3 13 15 := by decide +kernel

theorem receipt_row_03_band_15_17 : RowBandReceipt 3 15 17 := by decide +kernel

theorem receipt_row_03_band_17_19 : RowBandReceipt 3 17 19 := by decide +kernel

theorem receipt_row_03_band_19_21 : RowBandReceipt 3 19 21 := by decide +kernel

theorem receipt_row_03_band_21_23 : RowBandReceipt 3 21 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
