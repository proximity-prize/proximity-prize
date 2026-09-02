import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_02_y00_t00_24_fixed :
    FixedYReceipt 2 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y00_t00_24 : RowTileReceipt 2 0 1 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨0, by decide⟩ 0 24 receipt_row_02_y00_t00_24_fixed

private theorem receipt_row_02_y00_t24_26_fixed :
    FixedYReceipt 2 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y00_t24_26 : RowTileReceipt 2 0 1 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨0, by decide⟩ 24 26 receipt_row_02_y00_t24_26_fixed

private theorem receipt_row_02_y01_t00_24_fixed :
    FixedYReceipt 2 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y01_t00_24 : RowTileReceipt 2 1 2 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨1, by decide⟩ 0 24 receipt_row_02_y01_t00_24_fixed

private theorem receipt_row_02_y01_t24_26_fixed :
    FixedYReceipt 2 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y01_t24_26 : RowTileReceipt 2 1 2 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨1, by decide⟩ 24 26 receipt_row_02_y01_t24_26_fixed

private theorem receipt_row_02_y02_t00_24_fixed :
    FixedYReceipt 2 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y02_t00_24 : RowTileReceipt 2 2 3 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨2, by decide⟩ 0 24 receipt_row_02_y02_t00_24_fixed

private theorem receipt_row_02_y02_t24_26_fixed :
    FixedYReceipt 2 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y02_t24_26 : RowTileReceipt 2 2 3 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨2, by decide⟩ 24 26 receipt_row_02_y02_t24_26_fixed

private theorem receipt_row_02_y03_t00_24_fixed :
    FixedYReceipt 2 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y03_t00_24 : RowTileReceipt 2 3 4 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨3, by decide⟩ 0 24 receipt_row_02_y03_t00_24_fixed

private theorem receipt_row_02_y03_t24_26_fixed :
    FixedYReceipt 2 ⟨3, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y03_t24_26 : RowTileReceipt 2 3 4 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨3, by decide⟩ 24 26 receipt_row_02_y03_t24_26_fixed

private theorem receipt_row_02_y04_t00_24_fixed :
    FixedYReceipt 2 ⟨4, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y04_t00_24 : RowTileReceipt 2 4 5 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨4, by decide⟩ 0 24 receipt_row_02_y04_t00_24_fixed

private theorem receipt_row_02_y04_t24_26_fixed :
    FixedYReceipt 2 ⟨4, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y04_t24_26 : RowTileReceipt 2 4 5 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨4, by decide⟩ 24 26 receipt_row_02_y04_t24_26_fixed

private theorem receipt_row_02_y05_t00_24_fixed :
    FixedYReceipt 2 ⟨5, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y05_t00_24 : RowTileReceipt 2 5 6 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨5, by decide⟩ 0 24 receipt_row_02_y05_t00_24_fixed

private theorem receipt_row_02_y05_t24_26_fixed :
    FixedYReceipt 2 ⟨5, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y05_t24_26 : RowTileReceipt 2 5 6 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨5, by decide⟩ 24 26 receipt_row_02_y05_t24_26_fixed

private theorem receipt_row_02_y06_t00_24_fixed :
    FixedYReceipt 2 ⟨6, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y06_t00_24 : RowTileReceipt 2 6 7 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨6, by decide⟩ 0 24 receipt_row_02_y06_t00_24_fixed

private theorem receipt_row_02_y06_t24_26_fixed :
    FixedYReceipt 2 ⟨6, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y06_t24_26 : RowTileReceipt 2 6 7 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨6, by decide⟩ 24 26 receipt_row_02_y06_t24_26_fixed

private theorem receipt_row_02_y07_t00_26_fixed :
    FixedYReceipt 2 ⟨7, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y07_t00_26 : RowTileReceipt 2 7 8 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨7, by decide⟩ 0 26 receipt_row_02_y07_t00_26_fixed

private theorem receipt_row_02_y08_t00_26_fixed :
    FixedYReceipt 2 ⟨8, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y08_t00_26 : RowTileReceipt 2 8 9 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨8, by decide⟩ 0 26 receipt_row_02_y08_t00_26_fixed

private theorem receipt_row_02_y09_t00_26_fixed :
    FixedYReceipt 2 ⟨9, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y09_t00_26 : RowTileReceipt 2 9 10 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨9, by decide⟩ 0 26 receipt_row_02_y09_t00_26_fixed

private theorem receipt_row_02_y10_t00_26_fixed :
    FixedYReceipt 2 ⟨10, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y10_t00_26 : RowTileReceipt 2 10 11 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨10, by decide⟩ 0 26 receipt_row_02_y10_t00_26_fixed

private theorem receipt_row_02_y11_t00_26_fixed :
    FixedYReceipt 2 ⟨11, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y11_t00_26 : RowTileReceipt 2 11 12 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨11, by decide⟩ 0 26 receipt_row_02_y11_t00_26_fixed

theorem receipt_row_02_band_12_14 : RowBandReceipt 2 12 14 := by decide +kernel

theorem receipt_row_02_band_14_16 : RowBandReceipt 2 14 16 := by decide +kernel

theorem receipt_row_02_band_16_18 : RowBandReceipt 2 16 18 := by decide +kernel

theorem receipt_row_02_band_18_20 : RowBandReceipt 2 18 20 := by decide +kernel

theorem receipt_row_02_band_20_22 : RowBandReceipt 2 20 22 := by decide +kernel

theorem receipt_row_02_band_22_23 : RowBandReceipt 2 22 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
