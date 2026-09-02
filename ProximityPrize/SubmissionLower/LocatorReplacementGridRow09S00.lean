import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_band_00_02 : RowBandReceipt 9 0 2 := by decide +kernel

private theorem receipt_row_09_y02_t00_24_fixed :
    FixedYReceipt 9 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_09_y02_t00_24 : RowTileReceipt 9 2 3 0 24 :=
  fixedYReceipt_to_rowTile 9 ⟨2, by decide⟩ 0 24 receipt_row_09_y02_t00_24_fixed

private theorem receipt_row_09_y02_t24_29_fixed :
    FixedYReceipt 9 ⟨2, by decide⟩ 24 29 := by decide +kernel

theorem receipt_row_09_y02_t24_29 : RowTileReceipt 9 2 3 24 29 :=
  fixedYReceipt_to_rowTile 9 ⟨2, by decide⟩ 24 29 receipt_row_09_y02_t24_29_fixed

private theorem receipt_row_09_y03_t00_08_fixed :
    FixedYReceipt 9 ⟨3, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_09_y03_t00_08 : RowTileReceipt 9 3 4 0 8 :=
  fixedYReceipt_to_rowTile 9 ⟨3, by decide⟩ 0 8 receipt_row_09_y03_t00_08_fixed

private theorem receipt_row_09_y03_t08_29_fixed :
    FixedYReceipt 9 ⟨3, by decide⟩ 8 29 := by decide +kernel

theorem receipt_row_09_y03_t08_29 : RowTileReceipt 9 3 4 8 29 :=
  fixedYReceipt_to_rowTile 9 ⟨3, by decide⟩ 8 29 receipt_row_09_y03_t08_29_fixed

private theorem receipt_row_09_y04_t00_02_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_09_y04_t00_02 : RowTileReceipt 9 4 5 0 2 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 0 2 receipt_row_09_y04_t00_02_fixed

private theorem receipt_row_09_y04_t02_04_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_09_y04_t02_04 : RowTileReceipt 9 4 5 2 4 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 2 4 receipt_row_09_y04_t02_04_fixed

private theorem receipt_row_09_y04_t04_06_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 4 6 := by decide +kernel

theorem receipt_row_09_y04_t04_06 : RowTileReceipt 9 4 5 4 6 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 4 6 receipt_row_09_y04_t04_06_fixed

private theorem receipt_row_09_y04_t06_29_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 6 29 := by decide +kernel

theorem receipt_row_09_y04_t06_29 : RowTileReceipt 9 4 5 6 29 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 6 29 receipt_row_09_y04_t06_29_fixed

private theorem receipt_row_09_y05_t00_10_fixed :
    FixedYReceipt 9 ⟨5, by decide⟩ 0 10 := by decide +kernel

theorem receipt_row_09_y05_t00_10 : RowTileReceipt 9 5 6 0 10 :=
  fixedYReceipt_to_rowTile 9 ⟨5, by decide⟩ 0 10 receipt_row_09_y05_t00_10_fixed

private theorem receipt_row_09_y05_t10_29_fixed :
    FixedYReceipt 9 ⟨5, by decide⟩ 10 29 := by decide +kernel

theorem receipt_row_09_y05_t10_29 : RowTileReceipt 9 5 6 10 29 :=
  fixedYReceipt_to_rowTile 9 ⟨5, by decide⟩ 10 29 receipt_row_09_y05_t10_29_fixed

theorem receipt_row_09_band_06_08 : RowBandReceipt 9 6 8 := by decide +kernel

theorem receipt_row_09_band_08_10 : RowBandReceipt 9 8 10 := by decide +kernel

theorem receipt_row_09_band_10_12 : RowBandReceipt 9 10 12 := by decide +kernel

theorem receipt_row_09_band_12_14 : RowBandReceipt 9 12 14 := by decide +kernel

theorem receipt_row_09_band_14_16 : RowBandReceipt 9 14 16 := by decide +kernel

theorem receipt_row_09_band_16_18 : RowBandReceipt 9 16 18 := by decide +kernel

theorem receipt_row_09_band_18_20 : RowBandReceipt 9 18 20 := by decide +kernel

theorem receipt_row_09_band_20_22 : RowBandReceipt 9 20 22 := by decide +kernel

theorem receipt_row_09_band_22_25 : RowBandReceipt 9 22 25 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
