import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_15_y00_t00_24_fixed :
    FixedYReceipt 15 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_15_y00_t00_24 : RowTileReceipt 15 0 1 0 24 :=
  fixedYReceipt_to_rowTile 15 ⟨0, by decide⟩ 0 24 receipt_row_15_y00_t00_24_fixed

private theorem receipt_row_15_y00_t24_26_fixed :
    FixedYReceipt 15 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_15_y00_t24_26 : RowTileReceipt 15 0 1 24 26 :=
  fixedYReceipt_to_rowTile 15 ⟨0, by decide⟩ 24 26 receipt_row_15_y00_t24_26_fixed

private theorem receipt_row_15_y01_t00_24_fixed :
    FixedYReceipt 15 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_15_y01_t00_24 : RowTileReceipt 15 1 2 0 24 :=
  fixedYReceipt_to_rowTile 15 ⟨1, by decide⟩ 0 24 receipt_row_15_y01_t00_24_fixed

private theorem receipt_row_15_y01_t24_26_fixed :
    FixedYReceipt 15 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_15_y01_t24_26 : RowTileReceipt 15 1 2 24 26 :=
  fixedYReceipt_to_rowTile 15 ⟨1, by decide⟩ 24 26 receipt_row_15_y01_t24_26_fixed

private theorem receipt_row_15_y02_t00_24_fixed :
    FixedYReceipt 15 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_15_y02_t00_24 : RowTileReceipt 15 2 3 0 24 :=
  fixedYReceipt_to_rowTile 15 ⟨2, by decide⟩ 0 24 receipt_row_15_y02_t00_24_fixed

private theorem receipt_row_15_y02_t24_26_fixed :
    FixedYReceipt 15 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_15_y02_t24_26 : RowTileReceipt 15 2 3 24 26 :=
  fixedYReceipt_to_rowTile 15 ⟨2, by decide⟩ 24 26 receipt_row_15_y02_t24_26_fixed

private theorem receipt_row_15_y03_t00_24_fixed :
    FixedYReceipt 15 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_15_y03_t00_24 : RowTileReceipt 15 3 4 0 24 :=
  fixedYReceipt_to_rowTile 15 ⟨3, by decide⟩ 0 24 receipt_row_15_y03_t00_24_fixed

private theorem receipt_row_15_y03_t24_26_fixed :
    FixedYReceipt 15 ⟨3, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_15_y03_t24_26 : RowTileReceipt 15 3 4 24 26 :=
  fixedYReceipt_to_rowTile 15 ⟨3, by decide⟩ 24 26 receipt_row_15_y03_t24_26_fixed

theorem receipt_row_15_band_04_06 : RowBandReceipt 15 4 6 := by decide +kernel

theorem receipt_row_15_band_06_08 : RowBandReceipt 15 6 8 := by decide +kernel

theorem receipt_row_15_band_08_10 : RowBandReceipt 15 8 10 := by decide +kernel

theorem receipt_row_15_band_10_12 : RowBandReceipt 15 10 12 := by decide +kernel

theorem receipt_row_15_band_12_14 : RowBandReceipt 15 12 14 := by decide +kernel

theorem receipt_row_15_band_14_16 : RowBandReceipt 15 14 16 := by decide +kernel

theorem receipt_row_15_band_16_18 : RowBandReceipt 15 16 18 := by decide +kernel

theorem receipt_row_15_band_18_23 : RowBandReceipt 15 18 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
