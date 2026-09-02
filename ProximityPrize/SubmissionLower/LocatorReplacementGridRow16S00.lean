import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_16_y00_t00_24_fixed :
    FixedYReceipt 16 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_16_y00_t00_24 : RowTileReceipt 16 0 1 0 24 :=
  fixedYReceipt_to_rowTile 16 ⟨0, by decide⟩ 0 24 receipt_row_16_y00_t00_24_fixed

private theorem receipt_row_16_y00_t24_26_fixed :
    FixedYReceipt 16 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_16_y00_t24_26 : RowTileReceipt 16 0 1 24 26 :=
  fixedYReceipt_to_rowTile 16 ⟨0, by decide⟩ 24 26 receipt_row_16_y00_t24_26_fixed

private theorem receipt_row_16_y01_t00_24_fixed :
    FixedYReceipt 16 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_16_y01_t00_24 : RowTileReceipt 16 1 2 0 24 :=
  fixedYReceipt_to_rowTile 16 ⟨1, by decide⟩ 0 24 receipt_row_16_y01_t00_24_fixed

private theorem receipt_row_16_y01_t24_26_fixed :
    FixedYReceipt 16 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_16_y01_t24_26 : RowTileReceipt 16 1 2 24 26 :=
  fixedYReceipt_to_rowTile 16 ⟨1, by decide⟩ 24 26 receipt_row_16_y01_t24_26_fixed

private theorem receipt_row_16_y02_t00_24_fixed :
    FixedYReceipt 16 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_16_y02_t00_24 : RowTileReceipt 16 2 3 0 24 :=
  fixedYReceipt_to_rowTile 16 ⟨2, by decide⟩ 0 24 receipt_row_16_y02_t00_24_fixed

private theorem receipt_row_16_y02_t24_26_fixed :
    FixedYReceipt 16 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_16_y02_t24_26 : RowTileReceipt 16 2 3 24 26 :=
  fixedYReceipt_to_rowTile 16 ⟨2, by decide⟩ 24 26 receipt_row_16_y02_t24_26_fixed

private theorem receipt_row_16_y03_t00_25_fixed :
    FixedYReceipt 16 ⟨3, by decide⟩ 0 25 := by decide +kernel

theorem receipt_row_16_y03_t00_25 : RowTileReceipt 16 3 4 0 25 :=
  fixedYReceipt_to_rowTile 16 ⟨3, by decide⟩ 0 25 receipt_row_16_y03_t00_25_fixed

private theorem receipt_row_16_y03_t25_26_fixed :
    FixedYReceipt 16 ⟨3, by decide⟩ 25 26 := by decide +kernel

theorem receipt_row_16_y03_t25_26 : RowTileReceipt 16 3 4 25 26 :=
  fixedYReceipt_to_rowTile 16 ⟨3, by decide⟩ 25 26 receipt_row_16_y03_t25_26_fixed

theorem receipt_row_16_band_04_06 : RowBandReceipt 16 4 6 := by decide +kernel

theorem receipt_row_16_band_06_08 : RowBandReceipt 16 6 8 := by decide +kernel

theorem receipt_row_16_band_08_10 : RowBandReceipt 16 8 10 := by decide +kernel

theorem receipt_row_16_band_10_12 : RowBandReceipt 16 10 12 := by decide +kernel

theorem receipt_row_16_band_12_14 : RowBandReceipt 16 12 14 := by decide +kernel

theorem receipt_row_16_band_14_16 : RowBandReceipt 16 14 16 := by decide +kernel

theorem receipt_row_16_band_16_18 : RowBandReceipt 16 16 18 := by decide +kernel

theorem receipt_row_16_band_18_23 : RowBandReceipt 16 18 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
