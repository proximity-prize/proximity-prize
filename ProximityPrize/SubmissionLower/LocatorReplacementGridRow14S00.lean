import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_14_y00_t00_24_fixed :
    FixedYReceipt 14 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_14_y00_t00_24 : RowTileReceipt 14 0 1 0 24 :=
  fixedYReceipt_to_rowTile 14 ⟨0, by decide⟩ 0 24 receipt_row_14_y00_t00_24_fixed

private theorem receipt_row_14_y00_t24_26_fixed :
    FixedYReceipt 14 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_14_y00_t24_26 : RowTileReceipt 14 0 1 24 26 :=
  fixedYReceipt_to_rowTile 14 ⟨0, by decide⟩ 24 26 receipt_row_14_y00_t24_26_fixed

private theorem receipt_row_14_y01_t00_24_fixed :
    FixedYReceipt 14 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_14_y01_t00_24 : RowTileReceipt 14 1 2 0 24 :=
  fixedYReceipt_to_rowTile 14 ⟨1, by decide⟩ 0 24 receipt_row_14_y01_t00_24_fixed

private theorem receipt_row_14_y01_t24_26_fixed :
    FixedYReceipt 14 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_14_y01_t24_26 : RowTileReceipt 14 1 2 24 26 :=
  fixedYReceipt_to_rowTile 14 ⟨1, by decide⟩ 24 26 receipt_row_14_y01_t24_26_fixed

private theorem receipt_row_14_y02_t00_24_fixed :
    FixedYReceipt 14 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_14_y02_t00_24 : RowTileReceipt 14 2 3 0 24 :=
  fixedYReceipt_to_rowTile 14 ⟨2, by decide⟩ 0 24 receipt_row_14_y02_t00_24_fixed

private theorem receipt_row_14_y02_t24_26_fixed :
    FixedYReceipt 14 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_14_y02_t24_26 : RowTileReceipt 14 2 3 24 26 :=
  fixedYReceipt_to_rowTile 14 ⟨2, by decide⟩ 24 26 receipt_row_14_y02_t24_26_fixed

private theorem receipt_row_14_y03_t00_24_fixed :
    FixedYReceipt 14 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_14_y03_t00_24 : RowTileReceipt 14 3 4 0 24 :=
  fixedYReceipt_to_rowTile 14 ⟨3, by decide⟩ 0 24 receipt_row_14_y03_t00_24_fixed

private theorem receipt_row_14_y03_t24_26_fixed :
    FixedYReceipt 14 ⟨3, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_14_y03_t24_26 : RowTileReceipt 14 3 4 24 26 :=
  fixedYReceipt_to_rowTile 14 ⟨3, by decide⟩ 24 26 receipt_row_14_y03_t24_26_fixed

theorem receipt_row_14_band_04_06 : RowBandReceipt 14 4 6 := by decide +kernel

theorem receipt_row_14_band_06_08 : RowBandReceipt 14 6 8 := by decide +kernel

theorem receipt_row_14_band_08_10 : RowBandReceipt 14 8 10 := by decide +kernel

theorem receipt_row_14_band_10_12 : RowBandReceipt 14 10 12 := by decide +kernel

theorem receipt_row_14_band_12_14 : RowBandReceipt 14 12 14 := by decide +kernel

theorem receipt_row_14_band_14_16 : RowBandReceipt 14 14 16 := by decide +kernel

theorem receipt_row_14_band_16_18 : RowBandReceipt 14 16 18 := by decide +kernel

theorem receipt_row_14_band_18_23 : RowBandReceipt 14 18 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
