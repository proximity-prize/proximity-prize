import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_17_y00_t00_24_fixed :
    FixedYReceipt 17 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_17_y00_t00_24 : RowTileReceipt 17 0 1 0 24 :=
  fixedYReceipt_to_rowTile 17 ⟨0, by decide⟩ 0 24 receipt_row_17_y00_t00_24_fixed

private theorem receipt_row_17_y00_t24_26_fixed :
    FixedYReceipt 17 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_17_y00_t24_26 : RowTileReceipt 17 0 1 24 26 :=
  fixedYReceipt_to_rowTile 17 ⟨0, by decide⟩ 24 26 receipt_row_17_y00_t24_26_fixed

private theorem receipt_row_17_y01_t00_24_fixed :
    FixedYReceipt 17 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_17_y01_t00_24 : RowTileReceipt 17 1 2 0 24 :=
  fixedYReceipt_to_rowTile 17 ⟨1, by decide⟩ 0 24 receipt_row_17_y01_t00_24_fixed

private theorem receipt_row_17_y01_t24_26_fixed :
    FixedYReceipt 17 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_17_y01_t24_26 : RowTileReceipt 17 1 2 24 26 :=
  fixedYReceipt_to_rowTile 17 ⟨1, by decide⟩ 24 26 receipt_row_17_y01_t24_26_fixed

private theorem receipt_row_17_y02_t00_24_fixed :
    FixedYReceipt 17 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_17_y02_t00_24 : RowTileReceipt 17 2 3 0 24 :=
  fixedYReceipt_to_rowTile 17 ⟨2, by decide⟩ 0 24 receipt_row_17_y02_t00_24_fixed

private theorem receipt_row_17_y02_t24_26_fixed :
    FixedYReceipt 17 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_17_y02_t24_26 : RowTileReceipt 17 2 3 24 26 :=
  fixedYReceipt_to_rowTile 17 ⟨2, by decide⟩ 24 26 receipt_row_17_y02_t24_26_fixed

private theorem receipt_row_17_y03_t00_26_fixed :
    FixedYReceipt 17 ⟨3, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_17_y03_t00_26 : RowTileReceipt 17 3 4 0 26 :=
  fixedYReceipt_to_rowTile 17 ⟨3, by decide⟩ 0 26 receipt_row_17_y03_t00_26_fixed

theorem receipt_row_17_band_04_06 : RowBandReceipt 17 4 6 := by decide +kernel

theorem receipt_row_17_band_06_08 : RowBandReceipt 17 6 8 := by decide +kernel

theorem receipt_row_17_band_08_10 : RowBandReceipt 17 8 10 := by decide +kernel

theorem receipt_row_17_band_10_12 : RowBandReceipt 17 10 12 := by decide +kernel

theorem receipt_row_17_band_12_14 : RowBandReceipt 17 12 14 := by decide +kernel

theorem receipt_row_17_band_14_16 : RowBandReceipt 17 14 16 := by decide +kernel

theorem receipt_row_17_band_16_18 : RowBandReceipt 17 16 18 := by decide +kernel

theorem receipt_row_17_band_18_23 : RowBandReceipt 17 18 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
