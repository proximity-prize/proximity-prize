import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_11_y00_t00_24_fixed :
    FixedYReceipt 11 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_11_y00_t00_24 : RowTileReceipt 11 0 1 0 24 :=
  fixedYReceipt_to_rowTile 11 ⟨0, by decide⟩ 0 24 receipt_row_11_y00_t00_24_fixed

private theorem receipt_row_11_y00_t24_26_fixed :
    FixedYReceipt 11 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_11_y00_t24_26 : RowTileReceipt 11 0 1 24 26 :=
  fixedYReceipt_to_rowTile 11 ⟨0, by decide⟩ 24 26 receipt_row_11_y00_t24_26_fixed

private theorem receipt_row_11_y01_t00_24_fixed :
    FixedYReceipt 11 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_11_y01_t00_24 : RowTileReceipt 11 1 2 0 24 :=
  fixedYReceipt_to_rowTile 11 ⟨1, by decide⟩ 0 24 receipt_row_11_y01_t00_24_fixed

private theorem receipt_row_11_y01_t24_26_fixed :
    FixedYReceipt 11 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_11_y01_t24_26 : RowTileReceipt 11 1 2 24 26 :=
  fixedYReceipt_to_rowTile 11 ⟨1, by decide⟩ 24 26 receipt_row_11_y01_t24_26_fixed

private theorem receipt_row_11_y02_t00_24_fixed :
    FixedYReceipt 11 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_11_y02_t00_24 : RowTileReceipt 11 2 3 0 24 :=
  fixedYReceipt_to_rowTile 11 ⟨2, by decide⟩ 0 24 receipt_row_11_y02_t00_24_fixed

private theorem receipt_row_11_y02_t24_26_fixed :
    FixedYReceipt 11 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_11_y02_t24_26 : RowTileReceipt 11 2 3 24 26 :=
  fixedYReceipt_to_rowTile 11 ⟨2, by decide⟩ 24 26 receipt_row_11_y02_t24_26_fixed

theorem receipt_row_11_band_03_05 : RowBandReceipt 11 3 5 := by decide +kernel

theorem receipt_row_11_band_05_07 : RowBandReceipt 11 5 7 := by decide +kernel

theorem receipt_row_11_band_07_09 : RowBandReceipt 11 7 9 := by decide +kernel

theorem receipt_row_11_band_09_11 : RowBandReceipt 11 9 11 := by decide +kernel

theorem receipt_row_11_band_11_13 : RowBandReceipt 11 11 13 := by decide +kernel

theorem receipt_row_11_band_13_15 : RowBandReceipt 11 13 15 := by decide +kernel

theorem receipt_row_11_band_15_17 : RowBandReceipt 11 15 17 := by decide +kernel

theorem receipt_row_11_band_17_19 : RowBandReceipt 11 17 19 := by decide +kernel

theorem receipt_row_11_band_19_23 : RowBandReceipt 11 19 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
