import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_00_y00_t00_24_fixed :
    FixedYReceipt 0 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_00_y00_t00_24 : RowTileReceipt 0 0 1 0 24 :=
  fixedYReceipt_to_rowTile 0 ⟨0, by decide⟩ 0 24 receipt_row_00_y00_t00_24_fixed

private theorem receipt_row_00_y00_t24_26_fixed :
    FixedYReceipt 0 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_00_y00_t24_26 : RowTileReceipt 0 0 1 24 26 :=
  fixedYReceipt_to_rowTile 0 ⟨0, by decide⟩ 24 26 receipt_row_00_y00_t24_26_fixed

theorem receipt_row_00_band_01_03 : RowBandReceipt 0 1 3 := by decide +kernel

theorem receipt_row_00_band_03_05 : RowBandReceipt 0 3 5 := by decide +kernel

theorem receipt_row_00_band_05_07 : RowBandReceipt 0 5 7 := by decide +kernel

theorem receipt_row_00_band_07_09 : RowBandReceipt 0 7 9 := by decide +kernel

theorem receipt_row_00_band_09_11 : RowBandReceipt 0 9 11 := by decide +kernel

theorem receipt_row_00_band_11_13 : RowBandReceipt 0 11 13 := by decide +kernel

theorem receipt_row_00_band_13_15 : RowBandReceipt 0 13 15 := by decide +kernel

theorem receipt_row_00_band_15_17 : RowBandReceipt 0 15 17 := by decide +kernel

theorem receipt_row_00_band_17_19 : RowBandReceipt 0 17 19 := by decide +kernel

theorem receipt_row_00_band_19_21 : RowBandReceipt 0 19 21 := by decide +kernel

theorem receipt_row_00_band_21_23 : RowBandReceipt 0 21 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
