import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_10_band_00_02 : RowBandReceipt 10 0 2 := by decide +kernel

private theorem receipt_row_10_y02_t00_24_fixed :
    FixedYReceipt 10 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_10_y02_t00_24 : RowTileReceipt 10 2 3 0 24 :=
  fixedYReceipt_to_rowTile 10 ⟨2, by decide⟩ 0 24 receipt_row_10_y02_t00_24_fixed

private theorem receipt_row_10_y02_t24_29_fixed :
    FixedYReceipt 10 ⟨2, by decide⟩ 24 29 := by decide +kernel

theorem receipt_row_10_y02_t24_29 : RowTileReceipt 10 2 3 24 29 :=
  fixedYReceipt_to_rowTile 10 ⟨2, by decide⟩ 24 29 receipt_row_10_y02_t24_29_fixed

private theorem receipt_row_10_y03_t00_02_fixed :
    FixedYReceipt 10 ⟨3, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_10_y03_t00_02 : RowTileReceipt 10 3 4 0 2 :=
  fixedYReceipt_to_rowTile 10 ⟨3, by decide⟩ 0 2 receipt_row_10_y03_t00_02_fixed

private theorem receipt_row_10_y03_t02_04_fixed :
    FixedYReceipt 10 ⟨3, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_10_y03_t02_04 : RowTileReceipt 10 3 4 2 4 :=
  fixedYReceipt_to_rowTile 10 ⟨3, by decide⟩ 2 4 receipt_row_10_y03_t02_04_fixed

private theorem receipt_row_10_y03_t04_28_fixed :
    FixedYReceipt 10 ⟨3, by decide⟩ 4 28 := by decide +kernel

theorem receipt_row_10_y03_t04_28 : RowTileReceipt 10 3 4 4 28 :=
  fixedYReceipt_to_rowTile 10 ⟨3, by decide⟩ 4 28 receipt_row_10_y03_t04_28_fixed

private theorem receipt_row_10_y03_t28_29_fixed :
    FixedYReceipt 10 ⟨3, by decide⟩ 28 29 := by decide +kernel

theorem receipt_row_10_y03_t28_29 : RowTileReceipt 10 3 4 28 29 :=
  fixedYReceipt_to_rowTile 10 ⟨3, by decide⟩ 28 29 receipt_row_10_y03_t28_29_fixed

theorem receipt_row_10_band_04_06 : RowBandReceipt 10 4 6 := by decide +kernel

theorem receipt_row_10_band_06_08 : RowBandReceipt 10 6 8 := by decide +kernel

theorem receipt_row_10_band_08_10 : RowBandReceipt 10 8 10 := by decide +kernel

theorem receipt_row_10_band_10_12 : RowBandReceipt 10 10 12 := by decide +kernel

theorem receipt_row_10_band_12_14 : RowBandReceipt 10 12 14 := by decide +kernel

theorem receipt_row_10_band_14_16 : RowBandReceipt 10 14 16 := by decide +kernel

theorem receipt_row_10_band_16_18 : RowBandReceipt 10 16 18 := by decide +kernel

theorem receipt_row_10_band_18_20 : RowBandReceipt 10 18 20 := by decide +kernel

theorem receipt_row_10_band_20_22 : RowBandReceipt 10 20 22 := by decide +kernel

theorem receipt_row_10_band_22_25 : RowBandReceipt 10 22 25 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
