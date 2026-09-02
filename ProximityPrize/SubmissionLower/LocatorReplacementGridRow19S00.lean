import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_19_y00_t00_24_fixed :
    FixedYReceipt 19 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_19_y00_t00_24 : RowTileReceipt 19 0 1 0 24 :=
  fixedYReceipt_to_rowTile 19 ⟨0, by decide⟩ 0 24 receipt_row_19_y00_t00_24_fixed

private theorem receipt_row_19_y00_t24_26_fixed :
    FixedYReceipt 19 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_19_y00_t24_26 : RowTileReceipt 19 0 1 24 26 :=
  fixedYReceipt_to_rowTile 19 ⟨0, by decide⟩ 24 26 receipt_row_19_y00_t24_26_fixed

private theorem receipt_row_19_y01_t00_12_fixed :
    FixedYReceipt 19 ⟨1, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_19_y01_t00_12 : RowTileReceipt 19 1 2 0 12 :=
  fixedYReceipt_to_rowTile 19 ⟨1, by decide⟩ 0 12 receipt_row_19_y01_t00_12_fixed

private theorem receipt_row_19_y01_t12_26_fixed :
    FixedYReceipt 19 ⟨1, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_19_y01_t12_26 : RowTileReceipt 19 1 2 12 26 :=
  fixedYReceipt_to_rowTile 19 ⟨1, by decide⟩ 12 26 receipt_row_19_y01_t12_26_fixed

private theorem receipt_row_19_y02_t00_08_fixed :
    FixedYReceipt 19 ⟨2, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_19_y02_t00_08 : RowTileReceipt 19 2 3 0 8 :=
  fixedYReceipt_to_rowTile 19 ⟨2, by decide⟩ 0 8 receipt_row_19_y02_t00_08_fixed

private theorem receipt_row_19_y02_t08_26_fixed :
    FixedYReceipt 19 ⟨2, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_19_y02_t08_26 : RowTileReceipt 19 2 3 8 26 :=
  fixedYReceipt_to_rowTile 19 ⟨2, by decide⟩ 8 26 receipt_row_19_y02_t08_26_fixed

private theorem receipt_row_19_y03_t00_20_fixed :
    FixedYReceipt 19 ⟨3, by decide⟩ 0 20 := by decide +kernel

theorem receipt_row_19_y03_t00_20 : RowTileReceipt 19 3 4 0 20 :=
  fixedYReceipt_to_rowTile 19 ⟨3, by decide⟩ 0 20 receipt_row_19_y03_t00_20_fixed

private theorem receipt_row_19_y03_t20_26_fixed :
    FixedYReceipt 19 ⟨3, by decide⟩ 20 26 := by decide +kernel

theorem receipt_row_19_y03_t20_26 : RowTileReceipt 19 3 4 20 26 :=
  fixedYReceipt_to_rowTile 19 ⟨3, by decide⟩ 20 26 receipt_row_19_y03_t20_26_fixed

theorem receipt_row_19_band_04_06 : RowBandReceipt 19 4 6 := by decide +kernel

theorem receipt_row_19_band_06_08 : RowBandReceipt 19 6 8 := by decide +kernel

theorem receipt_row_19_band_08_10 : RowBandReceipt 19 8 10 := by decide +kernel

theorem receipt_row_19_band_10_12 : RowBandReceipt 19 10 12 := by decide +kernel

theorem receipt_row_19_band_12_14 : RowBandReceipt 19 12 14 := by decide +kernel

theorem receipt_row_19_band_14_16 : RowBandReceipt 19 14 16 := by decide +kernel

theorem receipt_row_19_band_16_18 : RowBandReceipt 19 16 18 := by decide +kernel

theorem receipt_row_19_band_18_23 : RowBandReceipt 19 18 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
