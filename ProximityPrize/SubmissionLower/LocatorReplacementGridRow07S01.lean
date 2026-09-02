import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y07_t08_09_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 8 9 := by decide +kernel

theorem receipt_row_07_y07_t08_09 : RowTileReceipt 7 7 8 8 9 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 8 9 receipt_row_07_y07_t08_09_fixed

private theorem receipt_row_07_y07_t09_10_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 9 10 := by decide +kernel

theorem receipt_row_07_y07_t09_10 : RowTileReceipt 7 7 8 9 10 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 9 10 receipt_row_07_y07_t09_10_fixed

private theorem receipt_row_07_y07_t10_11_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 10 11 := by decide +kernel

theorem receipt_row_07_y07_t10_11 : RowTileReceipt 7 7 8 10 11 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 10 11 receipt_row_07_y07_t10_11_fixed

private theorem receipt_row_07_y07_t11_13_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 11 13 := by decide +kernel

theorem receipt_row_07_y07_t11_13 : RowTileReceipt 7 7 8 11 13 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 11 13 receipt_row_07_y07_t11_13_fixed

private theorem receipt_row_07_y07_t13_15_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 13 15 := by decide +kernel

theorem receipt_row_07_y07_t13_15 : RowTileReceipt 7 7 8 13 15 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 13 15 receipt_row_07_y07_t13_15_fixed

private theorem receipt_row_07_y07_t15_17_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 15 17 := by decide +kernel

theorem receipt_row_07_y07_t15_17 : RowTileReceipt 7 7 8 15 17 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 15 17 receipt_row_07_y07_t15_17_fixed

private theorem receipt_row_07_y07_t17_25_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 17 25 := by decide +kernel

theorem receipt_row_07_y07_t17_25 : RowTileReceipt 7 7 8 17 25 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 17 25 receipt_row_07_y07_t17_25_fixed

private theorem receipt_row_07_y07_t25_26_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 25 26 := by decide +kernel

theorem receipt_row_07_y07_t25_26 : RowTileReceipt 7 7 8 25 26 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 25 26 receipt_row_07_y07_t25_26_fixed

theorem receipt_row_07_band_08_10 : RowBandReceipt 7 8 10 := by decide +kernel

theorem receipt_row_07_band_10_12 : RowBandReceipt 7 10 12 := by decide +kernel

theorem receipt_row_07_band_12_14 : RowBandReceipt 7 12 14 := by decide +kernel

theorem receipt_row_07_band_14_16 : RowBandReceipt 7 14 16 := by decide +kernel

theorem receipt_row_07_band_16_18 : RowBandReceipt 7 16 18 := by decide +kernel

theorem receipt_row_07_band_18_20 : RowBandReceipt 7 18 20 := by decide +kernel

theorem receipt_row_07_band_20_23 : RowBandReceipt 7 20 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
