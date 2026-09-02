import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_y08_t17_19_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 17 19 := by decide +kernel

theorem receipt_row_06_y08_t17_19 : RowTileReceipt 6 8 9 17 19 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 17 19 receipt_row_06_y08_t17_19_fixed

private theorem receipt_row_06_y08_t19_21_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 19 21 := by decide +kernel

theorem receipt_row_06_y08_t19_21 : RowTileReceipt 6 8 9 19 21 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 19 21 receipt_row_06_y08_t19_21_fixed

private theorem receipt_row_06_y08_t21_26_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 21 26 := by decide +kernel

theorem receipt_row_06_y08_t21_26 : RowTileReceipt 6 8 9 21 26 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 21 26 receipt_row_06_y08_t21_26_fixed

theorem receipt_row_06_band_09_11 : RowBandReceipt 6 9 11 := by decide +kernel

theorem receipt_row_06_band_11_13 : RowBandReceipt 6 11 13 := by decide +kernel

theorem receipt_row_06_band_13_15 : RowBandReceipt 6 13 15 := by decide +kernel

theorem receipt_row_06_band_15_17 : RowBandReceipt 6 15 17 := by decide +kernel

theorem receipt_row_06_band_17_19 : RowBandReceipt 6 17 19 := by decide +kernel

theorem receipt_row_06_band_19_21 : RowBandReceipt 6 19 21 := by decide +kernel

theorem receipt_row_06_band_21_23 : RowBandReceipt 6 21 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
