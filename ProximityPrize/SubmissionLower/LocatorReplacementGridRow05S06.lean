import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_y09_t06_08_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 6 8 := by decide +kernel

theorem receipt_row_05_y09_t06_08 : RowTileReceipt 5 9 10 6 8 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 6 8 receipt_row_05_y09_t06_08_fixed

private theorem receipt_row_05_y09_t08_26_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_05_y09_t08_26 : RowTileReceipt 5 9 10 8 26 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 8 26 receipt_row_05_y09_t08_26_fixed

theorem receipt_row_05_band_10_12 : RowBandReceipt 5 10 12 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
