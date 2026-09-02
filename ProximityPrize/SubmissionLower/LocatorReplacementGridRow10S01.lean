import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_10_y02_t00_08_fixed :
    FixedYReceipt 10 ⟨2, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_10_y02_t00_08 : RowTileReceipt 10 2 3 0 8 :=
  fixedYReceipt_to_rowTile 10 ⟨2, by decide⟩ 0 8 receipt_row_10_y02_t00_08_fixed

private theorem receipt_row_10_y02_t08_26_fixed :
    FixedYReceipt 10 ⟨2, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_10_y02_t08_26 : RowTileReceipt 10 2 3 8 26 :=
  fixedYReceipt_to_rowTile 10 ⟨2, by decide⟩ 8 26 receipt_row_10_y02_t08_26_fixed

theorem receipt_row_10_band_03_05 : RowBandReceipt 10 3 5 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
