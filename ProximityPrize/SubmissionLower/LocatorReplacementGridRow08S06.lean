import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_y06_t06_26_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 6 26 := by decide +kernel

theorem receipt_row_08_y06_t06_26 : RowTileReceipt 8 6 7 6 26 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 6 26 receipt_row_08_y06_t06_26_fixed

theorem receipt_row_08_band_07_09 : RowBandReceipt 8 7 9 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
