import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_y09_t02_26_fixed :
    FixedYReceipt 4 ⟨9, by decide⟩ 2 26 := by decide +kernel

theorem receipt_row_04_y09_t02_26 : RowTileReceipt 4 9 10 2 26 :=
  fixedYReceipt_to_rowTile 4 ⟨9, by decide⟩ 2 26 receipt_row_04_y09_t02_26_fixed

theorem receipt_row_04_band_10_12 : RowBandReceipt 4 10 12 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
