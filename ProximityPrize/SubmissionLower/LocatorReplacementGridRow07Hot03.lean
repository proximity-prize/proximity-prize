import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Hot03Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_band_05_t_05_b1_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 8 9 := by decide +kernel

theorem receipt_row_07_band_05_t_05_b1 : RowTileReceipt 7 7 8 8 9 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 8 9
    receipt_row_07_band_05_t_05_b1_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
