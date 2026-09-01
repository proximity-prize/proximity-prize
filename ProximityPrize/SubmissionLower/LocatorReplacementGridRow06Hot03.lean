import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot03Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_band_07_t_04_fixed :
    FixedYReceipt 6 ⟨9, by decide⟩ 16 20 := by decide +kernel

theorem receipt_row_06_band_07_t_04 : RowTileReceipt 6 9 10 16 20 :=
  fixedYReceipt_to_rowTile 6 ⟨9, by decide⟩ 16 20
    receipt_row_06_band_07_t_04_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
