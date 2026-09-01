import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot01T01C04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_band_06_t_01_c_05_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 5 6 := by decide +kernel

theorem receipt_row_06_band_06_t_01_c_05 : RowTileReceipt 6 8 9 5 6 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 5 6
    receipt_row_06_band_06_t_01_c_05_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
