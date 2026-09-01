import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot01T01C06

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_band_06_t_01_c_07_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 7 8 := by decide +kernel

theorem receipt_row_06_band_06_t_01_c_07 : RowTileReceipt 6 8 9 7 8 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 7 8
    receipt_row_06_band_06_t_01_c_07_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
