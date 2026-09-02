import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot01T00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_band_06_t_01_c_04_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 4 5 := by decide +kernel

theorem receipt_row_06_band_06_t_01_c_04 : RowTileReceipt 6 8 9 4 5 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 4 5
    receipt_row_06_band_06_t_01_c_04_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
