import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Band05T04
import ProximityPrize.SubmissionLower.LocatorReplacementGridFixedY

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_band_05_t_05_a_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 5 7 := by decide +kernel

theorem receipt_row_07_band_05_t_05_a : RowTileReceipt 7 7 8 5 7 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 5 7
    receipt_row_07_band_05_t_05_a_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
