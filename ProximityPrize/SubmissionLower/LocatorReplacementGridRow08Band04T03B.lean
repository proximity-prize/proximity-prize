import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Band04T02
import ProximityPrize.SubmissionLower.LocatorReplacementGridFixedY

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_band_04_t_03_b_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 5 8 := by decide +kernel

theorem receipt_row_08_band_04_t_03_b : RowTileReceipt 8 6 7 5 8 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 5 8
    receipt_row_08_band_04_t_03_b_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
