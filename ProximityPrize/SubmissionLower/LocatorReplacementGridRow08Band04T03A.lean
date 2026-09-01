import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Band04T02
import ProximityPrize.SubmissionLower.LocatorReplacementGridFixedY

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_band_04_t_03_a_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 3 5 := by decide +kernel

theorem receipt_row_08_band_04_t_03_a : RowTileReceipt 8 6 7 3 5 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 3 5
    receipt_row_08_band_04_t_03_a_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
