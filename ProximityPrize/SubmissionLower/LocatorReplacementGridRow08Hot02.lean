import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot02Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_04_t_02 : RowTileReceipt 8 6 7 2 3 := by decide +kernel

private theorem receipt_row_08_band_04_t_03_a0_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 3 4 := by decide +kernel

theorem receipt_row_08_band_04_t_03_a0 : RowTileReceipt 8 6 7 3 4 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 3 4
    receipt_row_08_band_04_t_03_a0_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
