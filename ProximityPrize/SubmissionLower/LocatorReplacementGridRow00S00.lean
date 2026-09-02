import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_00_y00_t00_24_fixed :
    FixedYReceipt 0 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_00_y00_t00_24 : RowTileReceipt 0 0 1 0 24 :=
  fixedYReceipt_to_rowTile 0 ⟨0, by decide⟩ 0 24 receipt_row_00_y00_t00_24_fixed

private theorem receipt_row_00_y00_t24_26_fixed :
    FixedYReceipt 0 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_00_y00_t24_26 : RowTileReceipt 0 0 1 24 26 :=
  fixedYReceipt_to_rowTile 0 ⟨0, by decide⟩ 24 26 receipt_row_00_y00_t24_26_fixed

theorem receipt_row_00_band_01_03 : RowBandReceipt 0 1 3 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
