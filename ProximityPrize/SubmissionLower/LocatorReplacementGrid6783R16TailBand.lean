import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R14Y00Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r16_0 : CoarseRouteReceipt 16 1 16 sourceC 5 := by decide +kernel
private theorem r16_1 : CoarseRouteReceipt 16 16 18 sourceC 4 := by decide +kernel
private theorem r16_2 : CoarseRouteReceipt 16 18 20 sourceAux 1 := by decide +kernel
private theorem r16_3 : CoarseInvalidReceipt 16 20 24 := by decide +kernel

theorem receipt_6783_r16_band_01_24 : RowBandReceipt 16 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 16 1 16 sourceC 5 r16_0
    (fun _ ↦ fastFits_of_sourceC5)
  have h1 := coarseRouteReceipt_to_rowBand 16 16 18 sourceC 4 r16_1
    (fun _ ↦ fastFits_of_sourceC4)
  have h2 := coarseRouteReceipt_to_rowBand 16 18 20 sourceAux 1 r16_2
    (fun _ ↦ fastFits_of_sourceAux)
  have h3 := coarseInvalidReceipt_to_rowBand 16 20 24 r16_3
  exact rowBandReceipt_append 16 1 16 24 h0
    (rowBandReceipt_append 16 16 18 24 h1
    (rowBandReceipt_append 16 18 20 24 h2
    h3))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
