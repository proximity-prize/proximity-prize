import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y03Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r12_0 : CoarseRouteReceipt 12 1 14 sourceC 6 := by decide +kernel
private theorem r12_1 : CoarseRouteReceipt 12 14 17 sourceC 5 := by decide +kernel
private theorem r12_2 : CoarseRouteReceipt 12 17 20 sourceC 4 := by decide +kernel
private theorem r12_3 : CoarseRouteReceipt 12 20 21 sourceAux 1 := by decide +kernel
private theorem r12_4 : CoarseInvalidReceipt 12 21 24 := by decide +kernel

theorem receipt_6783_r12_band_01_24 : RowBandReceipt 12 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 12 1 14 sourceC 6 r12_0
    (fun _ ↦ fastFits_of_sourceC6)
  have h1 := coarseRouteReceipt_to_rowBand 12 14 17 sourceC 5 r12_1
    (fun _ ↦ fastFits_of_sourceC5)
  have h2 := coarseRouteReceipt_to_rowBand 12 17 20 sourceC 4 r12_2
    (fun _ ↦ fastFits_of_sourceC4)
  have h3 := coarseRouteReceipt_to_rowBand 12 20 21 sourceAux 1 r12_3
    (fun _ ↦ fastFits_of_sourceAux)
  have h4 := coarseInvalidReceipt_to_rowBand 12 21 24 r12_4
  exact rowBandReceipt_append 12 1 14 24 h0
    (rowBandReceipt_append 12 14 17 24 h1
    (rowBandReceipt_append 12 17 20 24 h2
    (rowBandReceipt_append 12 20 21 24 h3
    h4)))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
