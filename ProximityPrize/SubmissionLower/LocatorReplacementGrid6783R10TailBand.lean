import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R08Y07Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r10_0 : CoarseRouteReceipt 10 4 12 sourceC 7 := by decide +kernel
private theorem r10_1 : CoarseRouteReceipt 10 12 14 sourceC 6 := by decide +kernel
private theorem r10_2 : CoarseRouteReceipt 10 14 17 sourceC 5 := by decide +kernel
private theorem r10_3 : CoarseRouteReceipt 10 17 20 sourceC 4 := by decide +kernel
private theorem r10_4 : CoarseRouteReceipt 10 20 21 sourceAux 1 := by decide +kernel
private theorem r10_5 : CoarseRouteReceipt 10 21 22 sourceA 1 := by decide +kernel
private theorem r10_6 : CoarseInvalidReceipt 10 22 24 := by decide +kernel

theorem receipt_6783_r10_band_04_24 : RowBandReceipt 10 4 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 10 4 12 sourceC 7 r10_0
    (fun _ ↦ fastFits_of_sourceC7)
  have h1 := coarseRouteReceipt_to_rowBand 10 12 14 sourceC 6 r10_1
    (fun _ ↦ fastFits_of_sourceC6)
  have h2 := coarseRouteReceipt_to_rowBand 10 14 17 sourceC 5 r10_2
    (fun _ ↦ fastFits_of_sourceC5)
  have h3 := coarseRouteReceipt_to_rowBand 10 17 20 sourceC 4 r10_3
    (fun _ ↦ fastFits_of_sourceC4)
  have h4 := coarseRouteReceipt_to_rowBand 10 20 21 sourceAux 1 r10_4
    (fun _ ↦ fastFits_of_sourceAux)
  have h5 := coarseRouteReceipt_to_rowBand 10 21 22 sourceA 1 r10_5
    (fun _ ↦ fastFits_of_sourceA)
  have h6 := coarseInvalidReceipt_to_rowBand 10 22 24 r10_6
  exact rowBandReceipt_append 10 4 12 24 h0
    (rowBandReceipt_append 10 12 14 24 h1
    (rowBandReceipt_append 10 14 17 24 h2
    (rowBandReceipt_append 10 17 20 24 h3
    (rowBandReceipt_append 10 20 21 24 h4
    (rowBandReceipt_append 10 21 22 24 h5
    h6)))))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
