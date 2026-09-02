import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y08Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r08_0 : CoarseRouteReceipt 8 8 9 sourceC 9 := by decide +kernel
private theorem r08_1 : CoarseRouteReceipt 8 9 11 sourceC 8 := by decide +kernel
private theorem r08_2 : CoarseRouteReceipt 8 11 12 sourceC 7 := by decide +kernel
private theorem r08_3 : CoarseRouteReceipt 8 12 15 sourceC 6 := by decide +kernel
private theorem r08_4 : CoarseRouteReceipt 8 15 18 sourceC 5 := by decide +kernel
private theorem r08_5 : CoarseRouteReceipt 8 18 21 sourceC 4 := by decide +kernel
private theorem r08_6 : CoarseRouteReceipt 8 21 22 sourceAux 1 := by decide +kernel
private theorem r08_7 : CoarseInvalidReceipt 8 22 24 := by decide +kernel

theorem receipt_6783_r08_band_08_24 : RowBandReceipt 8 8 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 8 8 9 sourceC 9 r08_0
    (fun _ ↦ fastFits_of_sourceC9)
  have h1 := coarseRouteReceipt_to_rowBand 8 9 11 sourceC 8 r08_1
    (fun _ ↦ fastFits_of_sourceC8)
  have h2 := coarseRouteReceipt_to_rowBand 8 11 12 sourceC 7 r08_2
    (fun _ ↦ fastFits_of_sourceC7)
  have h3 := coarseRouteReceipt_to_rowBand 8 12 15 sourceC 6 r08_3
    (fun _ ↦ fastFits_of_sourceC6)
  have h4 := coarseRouteReceipt_to_rowBand 8 15 18 sourceC 5 r08_4
    (fun _ ↦ fastFits_of_sourceC5)
  have h5 := coarseRouteReceipt_to_rowBand 8 18 21 sourceC 4 r08_5
    (fun _ ↦ fastFits_of_sourceC4)
  have h6 := coarseRouteReceipt_to_rowBand 8 21 22 sourceAux 1 r08_6
    (fun _ ↦ fastFits_of_sourceAux)
  have h7 := coarseInvalidReceipt_to_rowBand 8 22 24 r08_7
  exact rowBandReceipt_append 8 8 9 24 h0
    (rowBandReceipt_append 8 9 11 24 h1
    (rowBandReceipt_append 8 11 12 24 h2
    (rowBandReceipt_append 8 12 15 24 h3
    (rowBandReceipt_append 8 15 18 24 h4
    (rowBandReceipt_append 8 18 21 24 h5
    (rowBandReceipt_append 8 21 22 24 h6
    h7))))))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
