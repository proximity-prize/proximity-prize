import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R11Y00Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r13_0 : CoarseRouteReceipt 13 1 13 sourceC 6 := by decide +kernel
private theorem r13_1 : CoarseRouteReceipt 13 13 17 sourceC 5 := by decide +kernel
private theorem r13_2 : CoarseRouteReceipt 13 17 19 sourceC 4 := by decide +kernel
private theorem r13_3 : CoarseRouteReceipt 13 19 20 sourceAux 1 := by decide +kernel
private theorem r13_4 : CoarseRouteReceipt 13 20 21 sourceA 1 := by decide +kernel
private theorem r13_5 : CoarseInvalidReceipt 13 21 24 := by decide +kernel

theorem receipt_6783_r13_band_01_24 : RowBandReceipt 13 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 13 1 13 sourceC 6 r13_0
    (fun _ ↦ fastFits_of_sourceC6)
  have h1 := coarseRouteReceipt_to_rowBand 13 13 17 sourceC 5 r13_1
    (fun _ ↦ fastFits_of_sourceC5)
  have h2 := coarseRouteReceipt_to_rowBand 13 17 19 sourceC 4 r13_2
    (fun _ ↦ fastFits_of_sourceC4)
  have h3 := coarseRouteReceipt_to_rowBand 13 19 20 sourceAux 1 r13_3
    (fun _ ↦ fastFits_of_sourceAux)
  have h4 := coarseRouteReceipt_to_rowBand 13 20 21 sourceA 1 r13_4
    (fun _ ↦ fastFits_of_sourceA)
  have h5 := coarseInvalidReceipt_to_rowBand 13 21 24 r13_5
  exact rowBandReceipt_append 13 1 13 24 h0
    (rowBandReceipt_append 13 13 17 24 h1
    (rowBandReceipt_append 13 17 19 24 h2
    (rowBandReceipt_append 13 19 20 24 h3
    (rowBandReceipt_append 13 20 21 24 h4
    h5))))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
