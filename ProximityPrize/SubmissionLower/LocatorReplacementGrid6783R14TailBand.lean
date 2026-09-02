import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R12Y00Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r14_0 : CoarseRouteReceipt 14 1 16 sourceC 5 := by decide +kernel
private theorem r14_1 : CoarseRouteReceipt 14 16 19 sourceC 4 := by decide +kernel
private theorem r14_2 : CoarseRouteReceipt 14 19 20 sourceAux 1 := by decide +kernel
private theorem r14_3 : CoarseRouteReceipt 14 20 21 sourceA 1 := by decide +kernel
private theorem r14_4 : CoarseInvalidReceipt 14 21 24 := by decide +kernel

theorem receipt_6783_r14_band_01_24 : RowBandReceipt 14 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 14 1 16 sourceC 5 r14_0
    (fun _ ↦ fastFits_of_sourceC5)
  have h1 := coarseRouteReceipt_to_rowBand 14 16 19 sourceC 4 r14_1
    (fun _ ↦ fastFits_of_sourceC4)
  have h2 := coarseRouteReceipt_to_rowBand 14 19 20 sourceAux 1 r14_2
    (fun _ ↦ fastFits_of_sourceAux)
  have h3 := coarseRouteReceipt_to_rowBand 14 20 21 sourceA 1 r14_3
    (fun _ ↦ fastFits_of_sourceA)
  have h4 := coarseInvalidReceipt_to_rowBand 14 21 24 r14_4
  exact rowBandReceipt_append 14 1 16 24 h0
    (rowBandReceipt_append 14 16 19 24 h1
    (rowBandReceipt_append 14 19 20 24 h2
    (rowBandReceipt_append 14 20 21 24 h3
    h4)))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
