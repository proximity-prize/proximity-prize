import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R15Y00Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r17_0 : CoarseRouteReceipt 17 1 17 sourceC 4 := by decide +kernel
private theorem r17_1 : CoarseRouteReceipt 17 17 19 sourceAux 1 := by decide +kernel
private theorem r17_2 : CoarseRouteReceipt 17 19 20 sourceA 1 := by decide +kernel
private theorem r17_3 : CoarseInvalidReceipt 17 20 24 := by decide +kernel

theorem receipt_6783_r17_band_01_24 : RowBandReceipt 17 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 17 1 17 sourceC 4 r17_0
    (fun _ ↦ fastFits_of_sourceC4)
  have h1 := coarseRouteReceipt_to_rowBand 17 17 19 sourceAux 1 r17_1
    (fun _ ↦ fastFits_of_sourceAux)
  have h2 := coarseRouteReceipt_to_rowBand 17 19 20 sourceA 1 r17_2
    (fun _ ↦ fastFits_of_sourceA)
  have h3 := coarseInvalidReceipt_to_rowBand 17 20 24 r17_3
  exact rowBandReceipt_append 17 1 17 24 h0
    (rowBandReceipt_append 17 17 19 24 h1
    (rowBandReceipt_append 17 19 20 24 h2
    h3))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
