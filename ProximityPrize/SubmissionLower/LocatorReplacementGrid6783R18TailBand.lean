import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R16Y00Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r18_0 : CoarseRouteReceipt 18 1 16 sourceC 4 := by decide +kernel
private theorem r18_1 : CoarseRouteReceipt 18 16 19 sourceAux 1 := by decide +kernel
private theorem r18_2 : CoarseRouteReceipt 18 19 20 sourceA 1 := by decide +kernel
private theorem r18_3 : CoarseInvalidReceipt 18 20 24 := by decide +kernel

theorem receipt_6783_r18_band_01_24 : RowBandReceipt 18 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 18 1 16 sourceC 4 r18_0
    (fun _ ↦ fastFits_of_sourceC4)
  have h1 := coarseRouteReceipt_to_rowBand 18 16 19 sourceAux 1 r18_1
    (fun _ ↦ fastFits_of_sourceAux)
  have h2 := coarseRouteReceipt_to_rowBand 18 19 20 sourceA 1 r18_2
    (fun _ ↦ fastFits_of_sourceA)
  have h3 := coarseInvalidReceipt_to_rowBand 18 20 24 r18_3
  exact rowBandReceipt_append 18 1 16 24 h0
    (rowBandReceipt_append 18 16 19 24 h1
    (rowBandReceipt_append 18 19 20 24 h2
    h3))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
