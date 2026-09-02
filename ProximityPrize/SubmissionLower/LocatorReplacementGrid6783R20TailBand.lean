import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R18Y00Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r20_0 : CoarseRouteReceipt 20 1 7 sourceC 4 := by decide +kernel
private theorem r20_1 : CoarseRouteReceipt 20 7 18 sourceAux 1 := by decide +kernel
private theorem r20_2 : CoarseRouteReceipt 20 18 19 sourceA 1 := by decide +kernel
private theorem r20_3 : CoarseInvalidReceipt 20 19 24 := by decide +kernel

theorem receipt_6783_r20_band_01_24 : RowBandReceipt 20 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 20 1 7 sourceC 4 r20_0
    (fun _ ↦ fastFits_of_sourceC4)
  have h1 := coarseRouteReceipt_to_rowBand 20 7 18 sourceAux 1 r20_1
    (fun _ ↦ fastFits_of_sourceAux)
  have h2 := coarseRouteReceipt_to_rowBand 20 18 19 sourceA 1 r20_2
    (fun _ ↦ fastFits_of_sourceA)
  have h3 := coarseInvalidReceipt_to_rowBand 20 19 24 r20_3
  exact rowBandReceipt_append 20 1 7 24 h0
    (rowBandReceipt_append 20 7 18 24 h1
    (rowBandReceipt_append 20 18 19 24 h2
    h3))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
