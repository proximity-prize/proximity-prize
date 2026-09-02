import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R13Y00Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r15_0 : CoarseRouteReceipt 15 1 16 sourceC 5 := by decide +kernel
private theorem r15_1 : CoarseRouteReceipt 15 16 19 sourceC 4 := by decide +kernel
private theorem r15_2 : CoarseRouteReceipt 15 19 20 sourceAux 1 := by decide +kernel
private theorem r15_3 : CoarseInvalidReceipt 15 20 24 := by decide +kernel

theorem receipt_6783_r15_band_01_24 : RowBandReceipt 15 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 15 1 16 sourceC 5 r15_0
    (fun _ ↦ fastFits_of_sourceC5)
  have h1 := coarseRouteReceipt_to_rowBand 15 16 19 sourceC 4 r15_1
    (fun _ ↦ fastFits_of_sourceC4)
  have h2 := coarseRouteReceipt_to_rowBand 15 19 20 sourceAux 1 r15_2
    (fun _ ↦ fastFits_of_sourceAux)
  have h3 := coarseInvalidReceipt_to_rowBand 15 20 24 r15_3
  exact rowBandReceipt_append 15 1 16 24 h0
    (rowBandReceipt_append 15 16 19 24 h1
    (rowBandReceipt_append 15 19 20 24 h2
    h3))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
