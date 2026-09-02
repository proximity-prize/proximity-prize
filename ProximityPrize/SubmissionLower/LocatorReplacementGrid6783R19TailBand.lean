import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R17Y00Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r19_0 : CoarseRouteReceipt 19 1 14 sourceC 4 := by decide +kernel
private theorem r19_1 : CoarseRouteReceipt 19 14 19 sourceAux 1 := by decide +kernel
private theorem r19_2 : CoarseInvalidReceipt 19 19 24 := by decide +kernel

theorem receipt_6783_r19_band_01_24 : RowBandReceipt 19 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 19 1 14 sourceC 4 r19_0
    (fun _ ↦ fastFits_of_sourceC4)
  have h1 := coarseRouteReceipt_to_rowBand 19 14 19 sourceAux 1 r19_1
    (fun _ ↦ fastFits_of_sourceAux)
  have h2 := coarseInvalidReceipt_to_rowBand 19 19 24 r19_2
  exact rowBandReceipt_append 19 1 14 24 h0
    (rowBandReceipt_append 19 14 19 24 h1
    h2)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
