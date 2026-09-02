import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y08Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r09_0 : CoarseRouteReceipt 9 6 10 sourceC 8 := by decide +kernel
private theorem r09_1 : CoarseRouteReceipt 9 10 12 sourceC 7 := by decide +kernel
private theorem r09_2 : CoarseRouteReceipt 9 12 14 sourceC 6 := by decide +kernel
private theorem r09_3 : CoarseRouteReceipt 9 14 18 sourceC 5 := by decide +kernel
private theorem r09_4 : CoarseRouteReceipt 9 18 21 sourceC 4 := by decide +kernel
private theorem r09_5 : CoarseRouteReceipt 9 21 22 sourceA 1 := by decide +kernel
private theorem r09_6 : CoarseInvalidReceipt 9 22 24 := by decide +kernel

theorem receipt_6783_r09_band_06_24 : RowBandReceipt 9 6 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 9 6 10 sourceC 8 r09_0
    (fun _ ↦ fastFits_of_sourceC8)
  have h1 := coarseRouteReceipt_to_rowBand 9 10 12 sourceC 7 r09_1
    (fun _ ↦ fastFits_of_sourceC7)
  have h2 := coarseRouteReceipt_to_rowBand 9 12 14 sourceC 6 r09_2
    (fun _ ↦ fastFits_of_sourceC6)
  have h3 := coarseRouteReceipt_to_rowBand 9 14 18 sourceC 5 r09_3
    (fun _ ↦ fastFits_of_sourceC5)
  have h4 := coarseRouteReceipt_to_rowBand 9 18 21 sourceC 4 r09_4
    (fun _ ↦ fastFits_of_sourceC4)
  have h5 := coarseRouteReceipt_to_rowBand 9 21 22 sourceA 1 r09_5
    (fun _ ↦ fastFits_of_sourceA)
  have h6 := coarseInvalidReceipt_to_rowBand 9 22 24 r09_6
  exact rowBandReceipt_append 9 6 10 24 h0
    (rowBandReceipt_append 9 10 12 24 h1
    (rowBandReceipt_append 9 12 14 24 h2
    (rowBandReceipt_append 9 14 18 24 h3
    (rowBandReceipt_append 9 18 21 24 h4
    (rowBandReceipt_append 9 21 22 24 h5
    h6)))))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
