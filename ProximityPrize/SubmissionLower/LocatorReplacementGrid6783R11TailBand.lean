import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y05Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r11_0 : CoarseRouteReceipt 11 1 12 sourceC 7 := by decide +kernel
private theorem r11_1 : CoarseRouteReceipt 11 12 14 sourceC 6 := by decide +kernel
private theorem r11_2 : CoarseRouteReceipt 11 14 17 sourceC 5 := by decide +kernel
private theorem r11_3 : CoarseRouteReceipt 11 17 20 sourceC 4 := by decide +kernel
private theorem r11_4 : CoarseRouteReceipt 11 20 21 sourceAux 1 := by decide +kernel
private theorem r11_5 : CoarseInvalidReceipt 11 21 24 := by decide +kernel

theorem receipt_6783_r11_band_01_24 : RowBandReceipt 11 1 24 := by
  have h0 := coarseRouteReceipt_to_rowBand 11 1 12 sourceC 7 r11_0
    (fun _ ↦ fastFits_of_sourceC7)
  have h1 := coarseRouteReceipt_to_rowBand 11 12 14 sourceC 6 r11_1
    (fun _ ↦ fastFits_of_sourceC6)
  have h2 := coarseRouteReceipt_to_rowBand 11 14 17 sourceC 5 r11_2
    (fun _ ↦ fastFits_of_sourceC5)
  have h3 := coarseRouteReceipt_to_rowBand 11 17 20 sourceC 4 r11_3
    (fun _ ↦ fastFits_of_sourceC4)
  have h4 := coarseRouteReceipt_to_rowBand 11 20 21 sourceAux 1 r11_4
    (fun _ ↦ fastFits_of_sourceAux)
  have h5 := coarseInvalidReceipt_to_rowBand 11 21 24 r11_5
  exact rowBandReceipt_append 11 1 12 24 h0
    (rowBandReceipt_append 11 12 14 24 h1
    (rowBandReceipt_append 11 14 17 24 h2
    (rowBandReceipt_append 11 17 20 24 h3
    (rowBandReceipt_append 11 20 21 24 h4
    h5))))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
