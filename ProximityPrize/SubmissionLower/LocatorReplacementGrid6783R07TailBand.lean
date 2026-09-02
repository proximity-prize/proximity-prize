import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R06Y09Tail

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem r07_c8 : CoarseRouteReceipt 7 9 11 sourceC 8 := by decide +kernel
private theorem r07_c7 : CoarseRouteReceipt 7 11 13 sourceC 7 := by decide +kernel
private theorem r07_c6 : CoarseRouteReceipt 7 13 15 sourceC 6 := by decide +kernel
private theorem r07_c5 : CoarseRouteReceipt 7 15 18 sourceC 5 := by decide +kernel
private theorem r07_c4 : CoarseRouteReceipt 7 18 21 sourceC 4 := by decide +kernel
private theorem r07_aux : CoarseRouteReceipt 7 21 22 sourceAux 1 := by decide +kernel
private theorem r07_invalid : CoarseInvalidReceipt 7 22 24 := by decide +kernel

theorem receipt_6783_r07_band_09_24 : RowBandReceipt 7 9 24 := by
  have h8 := coarseRouteReceipt_to_rowBand 7 9 11 sourceC 8 r07_c8
    (fun _ ↦ fastFits_of_sourceC8)
  have h7 := coarseRouteReceipt_to_rowBand 7 11 13 sourceC 7 r07_c7
    (fun _ ↦ fastFits_of_sourceC7)
  have h6 := coarseRouteReceipt_to_rowBand 7 13 15 sourceC 6 r07_c6
    (fun _ ↦ fastFits_of_sourceC6)
  have h5 := coarseRouteReceipt_to_rowBand 7 15 18 sourceC 5 r07_c5
    (fun _ ↦ fastFits_of_sourceC5)
  have h4 := coarseRouteReceipt_to_rowBand 7 18 21 sourceC 4 r07_c4
    (fun _ ↦ fastFits_of_sourceC4)
  have ha := coarseRouteReceipt_to_rowBand 7 21 22 sourceAux 1 r07_aux
    (fun _ ↦ fastFits_of_sourceAux)
  have hx := coarseInvalidReceipt_to_rowBand 7 22 24 r07_invalid
  exact rowBandReceipt_append 7 9 11 24 h8
    (rowBandReceipt_append 7 11 13 24 h7
      (rowBandReceipt_append 7 13 15 24 h6
        (rowBandReceipt_append 7 15 18 24 h5
          (rowBandReceipt_append 7 18 21 24 h4
            (rowBandReceipt_append 7 21 22 24 ha hx)))))

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
