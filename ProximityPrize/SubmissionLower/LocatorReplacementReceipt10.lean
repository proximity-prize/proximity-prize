import ProximityPrize.SubmissionLower.LocatorReplacementReceipt10Chunk5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_10:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((10:Fin 16),yi,ti):=by
  intro yi ti
  fin_cases yi
  · exact receipt_10_y0 ti
  · exact receipt_10_y1 ti
  · exact receipt_10_y2 ti
  · exact receipt_10_y3 ti
  · exact receipt_10_y4 ti
  · exact receipt_10_y5 ti
  · exact receipt_10_y6 ti
  · exact receipt_10_y7 ti
  · exact receipt_10_y8 ti
  · exact receipt_10_y9 ti
  · exact receipt_10_y10 ti
  · exact receipt_10_y11 ti
  · exact receipt_10_y12 ti
  · exact receipt_10_y13 ti
  · exact receipt_10_y14 ti
  · exact receipt_10_y15 ti
  · exact receipt_10_y16 ti
  · exact receipt_10_y17 ti
  · exact receipt_10_y18 ti
  · exact receipt_10_y19 ti
  · exact receipt_10_y20 ti
  · exact receipt_10_y21 ti
  · exact receipt_10_y22 ti
  · exact receipt_10_y23 ti
  · exact receipt_10_y24 ti
  · exact receipt_10_y25 ti
  · exact receipt_10_y26 ti
  · exact receipt_10_y27 ti
  · exact receipt_10_y28 ti
  · exact receipt_10_y29 ti
  · exact receipt_10_y30 ti
  · exact receipt_10_y31 ti
  · exact receipt_10_y32 ti
  · exact receipt_10_y33 ti
  · exact receipt_10_y34 ti
  · exact receipt_10_y35 ti
end ProximityPrize.SubmissionLower.LocatorReplacementData
