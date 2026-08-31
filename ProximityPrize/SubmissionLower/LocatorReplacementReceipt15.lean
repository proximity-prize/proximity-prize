import ProximityPrize.SubmissionLower.LocatorReplacementReceipt15Chunk5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_15:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((15:Fin 16),yi,ti):=by
  intro yi ti
  fin_cases yi
  · exact receipt_15_y0 ti
  · exact receipt_15_y1 ti
  · exact receipt_15_y2 ti
  · exact receipt_15_y3 ti
  · exact receipt_15_y4 ti
  · exact receipt_15_y5 ti
  · exact receipt_15_y6 ti
  · exact receipt_15_y7 ti
  · exact receipt_15_y8 ti
  · exact receipt_15_y9 ti
  · exact receipt_15_y10 ti
  · exact receipt_15_y11 ti
  · exact receipt_15_y12 ti
  · exact receipt_15_y13 ti
  · exact receipt_15_y14 ti
  · exact receipt_15_y15 ti
  · exact receipt_15_y16 ti
  · exact receipt_15_y17 ti
  · exact receipt_15_y18 ti
  · exact receipt_15_y19 ti
  · exact receipt_15_y20 ti
  · exact receipt_15_y21 ti
  · exact receipt_15_y22 ti
  · exact receipt_15_y23 ti
  · exact receipt_15_y24 ti
  · exact receipt_15_y25 ti
  · exact receipt_15_y26 ti
  · exact receipt_15_y27 ti
  · exact receipt_15_y28 ti
  · exact receipt_15_y29 ti
  · exact receipt_15_y30 ti
  · exact receipt_15_y31 ti
  · exact receipt_15_y32 ti
  · exact receipt_15_y33 ti
  · exact receipt_15_y34 ti
  · exact receipt_15_y35 ti
end ProximityPrize.SubmissionLower.LocatorReplacementData
