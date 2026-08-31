import ProximityPrize.SubmissionLower.LocatorReplacementReceipt13Chunk5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_13:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((13:Fin 16),yi,ti):=by
  intro yi ti
  fin_cases yi
  · exact receipt_13_y0 ti
  · exact receipt_13_y1 ti
  · exact receipt_13_y2 ti
  · exact receipt_13_y3 ti
  · exact receipt_13_y4 ti
  · exact receipt_13_y5 ti
  · exact receipt_13_y6 ti
  · exact receipt_13_y7 ti
  · exact receipt_13_y8 ti
  · exact receipt_13_y9 ti
  · exact receipt_13_y10 ti
  · exact receipt_13_y11 ti
  · exact receipt_13_y12 ti
  · exact receipt_13_y13 ti
  · exact receipt_13_y14 ti
  · exact receipt_13_y15 ti
  · exact receipt_13_y16 ti
  · exact receipt_13_y17 ti
  · exact receipt_13_y18 ti
  · exact receipt_13_y19 ti
  · exact receipt_13_y20 ti
  · exact receipt_13_y21 ti
  · exact receipt_13_y22 ti
  · exact receipt_13_y23 ti
  · exact receipt_13_y24 ti
  · exact receipt_13_y25 ti
  · exact receipt_13_y26 ti
  · exact receipt_13_y27 ti
  · exact receipt_13_y28 ti
  · exact receipt_13_y29 ti
  · exact receipt_13_y30 ti
  · exact receipt_13_y31 ti
  · exact receipt_13_y32 ti
  · exact receipt_13_y33 ti
  · exact receipt_13_y34 ti
  · exact receipt_13_y35 ti
end ProximityPrize.SubmissionLower.LocatorReplacementData
