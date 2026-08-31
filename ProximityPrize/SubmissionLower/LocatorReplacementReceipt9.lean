import ProximityPrize.SubmissionLower.LocatorReplacementReceipt9Chunk5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_9:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((9:Fin 16),yi,ti):=by
  intro yi ti
  fin_cases yi
  · exact receipt_9_y0 ti
  · exact receipt_9_y1 ti
  · exact receipt_9_y2 ti
  · exact receipt_9_y3 ti
  · exact receipt_9_y4 ti
  · exact receipt_9_y5 ti
  · exact receipt_9_y6 ti
  · exact receipt_9_y7 ti
  · exact receipt_9_y8 ti
  · exact receipt_9_y9 ti
  · exact receipt_9_y10 ti
  · exact receipt_9_y11 ti
  · exact receipt_9_y12 ti
  · exact receipt_9_y13 ti
  · exact receipt_9_y14 ti
  · exact receipt_9_y15 ti
  · exact receipt_9_y16 ti
  · exact receipt_9_y17 ti
  · exact receipt_9_y18 ti
  · exact receipt_9_y19 ti
  · exact receipt_9_y20 ti
  · exact receipt_9_y21 ti
  · exact receipt_9_y22 ti
  · exact receipt_9_y23 ti
  · exact receipt_9_y24 ti
  · exact receipt_9_y25 ti
  · exact receipt_9_y26 ti
  · exact receipt_9_y27 ti
  · exact receipt_9_y28 ti
  · exact receipt_9_y29 ti
  · exact receipt_9_y30 ti
  · exact receipt_9_y31 ti
  · exact receipt_9_y32 ti
  · exact receipt_9_y33 ti
  · exact receipt_9_y34 ti
  · exact receipt_9_y35 ti
end ProximityPrize.SubmissionLower.LocatorReplacementData
