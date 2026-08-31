import ProximityPrize.SubmissionLower.LocatorReplacementReceipt11Chunk5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_11:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((11:Fin 16),yi,ti):=by
  intro yi ti
  fin_cases yi
  · exact receipt_11_y0 ti
  · exact receipt_11_y1 ti
  · exact receipt_11_y2 ti
  · exact receipt_11_y3 ti
  · exact receipt_11_y4 ti
  · exact receipt_11_y5 ti
  · exact receipt_11_y6 ti
  · exact receipt_11_y7 ti
  · exact receipt_11_y8 ti
  · exact receipt_11_y9 ti
  · exact receipt_11_y10 ti
  · exact receipt_11_y11 ti
  · exact receipt_11_y12 ti
  · exact receipt_11_y13 ti
  · exact receipt_11_y14 ti
  · exact receipt_11_y15 ti
  · exact receipt_11_y16 ti
  · exact receipt_11_y17 ti
  · exact receipt_11_y18 ti
  · exact receipt_11_y19 ti
  · exact receipt_11_y20 ti
  · exact receipt_11_y21 ti
  · exact receipt_11_y22 ti
  · exact receipt_11_y23 ti
  · exact receipt_11_y24 ti
  · exact receipt_11_y25 ti
  · exact receipt_11_y26 ti
  · exact receipt_11_y27 ti
  · exact receipt_11_y28 ti
  · exact receipt_11_y29 ti
  · exact receipt_11_y30 ti
  · exact receipt_11_y31 ti
  · exact receipt_11_y32 ti
  · exact receipt_11_y33 ti
  · exact receipt_11_y34 ti
  · exact receipt_11_y35 ti
end ProximityPrize.SubmissionLower.LocatorReplacementData
