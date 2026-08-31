import ProximityPrize.SubmissionLower.LocatorReplacementReceipt14Chunk5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_14:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((14:Fin 16),yi,ti):=by
  intro yi ti
  fin_cases yi
  · exact receipt_14_y0 ti
  · exact receipt_14_y1 ti
  · exact receipt_14_y2 ti
  · exact receipt_14_y3 ti
  · exact receipt_14_y4 ti
  · exact receipt_14_y5 ti
  · exact receipt_14_y6 ti
  · exact receipt_14_y7 ti
  · exact receipt_14_y8 ti
  · exact receipt_14_y9 ti
  · exact receipt_14_y10 ti
  · exact receipt_14_y11 ti
  · exact receipt_14_y12 ti
  · exact receipt_14_y13 ti
  · exact receipt_14_y14 ti
  · exact receipt_14_y15 ti
  · exact receipt_14_y16 ti
  · exact receipt_14_y17 ti
  · exact receipt_14_y18 ti
  · exact receipt_14_y19 ti
  · exact receipt_14_y20 ti
  · exact receipt_14_y21 ti
  · exact receipt_14_y22 ti
  · exact receipt_14_y23 ti
  · exact receipt_14_y24 ti
  · exact receipt_14_y25 ti
  · exact receipt_14_y26 ti
  · exact receipt_14_y27 ti
  · exact receipt_14_y28 ti
  · exact receipt_14_y29 ti
  · exact receipt_14_y30 ti
  · exact receipt_14_y31 ti
  · exact receipt_14_y32 ti
  · exact receipt_14_y33 ti
  · exact receipt_14_y34 ti
  · exact receipt_14_y35 ti
end ProximityPrize.SubmissionLower.LocatorReplacementData
