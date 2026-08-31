import ProximityPrize.SubmissionLower.LocatorReplacementReceipt12Chunk5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_12:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((12:Fin 16),yi,ti):=by
  intro yi ti
  fin_cases yi
  · exact receipt_12_y0 ti
  · exact receipt_12_y1 ti
  · exact receipt_12_y2 ti
  · exact receipt_12_y3 ti
  · exact receipt_12_y4 ti
  · exact receipt_12_y5 ti
  · exact receipt_12_y6 ti
  · exact receipt_12_y7 ti
  · exact receipt_12_y8 ti
  · exact receipt_12_y9 ti
  · exact receipt_12_y10 ti
  · exact receipt_12_y11 ti
  · exact receipt_12_y12 ti
  · exact receipt_12_y13 ti
  · exact receipt_12_y14 ti
  · exact receipt_12_y15 ti
  · exact receipt_12_y16 ti
  · exact receipt_12_y17 ti
  · exact receipt_12_y18 ti
  · exact receipt_12_y19 ti
  · exact receipt_12_y20 ti
  · exact receipt_12_y21 ti
  · exact receipt_12_y22 ti
  · exact receipt_12_y23 ti
  · exact receipt_12_y24 ti
  · exact receipt_12_y25 ti
  · exact receipt_12_y26 ti
  · exact receipt_12_y27 ti
  · exact receipt_12_y28 ti
  · exact receipt_12_y29 ti
  · exact receipt_12_y30 ti
  · exact receipt_12_y31 ti
  · exact receipt_12_y32 ti
  · exact receipt_12_y33 ti
  · exact receipt_12_y34 ti
  · exact receipt_12_y35 ti
end ProximityPrize.SubmissionLower.LocatorReplacementData
