import ProximityPrize.SubmissionLower.LocatorReplacementReceiptUnit
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt (c:GridCell):Receipt c:=by
  rcases c with c|c
  · rcases c with ⟨ri,yi,ti⟩
    fin_cases ri
    · exact receipt_coarse_0 yi ti
    · exact receipt_coarse_1 yi ti
    · exact receipt_coarse_2 yi ti
    · exact receipt_coarse_3 yi ti
    · exact receipt_coarse_4 yi ti
    · exact receipt_coarse_5 yi ti
    · exact receipt_coarse_6 yi ti
    · exact receipt_coarse_7 yi ti
    · exact receipt_coarse_8 yi ti
    · exact receipt_coarse_9 yi ti
    · exact receipt_coarse_10 yi ti
    · exact receipt_coarse_11 yi ti
    · exact receipt_coarse_12 yi ti
    · exact receipt_coarse_13 yi ti
    · exact receipt_coarse_14 yi ti
    · exact receipt_coarse_15 yi ti
  · rcases c with c|c
    · exact receipt_fine c
    · exact receipt_unit c

def chosenCost (c:GridCell):ℕ:=
  if OrdinaryFits c then ordinaryCost c else if Pair72Fits c then pair72Cost c
  else if Pair126Fits c then pair126Cost c else doubleCost c

theorem chosenCost_with_rest (c:GridCell) (hv:Valid c) (hnr:¬RateFits c):
    chosenCost c+gridRestCost c≤bound:=by
  have hroutes:=(receipt c hv).resolve_left hnr
  by_cases ho:OrdinaryFits c
  · rw [chosenCost,if_pos ho]
    exact ho
  · have hpairs:=hroutes.resolve_left ho
    by_cases h72:Pair72Fits c
    · rw [chosenCost,if_neg ho,if_pos h72]
      exact h72.2.2.2.2
    · have hpairs':=hpairs.resolve_left h72
      by_cases h126:Pair126Fits c
      · rw [chosenCost,if_neg ho,if_neg h72,if_pos h126]
        exact h126.2.2.2.2
      · have hdouble:Double126Fits c:=(hpairs'.resolve_left h126)
        rw [chosenCost,if_neg ho,if_neg h72,if_neg h126]
        exact hdouble.2.2.2.2.2.2

end ProximityPrize.SubmissionLower.LocatorReplacementData
