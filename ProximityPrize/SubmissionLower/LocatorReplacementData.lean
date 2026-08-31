import ProximityPrize.SubmissionLower.LocatorReplacementReceipt15
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt (c:Cell):Receipt c:=by
  rcases c with ⟨ri,yi,ti⟩
  fin_cases ri
  · exact receipt_0 yi ti
  · exact receipt_1 yi ti
  · exact receipt_2 yi ti
  · exact receipt_3 yi ti
  · exact receipt_4 yi ti
  · exact receipt_5 yi ti
  · exact receipt_6 yi ti
  · exact receipt_7 yi ti
  · exact receipt_8 yi ti
  · exact receipt_9 yi ti
  · exact receipt_10 yi ti
  · exact receipt_11 yi ti
  · exact receipt_12 yi ti
  · exact receipt_13 yi ti
  · exact receipt_14 yi ti
  · exact receipt_15 yi ti
def chosenCost (c:Cell):ℕ :=
  if OrdinaryFits c then ordinaryCost c
  else if Pair95Fits c then pair95Cost c else pair72Cost c
theorem chosenCost_with_rest (c:Cell) (hv:Valid c) (hnr:¬ RateFits c) :
    chosenCost c+gridRestCost c≤bound:=by
  have hroutes:=(receipt c hv).resolve_left hnr
  by_cases ho:OrdinaryFits c
  · have ho' : ordinaryCost c + gridRestCost c ≤ bound := by
      simpa only [OrdinaryFits] using ho
    rw [chosenCost, if_pos ho]
    exact ho'
  · have hpairs:=hroutes.resolve_left ho
    by_cases h95:Pair95Fits c
    · simpa only [chosenCost,if_neg ho,if_pos h95] using h95.2.2.2
    · have h72:=hpairs.resolve_left h95
      simpa only [chosenCost,if_neg ho,if_neg h95] using h72.2.2.2
end ProximityPrize.SubmissionLower.LocatorReplacementData
