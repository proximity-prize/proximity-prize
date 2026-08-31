import ProximityPrize.SubmissionLower.LocatorReplacementReceipt67

namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

theorem receipt (c : Cell) : Receipt c := by
  rcases c with ⟨ri, yi, ti⟩
  fin_cases ri
  · exact receipt_0 yi ti
  · exact receipt_1 yi ti
  · exact receipt_2 yi ti
  · exact receipt_3 yi ti
  · exact receipt_4 yi ti
  · exact receipt_5 yi ti
  · exact receipt_6 yi ti
  · exact receipt_7 yi ti

def chosenCost (c : Cell) : ℕ :=
  if OrdinaryFits c then ordinaryCost c else quotientCost c

theorem chosenCost_with_rest (c : Cell) (hv : Valid c) :
    chosenCost c + gridRestCost c ≤ 271500000000000000 := by
  by_cases h : OrdinaryFits c
  · rw [chosenCost, if_pos h]
    exact h
  · simpa only [chosenCost, if_neg h] using ((receipt c hv).resolve_left h).2

theorem band_lt (c : Cell) (hv : Valid c) (ho : ¬ OrdinaryFits c) :
    bandCost c < 38456280382 := ((receipt c hv).resolve_left ho).1

theorem quotient_caps (c : Cell) (hv : Valid c) :
    131072 ≤ quotientD c ∧ quotientD c ≤ 14002065 ∧
    1 ≤ quotientS c ∧ quotientS c ≤ quotientYS c ∧
    quotientYS c ≤ quotientT c ∧ 2 ≤ quotientYS c ∧
    quotientS c ≤ 16 ∧ quotientYS c ≤ 106 ∧ quotientT c ≤ 10000 := by
  have hr := c.1.isLt
  have ht := c.2.2.isLt
  have hy := hv.1
  dsimp [r, ylo] at hy
  simp only [quotientD, quotientT, quotientYS, quotientS, r, ylo, tlo]
  omega

end ProximityPrize.SubmissionLower.LocatorReplacementData
