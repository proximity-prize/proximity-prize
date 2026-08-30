import ProximityPrize.SubmissionLower.ContactLegacyAdaptiveBasic6750Research

namespace ProximityPrize.SubmissionLower.ContactLegacyAdaptiveBoundary6750Research

open ContactLegacyPureBandReceipt6750Research
open ContactLegacyAdaptiveBasic6750Research

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000

 



def boundaryNonPureCost (y r : Nat) : Nat :=
  upstreamRMax (y + 1) y r +
    coordinateCost 8417478 y y r + thirdCost y y r

theorem boundaryNonPureCost_le_budget
    (y r : Nat) (hy : y ≤ 64) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) :
    boundaryNonPureCost y r ≤
      ContactMovingSeedless6750Research.mcaBudget := by
  have hcheck : ∀ (yy : Fin 65) (rr : Fin 15),
      2 ≤ rr.1 → rr.1 < yy.1 →
      boundaryNonPureCost yy.1 rr.1 ≤
        ContactMovingSeedless6750Research.mcaBudget := by
    decide
  simpa using hcheck ⟨y, by omega⟩ ⟨r, by omega⟩ hr2 hry

end ProximityPrize.SubmissionLower.ContactLegacyAdaptiveBoundary6750Research

#print axioms ProximityPrize.SubmissionLower.ContactLegacyAdaptiveBoundary6750Research.boundaryNonPureCost_le_budget
