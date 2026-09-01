import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR01Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR02Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR03Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR04Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR05Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR06Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR07Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR10Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR11Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR12Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR13Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR14Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR15Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Full6765
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR17Full6765
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem receipt (c:Cell):Receipt c:=by
  rcases c with ⟨ri,y,b⟩
  fin_cases ri
  · exact receipt_r01_full y b
  · exact receipt_r02_full y b
  · exact receipt_r03_full y b
  · exact receipt_r04_full y b
  · exact receipt_r05_full y b
  · exact receipt_r06_full y b
  · exact receipt_r07_full y b
  · exact receipt_r08_full y b
  · exact receipt_r09_full y b
  · exact receipt_r10_full y b
  · exact receipt_r11_full y b
  · exact receipt_r12_full y b
  · exact receipt_r13_full y b
  · exact receipt_r14_full y b
  · exact receipt_r15_full y b
  · exact receipt_r16_full y b
  · exact receipt_r17_full y b

theorem chosenCost_with_rest (c:Cell) (hv:Valid c) (hnr:¬noBadFits c):
    chosenCost c+exactRest c≤271696008548359000:=by
  have routes:ordinaryFits c∨sourceFits c∨sourceFits126 c:=
    (receipt c hv).resolve_left hnr
  by_cases ho:ordinaryFits c
  · rw [chosenCost,if_pos ho]
    exact ho
  · have hsources:=routes.resolve_left ho
    by_cases h93:sourceFits c
    · rw [chosenCost,if_neg ho,if_pos h93]
      exact h93.2.2.2.2.2.2.2.2
    · rw [chosenCost,if_neg ho,if_neg h93]
      exact (hsources.resolve_left h93).2.2.2.2.2.2.2.2

end ProximityPrize.SubmissionLower.LocatorReplacementData
#print axioms ProximityPrize.SubmissionLower.LocatorReplacementData.receipt
