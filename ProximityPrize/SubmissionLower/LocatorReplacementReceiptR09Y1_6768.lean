import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y1A_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y1B_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y1C_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y1D_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y1:
    ∀ y:Fin 79,20≤y.val→y.val<40→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  by_cases h0:y.val<25
  · exact receipt_r09_y1a y hlo h0 b
  by_cases h1:y.val<30
  · exact receipt_r09_y1b y (by omega) h1 b
  by_cases h2:y.val<35
  · exact receipt_r09_y1c y (by omega) h2 b
  exact receipt_r09_y1d y (by omega) hhi b
end ProximityPrize.SubmissionLower.LocatorReplacementData
