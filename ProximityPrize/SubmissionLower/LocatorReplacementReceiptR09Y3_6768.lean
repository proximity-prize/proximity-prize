import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y3D_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y3:
    ∀ y:Fin 79,60≤y.val→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo b
  by_cases h65:y.val<65
  · exact receipt_r09_y3a y hlo h65 b
  by_cases h70:y.val<70
  · exact receipt_r09_y3b y (by omega) h70 b
  by_cases h75:y.val<75
  · exact receipt_r09_y3c y (by omega) h75 b
  · exact receipt_r09_y3d y (by omega) b
end ProximityPrize.SubmissionLower.LocatorReplacementData
