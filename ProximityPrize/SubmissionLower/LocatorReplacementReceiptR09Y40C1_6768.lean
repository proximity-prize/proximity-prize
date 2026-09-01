import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y40C0_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y40_c1:∀ b:Fin 160,32≤b.val→b.val<64→
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨40,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
