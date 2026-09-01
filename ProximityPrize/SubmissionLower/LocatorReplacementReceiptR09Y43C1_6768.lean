import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y43C0_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y43_c1:∀ b:Fin 160,32≤b.val→b.val<64→
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨43,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
