import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y76C1_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y76_c2:∀ b:Fin 160,64≤b.val→b.val<96→
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨76,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
