import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y48C2_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y48_c3:∀ b:Fin 160,96≤b.val→b.val<128→
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨48,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
