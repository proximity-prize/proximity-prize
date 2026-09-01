import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y51C3_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y51_c4:∀ b:Fin 160,128≤b.val→b.val<160→
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨51,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
