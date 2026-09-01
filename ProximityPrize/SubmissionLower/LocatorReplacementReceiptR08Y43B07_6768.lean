import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y43B06_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y43_b07:∀ b:Fin 160,140≤b.val→b.val<160→
    Receipt ((⟨7,by decide⟩:Fin 17),(⟨43,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
