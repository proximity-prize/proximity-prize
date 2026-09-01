import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y44B03_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y44_b04:∀ b:Fin 160,80≤b.val→b.val<100→
    Receipt ((⟨7,by decide⟩:Fin 17),(⟨44,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
