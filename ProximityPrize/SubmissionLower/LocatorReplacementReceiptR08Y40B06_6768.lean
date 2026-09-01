import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y40B05_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y40_b06:∀ b:Fin 160,120≤b.val→b.val<140→
    Receipt ((⟨7,by decide⟩:Fin 17),(⟨40,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
