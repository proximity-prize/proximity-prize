import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y40_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y41_b00:∀ b:Fin 160,b.val<20→
    Receipt ((⟨7,by decide⟩:Fin 17),(⟨41,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
