import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y41B00_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y41_b01:∀ b:Fin 160,20≤b.val→b.val<40→
    Receipt ((⟨7,by decide⟩:Fin 17),(⟨41,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
