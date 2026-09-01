import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y36B04_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y36_b05:∀ b:Fin 160,100≤b.val→b.val<120→
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨36,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
