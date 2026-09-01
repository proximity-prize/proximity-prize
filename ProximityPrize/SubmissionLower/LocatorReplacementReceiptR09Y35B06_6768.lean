import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y35B05_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y35_b06:∀ b:Fin 160,120≤b.val→b.val<140→
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨35,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
