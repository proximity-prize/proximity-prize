import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y68_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y69_c0:∀ b:Fin 160,b.val<32→
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨69,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
