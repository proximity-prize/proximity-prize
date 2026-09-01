import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y55_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y56_c0:∀ b:Fin 160,b.val<32→
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨56,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
