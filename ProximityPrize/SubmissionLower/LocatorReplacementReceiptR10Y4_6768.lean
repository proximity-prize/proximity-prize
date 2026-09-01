import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Full6765
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r10_y4:
    ∀ y:Fin 79,4≤y.val→y.val<6→∀ b:Fin 160,
      Receipt ((⟨9,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
