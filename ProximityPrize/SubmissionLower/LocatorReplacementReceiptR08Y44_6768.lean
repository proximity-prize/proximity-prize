import ProximityPrize.SubmissionLower.LocatorReplacementData
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y43_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y44:∀ b:Fin 160,
    Receipt ((⟨7,by decide⟩:Fin 17),(⟨44,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
