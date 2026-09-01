import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR10G3_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r10_g4a:∀ y:Fin 79,32≤y.val→y.val<34→∀ b:Fin 160,
    Receipt ((⟨9,by decide⟩:Fin 17),y,b):=by decide
theorem receipt_r10_g4b:∀ y:Fin 79,34≤y.val→y.val<36→∀ b:Fin 160,
    Receipt ((⟨9,by decide⟩:Fin 17),y,b):=by decide
theorem receipt_r10_g4c:∀ y:Fin 79,36≤y.val→y.val<38→∀ b:Fin 160,
    Receipt ((⟨9,by decide⟩:Fin 17),y,b):=by decide
theorem receipt_r10_g4d:∀ y:Fin 79,38≤y.val→y.val<40→∀ b:Fin 160,
    Receipt ((⟨9,by decide⟩:Fin 17),y,b):=by decide
theorem receipt_r10_g4:∀ y:Fin 79,32≤y.val→y.val<40→∀ b:Fin 160,
    Receipt ((⟨9,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  by_cases h34:y.val<34
  · exact receipt_r10_g4a y hlo h34 b
  by_cases h36:y.val<36
  · exact receipt_r10_g4b y (by omega) h36 b
  by_cases h38:y.val<38
  · exact receipt_r10_g4c y (by omega) h38 b
  · exact receipt_r10_g4d y (by omega) hhi b
end ProximityPrize.SubmissionLower.LocatorReplacementData
