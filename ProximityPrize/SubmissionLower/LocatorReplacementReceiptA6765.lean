import ProximityPrize.SubmissionLower.Core
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem receipt_r01_full:
    ∀ y:Fin 79,∀ b:Fin 151,
      Receipt ((⟨0,by decide⟩:Fin 17),y,b):=by decide

theorem receipt_r02_full:
    ∀ y:Fin 79,∀ b:Fin 151,
      Receipt ((⟨1,by decide⟩:Fin 17),y,b):=by decide

theorem receipt_r03_full:
    ∀ y:Fin 79,∀ b:Fin 151,
      Receipt ((⟨2,by decide⟩:Fin 17),y,b):=by decide

theorem receipt_r04_full:
    ∀ y:Fin 79,∀ b:Fin 151,
      Receipt ((⟨3,by decide⟩:Fin 17),y,b):=by decide

theorem receipt_r05_full:
    ∀ y:Fin 79,∀ b:Fin 151,
      Receipt ((⟨4,by decide⟩:Fin 17),y,b):=by decide

theorem receipt_r06_full:
    ∀ y:Fin 79,∀ b:Fin 151,
      Receipt ((⟨5,by decide⟩:Fin 17),y,b):=by decide

theorem receipt_r07_full:
    ∀ y:Fin 79,∀ b:Fin 151,
      Receipt ((⟨6,by decide⟩:Fin 17),y,b):=by decide

theorem receipt_r08_full:
    ∀ y:Fin 79,∀ b:Fin 151,
      Receipt ((⟨7,by decide⟩:Fin 17),y,b):=by decide

theorem receipt_r09_full:
    ∀ y:Fin 79,∀ b:Fin 151,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by decide

end ProximityPrize.SubmissionLower.LocatorReplacementData
