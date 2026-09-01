import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y44_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y2a:
    ∀ y:Fin 79,40≤y.val→y.val<45→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  have hcases:y.val=40∨y.val=41∨y.val=42∨y.val=43∨y.val=44:=by omega
  rcases hcases with h0|h1|h2|h3|h4
  · have hy:y=(⟨40,by decide⟩:Fin 79):=Fin.ext h0
    rw [hy];exact receipt_r09_y40 b
  · have hy:y=(⟨41,by decide⟩:Fin 79):=Fin.ext h1
    rw [hy];exact receipt_r09_y41 b
  · have hy:y=(⟨42,by decide⟩:Fin 79):=Fin.ext h2
    rw [hy];exact receipt_r09_y42 b
  · have hy:y=(⟨43,by decide⟩:Fin 79):=Fin.ext h3
    rw [hy];exact receipt_r09_y43 b
  · have hy:y=(⟨44,by decide⟩:Fin 79):=Fin.ext h4
    rw [hy];exact receipt_r09_y44 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
