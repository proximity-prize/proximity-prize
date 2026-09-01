import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y74_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y3c:
    ∀ y:Fin 79,70≤y.val→y.val<75→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  have hcases:y.val=70∨y.val=71∨y.val=72∨y.val=73∨y.val=74:=by omega
  rcases hcases with h0|h1|h2|h3|h4
  · have hy:y=(⟨70,by decide⟩:Fin 79):=Fin.ext h0
    rw [hy];exact receipt_r09_y70 b
  · have hy:y=(⟨71,by decide⟩:Fin 79):=Fin.ext h1
    rw [hy];exact receipt_r09_y71 b
  · have hy:y=(⟨72,by decide⟩:Fin 79):=Fin.ext h2
    rw [hy];exact receipt_r09_y72 b
  · have hy:y=(⟨73,by decide⟩:Fin 79):=Fin.ext h3
    rw [hy];exact receipt_r09_y73 b
  · have hy:y=(⟨74,by decide⟩:Fin 79):=Fin.ext h4
    rw [hy];exact receipt_r09_y74 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
