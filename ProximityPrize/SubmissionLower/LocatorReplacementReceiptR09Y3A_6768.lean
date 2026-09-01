import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y64_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y3a:
    ∀ y:Fin 79,60≤y.val→y.val<65→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  have hcases:y.val=60∨y.val=61∨y.val=62∨y.val=63∨y.val=64:=by omega
  rcases hcases with h0|h1|h2|h3|h4
  · have hy:y=(⟨60,by decide⟩:Fin 79):=Fin.ext h0
    rw [hy];exact receipt_r09_y60 b
  · have hy:y=(⟨61,by decide⟩:Fin 79):=Fin.ext h1
    rw [hy];exact receipt_r09_y61 b
  · have hy:y=(⟨62,by decide⟩:Fin 79):=Fin.ext h2
    rw [hy];exact receipt_r09_y62 b
  · have hy:y=(⟨63,by decide⟩:Fin 79):=Fin.ext h3
    rw [hy];exact receipt_r09_y63 b
  · have hy:y=(⟨64,by decide⟩:Fin 79):=Fin.ext h4
    rw [hy];exact receipt_r09_y64 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
