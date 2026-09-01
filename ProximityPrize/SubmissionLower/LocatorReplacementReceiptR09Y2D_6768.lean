import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y59_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y2d:
    ∀ y:Fin 79,55≤y.val→y.val<60→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  have hcases:y.val=55∨y.val=56∨y.val=57∨y.val=58∨y.val=59:=by omega
  rcases hcases with h0|h1|h2|h3|h4
  · have hy:y=(⟨55,by decide⟩:Fin 79):=Fin.ext h0
    rw [hy];exact receipt_r09_y55 b
  · have hy:y=(⟨56,by decide⟩:Fin 79):=Fin.ext h1
    rw [hy];exact receipt_r09_y56 b
  · have hy:y=(⟨57,by decide⟩:Fin 79):=Fin.ext h2
    rw [hy];exact receipt_r09_y57 b
  · have hy:y=(⟨58,by decide⟩:Fin 79):=Fin.ext h3
    rw [hy];exact receipt_r09_y58 b
  · have hy:y=(⟨59,by decide⟩:Fin 79):=Fin.ext h4
    rw [hy];exact receipt_r09_y59 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
