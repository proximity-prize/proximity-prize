import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y69_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y3b:
    ∀ y:Fin 79,65≤y.val→y.val<70→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  have hcases:y.val=65∨y.val=66∨y.val=67∨y.val=68∨y.val=69:=by omega
  rcases hcases with h0|h1|h2|h3|h4
  · have hy:y=(⟨65,by decide⟩:Fin 79):=Fin.ext h0
    rw [hy];exact receipt_r09_y65 b
  · have hy:y=(⟨66,by decide⟩:Fin 79):=Fin.ext h1
    rw [hy];exact receipt_r09_y66 b
  · have hy:y=(⟨67,by decide⟩:Fin 79):=Fin.ext h2
    rw [hy];exact receipt_r09_y67 b
  · have hy:y=(⟨68,by decide⟩:Fin 79):=Fin.ext h3
    rw [hy];exact receipt_r09_y68 b
  · have hy:y=(⟨69,by decide⟩:Fin 79):=Fin.ext h4
    rw [hy];exact receipt_r09_y69 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
