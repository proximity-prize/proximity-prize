import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y49_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y2b:
    ∀ y:Fin 79,45≤y.val→y.val<50→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  have hcases:y.val=45∨y.val=46∨y.val=47∨y.val=48∨y.val=49:=by omega
  rcases hcases with h0|h1|h2|h3|h4
  · have hy:y=(⟨45,by decide⟩:Fin 79):=Fin.ext h0
    rw [hy];exact receipt_r09_y45 b
  · have hy:y=(⟨46,by decide⟩:Fin 79):=Fin.ext h1
    rw [hy];exact receipt_r09_y46 b
  · have hy:y=(⟨47,by decide⟩:Fin 79):=Fin.ext h2
    rw [hy];exact receipt_r09_y47 b
  · have hy:y=(⟨48,by decide⟩:Fin 79):=Fin.ext h3
    rw [hy];exact receipt_r09_y48 b
  · have hy:y=(⟨49,by decide⟩:Fin 79):=Fin.ext h4
    rw [hy];exact receipt_r09_y49 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
