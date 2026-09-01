import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y54_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y2c:
    ∀ y:Fin 79,50≤y.val→y.val<55→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  have hcases:y.val=50∨y.val=51∨y.val=52∨y.val=53∨y.val=54:=by omega
  rcases hcases with h0|h1|h2|h3|h4
  · have hy:y=(⟨50,by decide⟩:Fin 79):=Fin.ext h0
    rw [hy];exact receipt_r09_y50 b
  · have hy:y=(⟨51,by decide⟩:Fin 79):=Fin.ext h1
    rw [hy];exact receipt_r09_y51 b
  · have hy:y=(⟨52,by decide⟩:Fin 79):=Fin.ext h2
    rw [hy];exact receipt_r09_y52 b
  · have hy:y=(⟨53,by decide⟩:Fin 79):=Fin.ext h3
    rw [hy];exact receipt_r09_y53 b
  · have hy:y=(⟨54,by decide⟩:Fin 79):=Fin.ext h4
    rw [hy];exact receipt_r09_y54 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
