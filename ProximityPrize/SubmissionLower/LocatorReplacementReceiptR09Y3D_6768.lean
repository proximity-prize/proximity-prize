import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y78_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y3d:
    ∀ y:Fin 79,75≤y.val→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo b
  have hcases:y.val=75∨y.val=76∨y.val=77∨y.val=78:=by omega
  rcases hcases with h0|h1|h2|h3
  · have hy:y=(⟨75,by decide⟩:Fin 79):=Fin.ext h0
    rw [hy];exact receipt_r09_y75 b
  · have hy:y=(⟨76,by decide⟩:Fin 79):=Fin.ext h1
    rw [hy];exact receipt_r09_y76 b
  · have hy:y=(⟨77,by decide⟩:Fin 79):=Fin.ext h2
    rw [hy];exact receipt_r09_y77 b
  · have hy:y=(⟨78,by decide⟩:Fin 79):=Fin.ext h3
    rw [hy];exact receipt_r09_y78 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
