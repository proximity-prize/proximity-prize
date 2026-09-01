import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y35_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y36_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y37_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y38_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y39_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y1d:
    ∀ y:Fin 79,35≤y.val→y.val<40→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  have hcases:y.val=35∨y.val=36∨y.val=37∨y.val=38∨y.val=39:=by omega
  rcases hcases with h|h|h|h|h
  · have hy:y=(⟨35,by decide⟩:Fin 79):=Fin.ext h
    rw [hy];exact receipt_r09_y35 b
  · have hy:y=(⟨36,by decide⟩:Fin 79):=Fin.ext h
    rw [hy];exact receipt_r09_y36 b
  · have hy:y=(⟨37,by decide⟩:Fin 79):=Fin.ext h
    rw [hy];exact receipt_r09_y37 b
  · have hy:y=(⟨38,by decide⟩:Fin 79):=Fin.ext h
    rw [hy];exact receipt_r09_y38 b
  · have hy:y=(⟨39,by decide⟩:Fin 79):=Fin.ext h
    rw [hy];exact receipt_r09_y39 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
