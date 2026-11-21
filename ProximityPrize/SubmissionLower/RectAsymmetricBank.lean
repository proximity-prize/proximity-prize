import ProximityPrize.SubmissionLower.Rect51Bank
import ProximityPrize.SubmissionLower.RectAsymmetricNode
import ProximityPrize.SubmissionLower.RectAsymmetricRank

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 32

namespace RectAsymmetricBank
noncomputable section

open K1 (I)
open K1_14 (L FX Shape)
open K1_14_1
open Finset RectAsymmetric
open P1_7_1 (poleRows groupedPoleMoment)
open scoped BigOperators

variable {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape)

/-- The actual CRT terminal bank rank floor after rectangular node and pole charges. -/
theorem rank_floor (hpos : 0<h) (hhi : h≤131070) (hchar : h<K1.p)
    (W u v : ℕ) (hUs : u+v≤s.U) (hw : rawWidthCond h s W) :
    rectAmbientVolume h s W u v ≤ rectPhysicalDebit s u v +
      h*(u+v+2)*groupedPoleMoment s.B s.J +
      ∑ j∈range (W+1),Module.finrank FX (Rect51Bank.evaluated Crt word s (rectangle u v) j) := by
  let A : Submodule L Source := contacted h word s W ⊓ rectangle u v
  let T := Rect51Bank.restricted Crt word s (rectangle u v) W
  have hAw : A≤ambient h s W ⊓ rectangle u v := le_inf
    (inf_le_left.trans (show contacted h word s W≤ambient h s W from inf_le_left)) inf_le_right
  let : Module.Finite L (ambient h s W ⊓ rectangle u v : Submodule L Source) :=
    rectAmbient_finite h s W u v hUs
  let : Module.Finite L A :=
    Module.Finite.of_injective (Submodule.inclusion hAw) (Submodule.inclusion_injective _)
  let : Module.Finite L T := inferInstanceAs (Module.Finite L (Rect51Bank.restricted Crt word s (rectangle u v) W))
  have hAmbient := rectAmbientBound (hhi.trans (Nat.le_succ _)) s W u v hw hUs
  have hPhysical := rectPhysicalBound h word s W u v
  have hPole := finrank_le_of_pole hpos hchar Crt s u v A T
    (fun P hP=>rectShaped_of_mem (hAw hP).1 (hAw hP).2)
    (fun P hA htest=>⟨⟨hA.1,htest⟩,hA.2⟩)
  have hTelescope := Rect51Bank.telescope Crt word s (rectangle u v) hhi W
  have hDebit : RectAsymmetric.debit h s u v =
      rectPoleCredit h s u v+h*(u+v+2)*groupedPoleMoment s.B s.J := by
    unfold RectAsymmetric.debit rectPoleCredit poleRows
    ring
  rw [hDebit] at hPole
  change _ ≤ _ + Module.finrank L A at hPhysical
  change Module.finrank L T≤_ at hTelescope
  omega

#print axioms rank_floor
end
end RectAsymmetricBank
