import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

namespace Low6960SharedPrice

open K1_13 (Shape)
open K1_13_8 (Valid)
open Low6960Prices (BentCap addBent bentIntegral bentGraph bentLift taylorLength tiltedFits)
open Low48BentLattice (Chamber)

open private signedFive signed_five_linear signed_five_nonneg
  from ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

/-- The tilted signed surface is linear in the cutter shape. Chamber positivity
also certifies the exact natural-number coefficients in the price ledger. -/
theorem surface_tilted_eq_weights {f : Shape} (hf : Valid f) (ht : tiltedFits f) (q : Shape) :
    surface .tilted f q = (weights .tilted f).b*q.b + (weights .tilted f).j*q.j +
      (weights .tilted f).t*q.t := by
  let p := f.chamber
  let g := bentGraph p
  let l := bentLift (taylorLength-4) p
  let r := bentLift (taylorLength-3) p
  have hb : p.j ≤ p.b := le_max_right _ _
  have hp : Chamber (p,0) := ⟨hb,hf.2.1,Nat.zero_le _⟩
  have hg : Chamber g := Low48BentSupport.graph_chamber hf.1 ht.1
  have hl : Chamber l := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-4)
  have hr : Chamber r := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-3)
  have hnonneg (u : Shape) : 0 ≤ signedFive (p,0) (u,0) g l r :=
    signed_five_nonneg u _ _ _ _ hp hg hl hr
  refine surface_eq_weights_of_signed .tilted f _ _ _ (hnonneg ⟨1,0,0⟩)
    (hnonneg ⟨0,1,0⟩) (hnonneg ⟨0,0,1⟩) (fun u => ?_) q
  change (↑(signedFive (p,0) (u,0) g l r).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg (hnonneg u)]
  exact signed_five_linear u _ _ _ _

#print axioms surface_tilted_eq_weights
end Low6960SharedPrice
