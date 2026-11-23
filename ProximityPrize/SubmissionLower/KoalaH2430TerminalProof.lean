import ProximityPrize.SubmissionLower.KoalaRectBridgeCore
import ProximityPrize.SubmissionLower.KoalaH2430Reject23
import ProximityPrize.SubmissionLower.KoalaH2430Terminal

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

namespace KoalaH2430Terminal
noncomputable section
open Polynomial Finset
open HighCore82258 (AnchorModel agreement Reduced crtWord)
open K1_14 (Equation)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_3 (Surface Parent ProjectedProduct)
open KoalaRect (axisDegree rectSlots rectGain rectDebit rectLoss)
open Pr657Rect2435Axes

theorem paid_degrees {u del} (M : AnchorModel u del) {D : PoleData 2430} (Crt : CRTLift D)
    {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : ∀ q ∈ qs, ∀ P ∈ evaluated Crt (crtWord M) terminal.shape
      (terminal.shape.m*agreement-1), P ∈ q.asIdeal)
    {f : Equation} (hf : Reduced f) (hprod : ProjectedProduct qs f) :
    f.natDegree < 23 ∧ axisDegree f 0+axisDegree f 1≤paidCap f.natDegree := by
  have hl : 2430 ≤ 2430 := le_rfl
  have hraw : 2430 < 131071 := by decide
  have he:1≤f.natDegree:=hf.1
  have hfull := grade_lt_23 M Crt hgeo hpass hprod
  refine ⟨hfull, ?_⟩
  by_contra! hv
  let E:=f.natDegree
  let T:=rectWitness E
  obtain ⟨hside,hbox⟩:=witness_guards he hfull.le
  obtain ⟨hlo,hhi,hsum⟩:=paid_order he hfull
  have hcost:=KoalaH2430Terminal.rect_bounds hl hraw he hfull.le
  have hdegree : T.order 0 + T.order 1 ≤ axisDegree f 0 + axisDegree f 1 := by
    rw [hsum]
    exact hv
  by_cases hor:axisDegree f 0≤axisDegree f 1
  · refine reject_shape Crt M hgeo hpass hf hprod (le_refl E) he T.U T.order hbox ?_ hcost
    intro r
    exact HighCore82258.oriented_rect_capacity_le hside hor hlo hhi hdegree
  · have hbox' : swap T.U 0 + swap T.U 1 ≤ terminal.shape.U := by
      simpa [Nat.add_comm] using hbox
    exact reject_shape Crt M hgeo hpass hf hprod (le_refl E) he (swap T.U) (swap T.order) hbox'
      (fun r => slots_reversed r hside (Nat.le_of_not_ge hor) hlo hhi hdegree)
      (KoalaH2430Terminal.rect_bounds_swap hl hraw he hfull.le)

#print axioms paid_degrees
end
end KoalaH2430Terminal
