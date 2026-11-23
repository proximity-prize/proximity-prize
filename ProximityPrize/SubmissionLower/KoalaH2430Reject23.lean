import ProximityPrize.SubmissionLower.KoalaRectBridgeCore
import ProximityPrize.SubmissionLower.KoalaH2430TerminalBank
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade23
import ProximityPrize.SubmissionLower.HighCore82258Family

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
open Pr657Rect2435Arithmetic (strict_of_checks)

theorem reject_shape {D : PoleData 2430} (Crt : CRTLift D) {u del}
    (M : AnchorModel u del) {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : ∀ q ∈ qs, ∀ P ∈ evaluated Crt (crtWord M) terminal.shape
      (terminal.shape.m*agreement-1), P ∈ q.asIdeal)
    {f : Equation} (hf : Reduced f) (hprod : ProjectedProduct qs f)
    {E : ℕ} (hE : E ≤ f.natDegree) (he : 0 < E)
    (U d : Fin 2 → ℕ) (hbox : U 0+U 1≤terminal.shape.U)
    (hslots : ∀ r, rectSlots U (axisDegree f) r≤rectSlots U d r)
    (hstrict : rectDebit 2430 terminal.nodeRows terminal.poleMoment U <
      rectGain agreement 2430 terminal.shape E U d) : False := by
  let t := terminal
  obtain ⟨hA,hsmall,hwid⟩ := terminal_guards
  have hne : f ≠ 0 := by
    intro hz
    have hp:=hf.1
    simp [hz] at hp
  have hbank := KoalaH2430Terminal.terminal_ok
  have hcut := rectLoss (h := 2430) (by decide) (by decide) (by decide)
    Crt (crtWord M) agreement t.shape U d hA hsmall hbox hbank.moment.2 hwid
    hbank.nodes.le hbank.moment.1 he hgeo hpass hne hE hprod hslots
  exact (not_le_of_gt hstrict) hcut

/-- The order-zero rank receipt rejects every grade at or above 23.
The only terminal input is vanishing of the actual evaluated bank. -/
theorem grade_lt_23 {u del} (M : AnchorModel u del) {D : PoleData 2430} (Crt : CRTLift D)
    {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : ∀ q ∈ qs, ∀ P ∈ evaluated Crt (crtWord M) terminal.shape
      (terminal.shape.m*agreement-1), P ∈ q.asIdeal)
    {f : Equation} (hprod : ProjectedProduct qs f) :
    f.natDegree < 23 := by
  have hf : Reduced f := ⟨hprod.positive, hprod.primitive, hprod.separable⟩
  by_contra! he
  let T := rectWitness 23
  have hstrict : rectDebit 2430 terminal.nodeRows terminal.poleMoment T.U <
      rectGain agreement 2430 terminal.shape 23 T.U T.order :=
    strict_of_checks (b := terminal) (v := T) (show 2430 ≤ 2430 from le_rfl) (by decide) (by decide) (by decide)
      (by decide) r23.1
  refine reject_shape Crt M hgeo hpass hf hprod he (by decide) T.U T.order
    (witness_guards (by decide : 1 ≤ 23) (by decide)).2 ?_ hstrict
  intro r
  have h0 : T.order 0 = 0 := by decide
  have h1 : T.order 1 = 0 := by decide
  simp only [rectSlots,h0,h1,Nat.mul_zero,Nat.sub_zero]
  exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)

#print axioms grade_lt_23

end
end KoalaH2430Terminal
