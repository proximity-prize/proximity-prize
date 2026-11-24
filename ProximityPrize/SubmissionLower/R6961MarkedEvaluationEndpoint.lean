import ProximityPrize.SubmissionLower.R6961MarkedEvaluationLedger
import ProximityPrize.SubmissionLower.R6961RetainedLinearAssembly

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open K1 (K p)
open K1_14 (L liftPoly Equation)
open Lower6961.RescueGeometry (Model Family)
open RetainedShortening (Word)
open KoalaRect (axisDegree)
open RetainedCompression
open RetainedLinear (GeometricallyLinear)
open scoped Polynomial

def NonlinearPrice (B : MarkedBand) : Prop :=
  ∀ {u deleted} {M:Model u deleted} {Γ} (F:Family M Γ) (T:Finset K), T⊆Γ →
    Word 179818 B.wordDegree M.word F.scalar T →
    ∀ f:Curve (Polynomial L), Irreducible f → 3≤f.degreeOf ordinate → f.degreeOf ordinate<B.maxOrd →
      0<f.degreeOf parameter → height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree →
      ¬GeometricallyLinear (view f) →
      (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤rate (f.degreeOf ordinate)*f.degreeOf parameter+(f.degreeOf ordinate-1)*f.degreeOf ordinate

theorem rate_monotone : Monotone rate := by
  intro e n en
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 en) _) (Nat.sub_le_sub_right en 1))
    (Nat.mul_le_mul_left 2 en)) 1

theorem proper_rate (e : ℕ) (he : 3 ≤ e) : 12 * e ≤ rate e := by
  unfold rate
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  have h1 : (9 * (3 + k) + 2) * (3 + k - 1) + 2 * (3 + k) = 9 * k ^ 2 + 49 * k + 64 := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [this]; ring
  omega

theorem retained_of_nonlinear (B : MarkedBand) (price : NonlinearPrice B)
    (hMax axesCap retainedCap : ℕ) (witnessBound : ℕ → ℕ)
    (haxesSmall : axesCap < p) (hdegFit : 131071 + hMax ≤ B.wordDegree)
    (paid : ∀ e a b, 3≤e → e<B.maxOrd → a+b≤axesCap → b<witnessBound e →
      rate e*(a+p*b)+(e-1)*e≤retainedCap)
    {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat ≤ hMax) (T : Finset K) (f : Equation) (sub : T⊆Γ)
    (emin : 3≤f.natDegree) (emax : f.natDegree<B.maxOrd)
    (axes : axisDegree f 0+axisDegree f 1≤axesCap)
    (graded : ∀ j : Fin 2, axisDegree f j < witnessBound f.natDegree)
    (marks : ∀ γ∈T, simpleSheet f (M.label γ) (F.scalar γ)) :
    T.card ≤ retainedCap := by
  apply retained_of_tariff B hMax axesCap retainedCap witnessBound haxesSmall hdegFit
    rate rate_monotone (by decide) (fun e he _ => proper_rate e he) paid _ F hi T f sub emin emax axes graded marks
  intro u deleted M Γ F T sub words f ir lo hi sv cap marks'
  by_cases g : GeometricallyLinear (view f)
  · have irr : Irreducible (view f) := (MulEquiv.irreducible_iff view).mpr ir
    have pos : 0<(view f).natDegree := by rw [view_y]; omega
    have pure := RetainedLinear.pure_of_geometrically_linear M.word (view f) irr pos g
    have bound := pure_node_price B words (scalar M) (scalar_injective M).injOn (view f) irr pos pure marks'
    rw [view_z] at bound
    exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ((by decide : 18≤rate 3).trans (rate_monotone lo)))
      (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))))
  · exact price F T sub words f ir lo hi sv cap g marks'

end Lower6961.MarkedEvaluation
