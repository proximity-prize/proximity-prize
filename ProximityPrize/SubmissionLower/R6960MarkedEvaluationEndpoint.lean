import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger
import ProximityPrize.SubmissionLower.R6960RetainedLinearAssembly

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1 (K)
open K1_14 (L liftPoly)
open RescueGeometry (Model Family)
open RetainedShortening (Word)
open RetainedCompression
open RetainedLinear (GeometricallyLinear)
open scoped Polynomial

/-- Only the nonlinear marked factors of the actual high family need the
single-determinant estimate. The protocol, scalar list, and all other cases
are supplied by the verified 69.60 pipeline. -/
def NonlinearPrice : Prop :=
  ∀ {u deleted} {M:Model u deleted} {Γ} (F:Family M Γ) (T:Finset K), T⊆Γ →
    Word 179827 wordDegree M.word F.scalar T →
    ∀ f:Curve L[X],Irreducible f → 3≤f.degreeOf ordinate → f.degreeOf ordinate<48 →
      0<f.degreeOf parameter → height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree →
      ¬GeometricallyLinear (view f) →
      (∀ γ∈T,MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤rate (f.degreeOf ordinate)*f.degreeOf parameter+(f.degreeOf ordinate-1)*f.degreeOf ordinate

theorem protocol_of_price (price:NonlinearPrice) :
    ProximityPrize.Benchmark.ProtocolClaim 6960 ProximityPrize.SubmissionLower.Front6960Radius.p
      ProximityPrize.SubmissionLower.Front6960Radius.q := by
  have mono:Monotone rate:=by
    intro e n en
    exact Nat.sub_le_sub_right (Nat.add_le_add
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 en) _) (Nat.sub_le_sub_right en 1))
      (Nat.mul_le_mul_left 2 en)) 1
  apply Lower6960.protocol_claim_of_retained
  have proper (e:ℕ) (he:3≤e) (hi:e<48) : 12*e≤rate e :=
    (by decide +kernel : ∀ i:Fin 48, 3 ≤ i.val → 12*i.val≤rate i.val) ⟨e,hi⟩ he
  apply retained_of_tariff rate mono (by decide) proper budget
  · intro u deleted M Γ F T sub words f ir lo hi sv cap marks
    by_cases g:GeometricallyLinear (view f)
    · have irr : Irreducible (view f) := (MulEquiv.irreducible_iff view).mpr ir
      have pos : 0<(view f).natDegree := by rw [view_y];omega
      have pure:=RetainedLinear.pure_of_geometrically_linear M.word (view f) irr pos g
      have bound:=pure_node_price words (scalar M) (scalar_injective M).injOn (view f) irr pos pure marks
      rw [view_z] at bound
      exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ((by decide : 18≤rate 3).trans (mono lo)))
        (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))))
    · exact price F T sub words f ir lo hi sv cap g marks

#print axioms protocol_of_price
end Lower6960.MarkedEvaluation
