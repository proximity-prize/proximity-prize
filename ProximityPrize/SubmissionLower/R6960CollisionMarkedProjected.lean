import ProximityPrize.SubmissionLower.R6960CollisionMarkedActualSheet

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial NormalizedFiber Module
open K1_14 (L)
open RetainedCompression (MarkedFiber specialize incl eval_swap)
open scoped Polynomial TensorProduct Lower6960.CollisionMarked

/-- Put the actual scalar coordinate in the outer plane variable, as used
by the quotient defining `NormalizedFiber.Fiber`. -/
def projectedRaw (P : CurvatureSquares.Ordinate) : (Polynomial (Plane L)) := P.map Bivariate.swap.toRingHom

theorem projectedRaw_degree (P : CurvatureSquares.Ordinate) :
    (projectedRaw P).natDegree=P.natDegree :=
  natDegree_map_eq_of_injective Bivariate.swap.injective _

theorem projectedRaw_fibre (P : CurvatureSquares.Ordinate) (z : L) :
    (projectedRaw P).map (genericFibreBase z)=(specialize P z).map incl := by
  apply Polynomial.ext
  intro i
  simp only [projectedRaw,RetainedCompression.specialize,coeff_map,Polynomial.coe_mapRingHom]
  change incl ((Bivariate.swap (P.coeff i)).eval (Polynomial.C z))=incl ((P.coeff i).map (evalRingHom z))
  rw [eval_swap]

/-- The native full/separable mark gives the generic word projector in
the actual quotient of the plane normalization. -/
theorem projected_word_sheet {E : Type} [Field E] [Algebra (Plane L) E]
    [Algebra (FractionRing (Plane L)) E] [IsScalarTower (Plane L) (FractionRing (Plane L)) E]
    [FiniteDimensional (FractionRing (Plane L)) E]
    (p : ℕ) [CharP (FractionRing (Polynomial L)) p]
    (P : CurvatureSquares.Ordinate) (large : 2≤P.natDegree) (small : P.natDegree<p)
    (b : PowerBasis (FractionRing (Plane L)) E) (dim : b.dim=P.natDegree)
    (root : aeval b.gen (projectedRaw P)=0) (z : L) (S : (Polynomial L)) (mark : MarkedFiber P z S) :
    let pn : projectedRaw P≠0 := fun h=>by
      have d := projectedRaw_degree P
      rw [h,natDegree_zero] at d
      omega
    let q := (projectedRaw P).integralNormalization.map (genericFibreBase z)
    let y := genericFibreBase z (projectedRaw P).leadingCoeff*incl S
    ∃ (e : AdjoinRoot q ≃ₐ[FractionRing (Polynomial L)] ((FractionRing (Polynomial L))⊗[(Polynomial L)] Fiber E z))
      (H Q : (Polynomial (FractionRing (Polynomial L)))),
      q.Separable ∧ q=(Polynomial.X-C y)*Q ∧ H.eval y=1 ∧ Q∣H ∧
      e (AdjoinRoot.root q)=scaledOrdinate (projectedRaw P) b.gen pn root z ∧
      let η:=e (AdjoinRoot.mk q H)
      η^2=η ∧ η≠0 ∧ η≠1 ∧
        (scaledOrdinate (projectedRaw P) b.gen pn root z-(y ⊗ₜ[(Polynomial L)] (1:Fiber E z)))*η=0 := by
  have full : ((projectedRaw P).map (genericFibreBase z)).natDegree=(projectedRaw P).natDegree := by
    rw [projectedRaw_fibre,natDegree_map_eq_of_injective (IsFractionRing.injective _ _),mark.full,projectedRaw_degree]
  have sep : ((projectedRaw P).map (genericFibreBase z)).Separable := projectedRaw_fibre P z ▸ mark.separable
  have rt : ((projectedRaw P).map (genericFibreBase z)).eval (incl S)=0 := by
    rw [projectedRaw_fibre,Polynomial.eval_map_apply,mark.root,map_zero]
  exact actual_scaled_word_sheet p (projectedRaw P) (projectedRaw_degree P ▸ large)
    (projectedRaw_degree P ▸ small) b (dim.trans (projectedRaw_degree P).symm) root z S full sep rt

#print axioms projected_word_sheet
end
end Lower6960.CollisionMarked
