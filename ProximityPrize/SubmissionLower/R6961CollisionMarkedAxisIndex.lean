import ProximityPrize.SubmissionLower.R6961CollisionMarkedCommonAxis
import ProximityPrize.SubmissionLower.R6961CollisionMarkedAxisField
import ProximityPrize.SubmissionLower.R6961CollisionMarkedInfinityIndex

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Lower6960.NormalizedFiber RetainedSurfaceClass Lower6960.LineEuler Polynomial Algebra Lower6960.CollisionTame Lower6961.CollisionTame Module
open scoped Lower6960.CollisionMarked Lower6961.CollisionMarked Lower6961.RetainedSurfaceClass Polynomial TensorProduct

variable {E : Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]

local instance indexedAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)

local instance indexedFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)

theorem axisFractionFinite (b:Bool) :
    let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
    FiniteDimensional (FractionRing (Plane L)) E := by
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
  exact Module.Finite.of_basis (axisFractionBasis (E:=E) b (Module.finBasis ChartField E)).val

theorem axisFractionRank (b:Bool) :
    let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
    finrank (FractionRing (Plane L)) E = finrank ChartField E := by
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
  exact (finrank_eq_card_basis (axisFractionBasis (E:=E) b (Module.finBasis ChartField E)).val).trans
    (Fintype.card_fin _)

def axisDiscriminant (b:Bool) : Ideal (Plane L) :=
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower b
  let : FiniteDimensional (FractionRing (Plane L)) E := axisFractionFinite b
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := axisFraction_separable b
  normalizationDiscriminant (A:=Plane L) (E:=E) (FractionRing (Plane L))

omit [Algebra.IsSeparable ChartField E] in
private theorem reducedOnChart (b:Bool) (z:L) (nz:z≠0) [IsReduced (AxisGeneric (E:=E) z)] :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    IsReduced (FibreGeneric (E:=E) z) := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let g := (axisGenericData (E:=E) b z nz).val
  constructor
  intro x hx
  apply g.injective
  rw [map_zero]
  exact IsReduced.eq_zero _ (hx.map g.toRingHom)

omit [Algebra.IsSeparable ChartField E] in
/-- An index clearing in the original fibre ring becomes literally the
same marked multiple in the common generic algebra. -/
private theorem chartClear (b:Bool) (z:L) (nz:z≠0)
    (d:(Polynomial L)) (η:AxisGeneric (E:=E) z) (idem:η^2=η)
    (clear : let : Algebra (Plane L) E := axisPlaneAlgebra b
      ∀ x:FibreGeneric (E:=E) z,IsIntegral (Polynomial L) x →
        ∃ u:Fiber E z,(1 ⊗ₜ[(Polynomial L)] u : FibreGeneric (E:=E) z)=
          algebraMap (Polynomial L) (FibreGeneric (E:=E) z) d*x) :
    ∃ v∈chartImage E true z b,
      axisToGeneric (E:=E) z v=axisToGeneric (E:=E) z (polyMap E true z b d)*η := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let V := FibreGeneric (E:=E) z
  let G := axisGenericData (E:=E) b z nz
  let g := G.val
  let x : V := g.symm η
  have idemx : x^2=x :=
    (map_pow g.symm η 2).symm.trans (congrArg g.symm idem)
  obtain ⟨u,hu⟩ := clear x (idempotent_integral (A:=(Polynomial L)) x idemx)
  let φ := axisFibreData (E:=E) b z nz
  refine ⟨φ.val u,(φ.property.2.2 _).mp ⟨u,rfl⟩,?_⟩
  have m := congrArg g hu
  rw [G.property.1,map_mul,axisGenericData_scalar] at m
  change axisToGeneric (E:=E) z (φ.val u)=axisToGeneric (E:=E) z (polyMap E true z b d)*g (g.symm η) at m
  rw [RingEquiv.apply_symm_apply] at m
  exact m

/-- The actual finite-side determinant retains its square divisibility
and collision support while clearing the projector on the native axis. -/
theorem actual_axis_finite_index (p:ℕ) [CharP L p] [CharP (FractionRing (Polynomial L)) p]
    (small:finrank ChartField E<p) (z:L) (nz:z≠0) [IsReduced (AxisGeneric (E:=E) z)]
    (δ:Plane L) (nonzero:δ≠0) (principal:axisDiscriminant (E:=E) false=Ideal.span {δ})
    [DecidableEq L] :
    (branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0 ∧
    ∃ d:(Polynomial L), d≠0 ∧ d^2∣δ.eval (C z) ∧
      (∀ x∈d.roots,2≤((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x) ∧
      ∀ η:AxisGeneric (E:=E) z, η^2=η →
        ∃ v∈chartImage E true z false,
          axisToGeneric (E:=E) z v=axisToGeneric (E:=E) z (polyMap E true z false d)*η := by
  let : Algebra (Plane L) E := axisPlaneAlgebra false
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower false
  let : FiniteDimensional (FractionRing (Plane L)) E := axisFractionFinite false
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := axisFraction_separable false
  let : IsReduced (FibreGeneric (E:=E) z) := reducedOnChart false z nz
  have degree : finrank (FractionRing (Plane L)) E<p :=
    (axisFractionRank (E:=E) false).symm ▸ small
  obtain ⟨good,d,dn,dvd,support,clear⟩ := fibre_index_supported p degree z δ nonzero principal
  exact ⟨good,d,dn,dvd,support,fun η idem=>chartClear false z nz d η idem clear⟩

/-- The actual reciprocal determinant clears the same idempotent and
is a unit at the boundary whenever the single seed polynomial survives. -/
theorem actual_axis_infinity_index (p:ℕ) [CharP L p] [CharP (FractionRing (Polynomial L)) p]
    (small:finrank ChartField E<p) (z:L) (nz:z≠0) [IsReduced (AxisGeneric (E:=E) z)]
    (δ:Plane L) (nonzero:δ≠0) (principal:axisDiscriminant (E:=E) true=Ideal.span {δ})
    [DecidableEq L] (good:(Bivariate.swap δ).trailingCoeff.eval z≠0) :
    ∃ d:(Polynomial L),d.eval 0≠0 ∧
      ∀ η:AxisGeneric (E:=E) z,η^2=η →
        ∃ v∈chartImage E true z true,
          axisToGeneric (E:=E) z v=axisToGeneric (E:=E) z (polyMap E true z true d)*η := by
  let : Algebra (Plane L) E := axisPlaneAlgebra true
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra true
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower true
  let : FiniteDimensional (FractionRing (Plane L)) E := axisFractionFinite true
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := axisFraction_separable true
  let : IsReduced (FibreGeneric (E:=E) z) := reducedOnChart true z nz
  have degree : finrank (FractionRing (Plane L)) E<p :=
    (axisFractionRank (E:=E) true).symm ▸ small
  obtain ⟨d,d0,clear⟩ := boundary_index p degree δ nonzero principal z good
  exact ⟨d,d0,fun η idem=>chartClear true z nz d η idem clear⟩

#print axioms actual_axis_finite_index
#print axioms actual_axis_infinity_index
end
end Lower6961.CollisionMarked
