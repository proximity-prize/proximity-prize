import ProximityPrize.SubmissionLower.R6961CollisionMarkedAxisLaurent
import ProximityPrize.SubmissionLower.R6961CollisionMarkedIndexSupport

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4100000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Lower6960.NormalizedFiber RetainedSurfaceClass Lower6960.LineEuler Polynomial Algebra
open scoped Lower6960.CollisionMarked Lower6961.CollisionMarked Lower6961.RetainedSurfaceClass Polynomial TensorProduct
open Lower6960.LineEuler (chartLocalization)

private theorem lineCoordinateUnit
    (t : Submonoid.powers (Polynomial.X:(Polynomial L))) :
    IsUnit (algebraMap (Polynomial L) (FractionRing (Polynomial L)) (t:(Polynomial L))) := by
  obtain ⟨n,nt⟩ := t.property
  apply IsUnit.mk0
  apply (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) (FractionRing (Polynomial L)))).mpr
  rw [←nt]
  exact pow_ne_zero _ Polynomial.X_ne_zero

@[instance_reducible] def laurentOnFraction (b:Bool) : Algebra (Laurent L) (FractionRing (Polynomial L)) :=
  let : Algebra (Polynomial L) (Laurent L) := (chartEmbedding b).toRingHom.toAlgebra
  let : IsLocalization.Away (Polynomial.X:(Polynomial L)) (Laurent L) := Lower6960.LineEuler.chartLocalization b
  (IsLocalization.lift (M:=Submonoid.powers (Polynomial.X:(Polynomial L)))
    (g:=algebraMap (Polynomial L) (FractionRing (Polynomial L))) lineCoordinateUnit).toAlgebra

theorem laurentOnFraction_scalar (b:Bool) (a:(Polynomial L)) :
    let : Algebra (Laurent L) (FractionRing (Polynomial L)) := laurentOnFraction b
    algebraMap (Laurent L) (FractionRing (Polynomial L)) (chartEmbedding b a)=
      algebraMap (Polynomial L) (FractionRing (Polynomial L)) a := by
  let : Algebra (Polynomial L) (Laurent L) := (chartEmbedding b).toRingHom.toAlgebra
  let : IsLocalization.Away (Polynomial.X:(Polynomial L)) (Laurent L) := Lower6960.LineEuler.chartLocalization b
  change IsLocalization.lift (M:=Submonoid.powers (Polynomial.X:(Polynomial L))) lineCoordinateUnit
    (algebraMap (Polynomial L) (Laurent L) a)=_
  exact IsLocalization.lift_eq _ _

@[instance_reducible] def lineOnLaurentFraction (b:Bool) : Algebra (Polynomial L) (FractionRing (Laurent L)) :=
  ((algebraMap (Laurent L) (FractionRing (Laurent L))).comp (chartEmbedding b).toRingHom).toAlgebra

/-- The two generic line fields embed into the same Laurent fraction
field. The inverse chart uses the inverse Laurent coordinate. -/
def chartFractionToLaurent (b:Bool) :
    let : Algebra (Polynomial L) (FractionRing (Laurent L)) := lineOnLaurentFraction b
    FractionRing (Polynomial L) ≃ₐ[(Polynomial L)] FractionRing (Laurent L) := by
  let R := (Polynomial L)
  let Λ := Laurent L
  let K := FractionRing R
  let F := FractionRing Λ
  let : Algebra R F := lineOnLaurentFraction b
  let : Algebra R Λ := (chartEmbedding b).toRingHom.toAlgebra
  let : Algebra Λ K := laurentOnFraction b
  let : SMul R K := (inferInstance : Algebra R K).toSMul
  let : IsScalarTower R Λ K := IsScalarTower.of_algebraMap_eq fun r=>(laurentOnFraction_scalar b r).symm
  let : IsLocalization.Away (Polynomial.X:R) Λ := Lower6960.LineEuler.chartLocalization b
  let : IsFractionRing Λ K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (Polynomial.X:R)) Λ K
  let e := IsLocalization.algEquiv (nonZeroDivisors Λ) K F
  refine { e.toRingEquiv with commutes' := fun r=>?_ }
  change e (algebraMap R K r)=algebraMap R F r
  rw [←laurentOnFraction_scalar b r,e.commutes]
  rfl

variable {E : Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]

local instance genericAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)

local instance genericAxisFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)

abbrev AxisGeneric (z:L) := (FractionRing (Laurent L))⊗[Laurent L] Axis E true z

/-- Identify each separate affine generic fibre with the common
localization of the geometric torus fibre. Both the original order's
quotient map and the direction of the scalar embedding are explicit. -/
def axisGenericData (b:Bool) (z:L) (nz:z≠0) :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    let φ : Fiber E z→+*Axis E true z := (axisFibreData (E:=E) b z nz).val
    { e : FibreGeneric (E:=E) z ≃+* AxisGeneric (E:=E) z //
      (∀ v:Fiber E z,e (1 ⊗ₜ[(Polynomial L)] v)=1 ⊗ₜ[Laurent L] φ v) ∧
      ∀ r:FractionRing (Polynomial L),e (r ⊗ₜ[(Polynomial L)] 1)=chartFractionToLaurent b r ⊗ₜ[Laurent L] 1 } := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let R := (Polynomial L)
  let Λ := Laurent L
  let K := FractionRing R
  let F := FractionRing Λ
  let B := Fiber E z
  let U := Axis E true z
  let : Algebra R Λ := (chartEmbedding b).toRingHom.toAlgebra
  let : Algebra R B := Lower6960.CollisionMarked.fibreAlgebra z
  let : Algebra R F := lineOnLaurentFraction b
  let : Module R Λ := (inferInstance : Algebra R Λ).toModule
  let : Module R B := (inferInstance : Algebra R B).toModule
  let : Module R F := (inferInstance : Algebra R F).toModule
  let : Module Λ F := (inferInstance : Algebra Λ F).toModule
  let : SMul R Λ := (inferInstance : Algebra R Λ).toSMul
  let : SMul Λ F := (inferInstance : Algebra Λ F).toSMul
  let : SMul R F := (inferInstance : Algebra R F).toSMul
  let : IsScalarTower R Λ F := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsScalarTower R R F := IsScalarTower.of_algebraMap_eq (R:=R) (S:=R) (A:=F) fun _=>by
    rw [Algebra.algebraMap_self,RingHom.id_apply]
  let φ := (axisFibreData (E:=E) b z nz).val
  let first : (K⊗[R] B) ≃ₐ[R] (F⊗[R] B) :=
    Algebra.TensorProduct.congr (chartFractionToLaurent b) (AlgEquiv.refl (R:=R) (A₁:=B))
  let : CommRing (Λ⊗[R] B) := Algebra.TensorProduct.instCommRing (R:=R) (A:=Λ) (B:=B)
  let : Algebra Λ (Λ⊗[R] B) :=
    Algebra.TensorProduct.leftAlgebra (R:=R) (S:=Λ) (A:=Λ) (B:=B)
  let : Module Λ (Λ⊗[R] B) := (inferInstance : Algebra Λ (Λ⊗[R] B)).toModule
  let middle := (Algebra.TensorProduct.cancelBaseChange R Λ F F B).symm
  let torus := axisLaurentData (E:=E) b z nz
  let last : (F⊗[Λ] (Λ⊗[R] B))≃ₐ[F](F⊗[Λ] U) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R:=F) (A₁:=F)) torus.val
  have first_tmul (r:K) (v:B) : first (r ⊗ₜ[R] v)=chartFractionToLaurent b r ⊗ₜ[R] v := by
    dsimp only [first]
    rw [Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
    rfl
  refine ⟨first.toRingEquiv.trans (middle.toRingEquiv.trans last.toRingEquiv),?_,?_⟩
  · intro v
    change last (middle (first (1 ⊗ₜ[R] v)))=_
    rw [first_tmul,map_one,Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    change (1:F) ⊗ₜ[Λ] torus.val (1 ⊗ₜ[R] v)=_
    rw [torus.property]
  · intro r
    change last (middle (first (r ⊗ₜ[R] (1:B))))=_
    rw [first_tmul,Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    change (chartFractionToLaurent b r) ⊗ₜ[Λ] torus.val (1 ⊗ₜ[R] (1:B))=_
    rw [torus.property,map_one]

#print axioms axisGenericData
end
end Lower6961.CollisionMarked
