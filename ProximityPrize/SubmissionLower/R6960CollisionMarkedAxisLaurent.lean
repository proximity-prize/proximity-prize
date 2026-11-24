import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxis
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3800000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler Polynomial Algebra
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial TensorProduct
open Lower6960.LineEuler (chartLocalization)

variable {E : Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]

local instance axisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)

local instance axisFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)

abbrev LaurentFibreComparison (R Λ B U : Type*) [CommRing R] [CommRing Λ] [CommRing B]
    [CommRing U] [Algebra R Λ] [Algebra R B] [Algebra Λ U] (φ:B→+*U) :=
  { e : (Λ ⊗[R] B) ≃ₐ[Λ] U // ∀ v:B,e (1 ⊗ₜ[R] v)=φ v }

/-- Inverting the actual abscissa coordinate on either original
normalized surface fibre gives the same Laurent ring quotient. -/
def axisLaurentData (b:Bool) (z:L) (nz:z≠0) :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    let φ : Fiber E z→+*Axis E true z := (axisFibreData (E:=E) b z nz).val
    let : Algebra (Polynomial L) (Laurent L) := (chartEmbedding b).toRingHom.toAlgebra
    let : Algebra (Polynomial L) (Fiber E z) := CollisionMarked.fibreAlgebra z
    LaurentFibreComparison (Polynomial L) (Laurent L) (Fiber E z) (Axis E true z) φ := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let R := (Polynomial L)
  let Λ := Laurent L
  let B := Fiber E z
  let U := Axis E true z
  let data := axisFibreData (E:=E) b z nz
  let φ : B→+*U := data.val
  let : Algebra R Λ := (chartEmbedding b).toRingHom.toAlgebra
  let : Algebra R B := CollisionMarked.fibreAlgebra z
  let two : Algebra B U := φ.toAlgebra
  let : Algebra B U := two
  let : SMul B U := two.toSMul
  let : SMul R B := (inferInstance : Algebra R B).toSMul
  let : Algebra R U := ((axisLaurent E true z).comp (chartEmbedding b).toRingHom).toAlgebra
  let : IsScalarTower R Λ U := IsScalarTower.of_algebraMap_eq fun _=>rfl
  have scal (f : R) : φ (algebraMap R B f)=algebraMap R U f := by
    change φ (baseMap E z f)=((axisLaurent E true z).comp (chartEmbedding b).toRingHom) f
    rw [axisFibreData_scalar, signed_chart]
  let : IsScalarTower R B U := IsScalarTower.of_algebraMap_eq fun f=>(scal f).symm
  let S := Submonoid.powers (Polynomial.X : R)
  let f : B→ₗ[R]U := (IsScalarTower.toAlgHom R B U).toLinearMap
  have lifts (w:U) : ∃ n:ℕ,∃ v:B,(chartEmbedding b (Polynomial.X:R))^n • w=f v := by
    let orig := nativeMap E true z b
    let : IsLocalizedModule S orig := native_localization E true z nz b
    obtain ⟨⟨u,t⟩,rel⟩ := IsLocalizedModule.surj S orig w
    obtain ⟨n,ne⟩ := t.property
    obtain ⟨v,hv⟩ := (data.property.2.2 u.val).mpr u.property
    refine ⟨n,v,?_⟩
    change (chartEmbedding b (t:R)) • w=u.val at rel
    rw [←ne,map_pow,←hv] at rel
    exact rel
  let : IsLocalizedModule S f := isChartLocalization_of_clearing b f
    (fun x y h=>data.property.1 h) lifts
  let : IsLocalization S Λ := Lower6960.LineEuler.chartLocalization b
  letI : IsLocalization (Algebra.algebraMapSubmonoid B S) U :=
    isLocalizedModule_iff_isLocalization.mp (inferInstance : IsLocalizedModule S f)
  let push : Algebra.IsPushout R B Λ U := Algebra.isPushout_of_isLocalization S Λ B U
  letI : Algebra.IsPushout R Λ B U := push.symm
  refine ⟨Algebra.IsPushout.equiv R Λ B U,fun v=>?_⟩
  rw [Algebra.IsPushout.equiv_tmul,map_one,one_mul]
  rfl


#print axioms axisLaurentData
end
end Lower6960.CollisionMarked
