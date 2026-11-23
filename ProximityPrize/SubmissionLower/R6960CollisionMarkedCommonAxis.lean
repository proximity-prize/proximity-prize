import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisGeneric
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisSection

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler Polynomial Algebra Module
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial TensorProduct

variable {E : Type} [Field E] [Algebra ChartField E]

local instance commonAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)

local instance commonAxisFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)

def axisToGeneric (z:L) : Axis E true z→+*AxisGeneric (E:=E) z :=
  (Algebra.TensorProduct.includeRight (R:=Laurent L) (A:=FractionRing (Laurent L))
    (B:=Axis E true z)).toRingHom

/-- The Laurent quotient itself embeds in its generic algebra. The
basis proving this is localized from the genuine free line chart. -/
theorem axisToGeneric_injective [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (z:L) (nz:z≠0) : Function.Injective (axisToGeneric (E:=E) z) := by
  let U := Axis E true z
  let B := chartImage E true z false
  let Λ := Laurent L
  let F := FractionRing Λ
  let : Module.Free L[X] B := chart_free E true z false
  let A := Module.Free.chooseBasis L[X] B
  let b := localFreeBasis false A (nativeMap E true z false) (native_localization E true z nz false)
  let bk := b.baseChange F
  intro v w eq
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have h := congrArg (fun a : F⊗[Λ] U=>bk.repr a i) eq
  change (b.baseChange F).repr ((1:F) ⊗ₜ[Λ] v) i=(b.baseChange F).repr ((1:F) ⊗ₜ[Λ] w) i at h
  rw [Basis.baseChange_repr_tmul,Basis.baseChange_repr_tmul,
    Algebra.smul_def,Algebra.smul_def,mul_one,mul_one] at h
  exact IsFractionRing.injective Λ F h

/-- Evaluation in the native line chart is literal polynomial evaluation
at either the abscissa unit or its reciprocal on the common torus. -/
theorem axis_polyEval (b:Bool) (z:L) (h:L[X]) :
    polyMap E true z b h=h.eval₂ (algebraMap L (Axis E true z))
      (if b then ↑(axisX (E:=E) z)⁻¹ else ↑(axisX (E:=E) z)) := by
  let U := Axis E true z
  let π : Tor E→+*U := Ideal.Quotient.mk (axisIdeal E true z)
  let a : U := if b then ↑(axisX (E:=E) z)⁻¹ else ↑(axisX (E:=E) z)
  let ev := eval₂RingHom (algebraMap L U) a
  have identity : polyMap E true z b=ev := by
    apply Polynomial.ringHom_ext
    · intro c
      change π (along E true b (C c))=ev (C c)
      rw [show along E true b (C c)=algebraMap L (Tor E) c from eval₂_C _ _,show ev (C c)=algebraMap L U c from eval₂_C _ _]
      rfl
    · rw [show ev Polynomial.X=a from eval₂_X _ _]
      change π (along E true b Polynomial.X)=a
      rw [show along E true b Polynomial.X=torVar E false b from eval₂_X _ _]
      cases b <;> rfl
  exact DFunLike.congr_fun identity h

/-- A scalar from either affine chart maps to the matching polynomial
in the common generic fibre. -/
theorem axisGenericData_scalar [FiniteDimensional ChartField E]
    (b:Bool) (z:L) (nz:z≠0) (h:L[X]) :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    let V := FibreGeneric (E:=E) z
    let g : V≃+*AxisGeneric (E:=E) z := (axisGenericData (E:=E) b z nz).val
    g (algebraMap L[X] V h)=axisToGeneric (E:=E) z (polyMap E true z b h) := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let B := Fiber E z
  let V := FibreGeneric (E:=E) z
  let g := axisGenericData (E:=E) b z nz
  let f := axisFibreData (E:=E) b z nz
  have j : algebraMap L[X] V h=(1 ⊗ₜ[L[X]] (algebraMap L[X] B h):V) :=
    (Algebra.TensorProduct.includeRight (R:=L[X]) (A:=FractionRing L[X]) (B:=B)).commutes h |>.symm
  change g.val (algebraMap L[X] V h)=axisToGeneric (E:=E) z (polyMap E true z b h)
  rw [j,g.property.1]
  change axisToGeneric (E:=E) z (f.val (baseMap E z h))=_
  rw [axisFibreData_scalar]

#print axioms axisToGeneric_injective
#print axioms axisGenericData_scalar
end
end Lower6960.CollisionMarked
