import ProximityPrize.SubmissionLower.R6961CollisionMarkedGenericFrames
import ProximityPrize.SubmissionLower.R6960HornerNative
import ProximityPrize.SubmissionLower.R6961MarkedScalarAxis

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (Scalar ChartField)
open MonicFourChartDescent RetainedRestrictionTorus
open Lower6961.MarkedEvaluation (swapBase swap_x swap_z swap_constant)
open Polynomial Lower6960.CollisionTame Lower6961.CollisionTame Lower6960.LineEuler
open scoped Polynomial
open Lower6960.LineEuler (chartLocalization)
open Lower6961.CollisionMarked (lineEmbedding lineEmbedding_on_plane)
open Lower6961.CollisionMarked (outerField outer_CC outer_X outer_CX)

private def orientField (j:Bool) : ChartField→+*ChartField :=
  if j then RingHom.id _ else swapBase.toRingHom

private theorem orient_const (j:Bool) (r:L) :
    orientField j (constants r)=constants r := by
  cases j
  · exact swap_constant r
  · rfl

private theorem orient_seed (j:Bool) : orientField j scalarCoordinate=coordinate j := by
  cases j
  · exact swap_z
  · rfl

private theorem orient_line (j:Bool) : orientField j RatFunc.X=coordinate (!j) := by
  cases j
  · exact swap_x
  · rfl

private theorem embedding_coefficients (j:Bool) :
    (Lower6961.CollisionMarked.lineEmbedding j false).comp Polynomial.C=
      (orientField j).comp RatFunc.C := by
  let U := (Polynomial L)
  let A := PlaneRing L
  let R := GenericLine L
  let d := algebraMap U Scalar
  have poly : (Lower6961.CollisionMarked.outerField j false).comp Polynomial.C=
      ((orientField j).comp RatFunc.C).comp d := by
    apply Polynomial.ringHom_ext
    · intro r
      change Lower6961.CollisionMarked.outerField j false (Polynomial.C (Polynomial.C r))=
        orientField j (constants r)
      rw [Lower6961.CollisionMarked.outer_CC,orient_const]
    · change Lower6961.CollisionMarked.outerField j false (Polynomial.C Polynomial.X)=
        orientField j scalarCoordinate
      rw [Lower6961.CollisionMarked.outer_CX,orient_seed]
  apply IsFractionRing.ringHom_ext (A:=U)
  intro a
  change Lower6961.CollisionMarked.lineEmbedding j false (Polynomial.C (d a))=
    orientField j (RatFunc.C (d a))
  have h : (Polynomial.C (d a):R)=(Polynomial.C a:A).map d := (map_C d).symm
  rw [h]
  have q := Lower6961.CollisionMarked.lineEmbedding_on_plane j false (Polynomial.C a)
  have e := DFunLike.congr_fun poly a
  exact q.trans e

/-- The actual generic Laurent chart is the usual rational Laurent
embedding in the vertical ruling and the switched coordinates in the
horizontal ruling. -/
theorem genericLaurent_coordinates (j:Bool) :
    (genericPlaneField j).toRingHom.comp (genericLaurent L)=
      (orientField j).comp (Lower6960.Horner.rationalLaurent (k:=Scalar)) := by
  let A := GenericLine L
  let R := Laurent Scalar
  let S := Submonoid.powers (Polynomial.X:A)
  let : Algebra A R := (chartEmbedding (k:=Scalar) false).toRingHom.toAlgebra
  let : IsLocalization S R := Lower6960.LineEuler.chartLocalization false
  apply IsLocalization.ringHom_ext S
  apply Polynomial.ringHom_ext
  · intro r
    change (Lower6961.CollisionMarked.lineEmbedding j false) (Polynomial.C r)=
      orientField j (Lower6960.Horner.rationalLaurent (chartEmbedding false (Polynomial.C r)))
    rw [show Lower6960.Horner.rationalLaurent (chartEmbedding false (Polynomial.C r))=
      algebraMap (Polynomial Scalar) ChartField (Polynomial.C r) from
        DFunLike.congr_fun Lower6960.Horner.rationalLaurent_finite _,RatFunc.algebraMap_C]
    exact DFunLike.congr_fun (embedding_coefficients j) r
  · change (Lower6961.CollisionMarked.lineEmbedding j false) (Polynomial.X:A)=
      orientField j (Lower6960.Horner.rationalLaurent (chartEmbedding false (Polynomial.X:A)))
    rw [show Lower6960.Horner.rationalLaurent (chartEmbedding false (Polynomial.X:A))=
      algebraMap (Polynomial Scalar) ChartField Polynomial.X from
        DFunLike.congr_fun Lower6960.Horner.rationalLaurent_finite _,RatFunc.algebraMap_X,orient_line]
    have hx := Lower6961.CollisionMarked.lineEmbedding_on_plane j false (Polynomial.X:PlaneRing L)
    change Lower6961.CollisionMarked.lineEmbedding j false
      ((Polynomial.X:PlaneRing L).map (algebraMap (Polynomial L) Scalar))=_ at hx
    rw [map_X,Lower6961.CollisionMarked.outer_X] at hx
    exact hx

variable {E:Type} [Field E] [Algebra ChartField E]

theorem generic_algebra_vertical :
    genericLineAlgebra (E:=E) true=Lower6960.Horner.rationalLaurentAlgebra (k:=Scalar) (E:=E) := by
  unfold genericLineAlgebra Lower6960.Horner.rationalLaurentAlgebra
  apply congrArg RingHom.toAlgebra
  apply RingHom.ext
  intro r
  exact congrArg (algebraMap ChartField E) (DFunLike.congr_fun (genericLaurent_coordinates true) r)

theorem generic_algebra_horizontal :
    genericLineAlgebra (E:=E) false=
      (((algebraMap ChartField E).comp swapBase.toRingHom).comp
        (Lower6960.Horner.rationalLaurent (k:=Scalar))).toAlgebra := by
  unfold genericLineAlgebra
  apply congrArg RingHom.toAlgebra
  apply RingHom.ext
  intro r
  exact congrArg (algebraMap ChartField E) (DFunLike.congr_fun (genericLaurent_coordinates false) r)

#print axioms generic_algebra_vertical
#print axioms generic_algebra_horizontal
end
end Lower6961.CollisionMarked
