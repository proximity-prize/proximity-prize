import ProximityPrize.SubmissionLower.R6961CollisionMarkedGenericFrames
import ProximityPrize.SubmissionLower.R6960HornerNative
import ProximityPrize.SubmissionLower.R6961MarkedMatrixNorm
import ProximityPrize.SubmissionLower.R6961MarkedGenericRuling
import ProximityPrize.SubmissionLower.R6961MarkedZeroDegree
import ProximityPrize.SubmissionLower.R6961MarkedConstantDescent
import ProximityPrize.SubmissionLower.R6961CollisionMarkedGenericMeasure

set_option Elab.async false

-- merged module R6961CollisionMarkedGenericCoordinates
section Merged_R6961CollisionMarkedGenericCoordinates

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

end Merged_R6961CollisionMarkedGenericCoordinates

-- merged module R6961MarkedVerticalProfile
section Merged_R6961MarkedVerticalProfile
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 14000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Lower6960.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField Scalar)
open RetainedCompression (Curve ordinate view view_y height heightCap MarkedBand)
open RetainedRestrictionTorus RetainedSurfaceClass Lower6960.CollisionMarked Lower6961.CollisionMarked Polynomial Lower6960.LineEuler Algebra Module Submodule Lower6960.Horner
open scoped Polynomial BigOperators Lower6960.MarkedEvaluation Lower6961.MarkedEvaluation Lower6960.Horner Lower6961.RetainedSurfaceClass
local instance profileScalarDecidable : DecidableEq Scalar := Classical.decEq _
local instance profileFieldDecidable : DecidableEq ChartField := Classical.decEq _
local instance (priority:=2300) profileScalarBase : Algebra Scalar ChartField:=RatFunc.instAlgebraOfPolynomial Scalar Scalar
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
local instance profileNodeRing (x z:L) : CommRing (Crossing E x z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E false x⊔axisIdeal E true z)

/-- The vertical deficit of this precise surface is positive on the nonlinear
branch, is tame at the profile prime, and supplies the physical function rank. -/
theorem vertical_profile (B : MarkedBand) (f : Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<B.maxOrd)
    (bounded:height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree) (nonlin:¬RetainedLinear.GeometricallyLinear (view f))
    (b:PowerBasis ChartField E) (dim:b.dim=(view f).natDegree)
    (root:aeval b.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (small:finrank L (Crossing E x z)<K1.p) {n:ℕ}
    (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true))
    (s:ℕ) (measure:(transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ)) :
    0<s ∧ 2*s<K1.p ∧ ∀(U:Finset L)(m:ℕ)(v:Fin m→E),(∀j,controlled E (s-1) U (v j)) →
      finrank Scalar (span Scalar (Set.range v))+s≤(view f).natDegree*s := by
  classical
  let Q:=RetainedLinear.toSeed (view f)
  have e0:Q.natDegree=(view f).natDegree:=RetainedLinear.toSeed_degree _
  have e1:(view f).natDegree=f.degreeOf ordinate:=view_y f
  have rank:finrank ChartField E=(view f).natDegree:=b.finrank.trans dim
  have gen:=generic_measure_eq_native (E:=E) true x z nx nz K1.p small zf zi s measure
  dsimp only at gen
  rw [generic_algebra_vertical] at gen
  obtain ⟨F,I,det⟩:=gen
  have positive:0<s := by
    by_contra! h
    have zd:s=0:=by omega
    rw [zd,Nat.cast_zero,neg_zero,WithBot.coe_zero] at det
    obtain ⟨w,ind,integ⟩:=constant_frame F I det
    have pos:0<finrank ChartField E:=Module.finrank_pos
    letI:Nonempty (Fin (finrank ChartField E)):=⟨⟨0,pos⟩⟩
    exact nonlin (actual_geometric_of_constants (view f) ((MulEquiv.irreducible_iff view).mpr ir)
      (by omega) b root w ind (Fintype.card_fin _) integ)
  have width (j:ℕ):(Q.coeff j).natDegree≤heightCap (f.degreeOf ordinate) B.wordDegree := by
    have d:(Q.coeff j).natDegree=((view f).coeff j).natDegree:=by
      simp only [Q,RetainedLinear.toSeed,Polynomial.coe_mapRingHom,coeff_map,natDegree_map_eq_of_injective (RetainedLinear.incl_injective L)]
    rw [d]
    by_cases z:(view f).coeff j=0
    · rw [z,natDegree_zero];omega
    · exact (Nat.le_add_right _ _).trans ((RetainedCompression.abscissa_coeff_height f B.wordDegree j z).trans bounded)
  have hr (n':ℕ) (eq:n'=Q.natDegree)
      (F':Basis (Fin n') (Polynomial Scalar) (chartOrder (k:=Scalar) (E:=E) false))
      (I':Basis (Fin n') (Polynomial Scalar) (chartOrder (k:=Scalar) (E:=E) true))
      (dd:(normalizedTransition F' I').det.degree=((-(s:ℤ):ℤ):WithBot ℤ)) :
      s≤(Q.natDegree-1)*heightCap (f.degreeOf ordinate) B.wordDegree := by
    subst n'
    obtain ⟨d,dg,db⟩:=actual_horner_budget Q _ (by omega) width b.gen root
      (b.natDegree_minpoly.trans (dim.trans e0.symm)) F' I'
    have eq:d= -(s:ℤ):=WithBot.coe_injective (dg.symm.trans dd)
    rw [eq,neg_neg] at db
    exact_mod_cast db
  have cap:=hr _ (rank.trans e0.symm) F I det
  have tame:2*s<K1.p := by
    have h:2*((f.degreeOf ordinate-1)*heightCap (f.degreeOf ordinate) B.wordDegree)<K1.p := by
      exact B.vert _ hi lo
    rw [e0,e1] at cap;omega
  refine ⟨positive,tame,fun U m v regular=>?_⟩
  have bound:=actual_vertical_rank F I s positive det U m v regular
  rwa [Fintype.card_fin,rank] at bound

#print axioms vertical_profile
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedVerticalProfile
