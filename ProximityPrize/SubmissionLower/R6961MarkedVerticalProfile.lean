import ProximityPrize.SubmissionLower.R6961MarkedGenericRuling
import ProximityPrize.SubmissionLower.R6961MarkedZeroDegree
import ProximityPrize.SubmissionLower.R6961MarkedConstantDescent
import ProximityPrize.SubmissionLower.R6961CollisionMarkedGenericMeasure
import ProximityPrize.SubmissionLower.R6961CollisionMarkedGenericCoordinates
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
