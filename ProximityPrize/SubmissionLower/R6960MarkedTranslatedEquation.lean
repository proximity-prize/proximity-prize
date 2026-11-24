import ProximityPrize.SubmissionLower.R6960MarkedScalarAxis
import ProximityPrize.SubmissionLower.R6960CollisionMarkedProjected
import ProximityPrize.SubmissionLower.R6960RetainedAxisCharts
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open MonicFourChartDescent RetainedSurfaceClass NormalizedFiber CollisionMarked Polynomial Algebra
open scoped Polynomial Lower6960.MonicChart
open Lower6960.RetainedSurfaceClass (oriented_var oriented_const oriented_line)

def translatedX (c:L) : (Polynomial L)→+*Scalar := (translateField Scalar c).toRingHom.comp (algebraMap (Polynomial L) Scalar)
def rowPlane (c:L) : Plane L→+*(Polynomial Scalar) := eval₂RingHom (C.comp (translatedX c)) Polynomial.X
local notation "fp" => algebraMap (Polynomial Scalar) ChartField

private theorem translatedX_const (c a:L) : translatedX c (C a)=inner a := by
  change translateField Scalar c (algebraMap (Polynomial L) Scalar (C a))=_
  rw [translate_polynomial,taylor_C];rfl
private theorem translatedX_var (c:L) : translatedX c Polynomial.X=algebraMap (Polynomial L) Scalar Polynomial.X+inner c := by
  change translateField Scalar c (algebraMap (Polynomial L) Scalar Polynomial.X)=_
  rw [translate_polynomial,taylor_X,map_add];rfl

/-- Every original coefficient becomes a polynomial in the scalar variable
after translating its physical abscissa and exchanging the axes. -/
theorem row_plane (c:L) (p:Plane L) :
    rowBase c ((oriented true false p):ChartField)=fp (rowPlane c p) := by
  let f:Plane L→+*ChartField:= (rowBase c).toRingHom.comp ((baseChart _).subtype.comp (oriented true false).toRingHom)
  let g:Plane L→+*ChartField:=(algebraMap (Polynomial Scalar) ChartField).comp (rowPlane c)
  have eq:f=g := by
    apply Polynomial.ringHom_ext
    · intro v
      have innerEq:f.comp C=g.comp C := by
        apply Polynomial.ringHom_ext
        · intro a
          change rowBase c ((oriented true false (C (C a))):ChartField)=fp ((C (C a)).eval₂ (C.comp (translatedX c)) Polynomial.X)
          rw [Lower6960.RetainedSurfaceClass.oriented_const,row_constant,eval₂_C,RingHom.comp_apply,translatedX_const,RatFunc.algebraMap_C];rfl
        · change rowBase c ((oriented true false (C Polynomial.X)):ChartField)=fp ((C Polynomial.X).eval₂ (C.comp (translatedX c)) Polynomial.X)
          rw [Lower6960.RetainedSurfaceClass.oriented_line,eval₂_C,RingHom.comp_apply,translatedX_var,RatFunc.algebraMap_C,map_add]
          exact row_abscissa c
      exact DFunLike.congr_fun innerEq v
    · change rowBase c ((oriented true false Polynomial.X):ChartField)=fp (Polynomial.X.eval₂ (C.comp (translatedX c)) Polynomial.X)
      rw [Lower6960.RetainedSurfaceClass.oriented_var,eval₂_X,RatFunc.algebraMap_X];exact row_parameter c
  exact DFunLike.congr_fun eq p

theorem row_specialization (c z:L) :
    (evalRingHom (inner z)).comp (rowPlane c)=(translateField Scalar c).toRingHom.comp (genericFibreBase z) := by
  apply Polynomial.ringHom_ext
  · intro v
    change ((C v).eval₂ (C.comp (translatedX c)) Polynomial.X).eval (inner z)=
      translateField Scalar c (algebraMap (Polynomial L) Scalar ((C v).eval (C z)))
    rw [eval₂_C,RingHom.comp_apply,eval_C,eval_C];rfl
  · change (Polynomial.X.eval₂ (C.comp (translatedX c)) Polynomial.X).eval (inner z)=
      translateField Scalar c (algebraMap (Polynomial L) Scalar (Polynomial.X.eval (C z)))
    rw [eval₂_X,eval_X,eval_X];exact (translatedX_const c z).symm

theorem normalized_fibre_separable (z:L) (P:CurvatureSquares.Ordinate) (S:(Polynomial L))
    (p:ℕ) [CharP Scalar p] (lo:0<P.natDegree) (hi:P.natDegree<p)
    (mark:RetainedCompression.MarkedFiber P z S) :
    ((projectedRaw P).integralNormalization.map (genericFibreBase z)).Separable := by
  let raw:=projectedRaw P
  let J:=genericFibreBase z
  have full:(raw.map J).natDegree=raw.natDegree := by
    rw [show raw.map J= _ from projectedRaw_fibre P z,natDegree_map_eq_of_injective (IsFractionRing.injective _ _),mark.full,projectedRaw_degree]
  have nz:J raw.leadingCoeff≠0 := fun bad=>(natDegree_map_lt' bad (projectedRaw_degree P ▸ lo)).ne full
  have base:(raw.map J).Separable := projectedRaw_fibre P z ▸ mark.separable
  rw [←integralNormalization_map J raw nz]
  apply integralNormalization_separable p _ _ _ base <;> rwa [full,projectedRaw_degree]

theorem marked_row_separable (c z:L) (P:CurvatureSquares.Ordinate) (S:(Polynomial L))
    (p:ℕ) [CharP Scalar p] (lo:0<P.natDegree) (hi:P.natDegree<p) (mark:RetainedCompression.MarkedFiber P z S) :
    ((((projectedRaw P).integralNormalization.map (rowPlane c)).map (evalRingHom (inner z)))).Separable := by
  rw [Polynomial.map_map,row_specialization,←Polynomial.map_map]
  exact (normalized_fibre_separable z P S p lo hi mark).map

/-- The horizontal embedding preserves the degree of the actual scaled
ordinate, including its arbitrary nonzero leading-coefficient multiplier. -/
theorem scaled_row_degree {F E Ω:Type} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω]
    (b:PowerBasis F E) (σ:F≃+*F) (ev:E→+*Ω)
    (base:∀a,ev (algebraMap F E a)=algebraMap F Ω (σ a)) (a:F) (nz:a≠0) :
    (minpoly F (ev (algebraMap F E a*b.gen))).natDegree=b.dim := by
  let q:=minpoly F b.gen
  let Q:=q.map σ.toRingHom
  have mon:Q.Monic:=(minpoly.monic b.isIntegral_gen).map _
  have irr:Irreducible Q:=(MulEquiv.irreducible_iff (Polynomial.mapEquiv σ)).mpr (minpoly.irreducible b.isIntegral_gen)
  have h:(algebraMap F Ω).comp σ.toRingHom=ev.comp (algebraMap F E) := RingHom.ext (fun r=>(base r).symm)
  have zero:aeval (ev b.gen) Q=0 := by
    rw [aeval_def,show Q=q.map σ.toRingHom from rfl,eval₂_map,h,←Polynomial.hom_eval₂]
    exact (congrArg ev (minpoly.aeval F b.gen)).trans (map_zero _)
  have eq:=minpoly.eq_of_irreducible_of_monic irr zero mon
  rw [map_mul,base,←Algebra.smul_def,IsIntegrallyClosed.minpoly_smul ((map_ne_zero_iff _ σ.injective).mpr nz)
    (show IsIntegral F (ev b.gen) from ⟨Q,mon,zero⟩),natDegree_scaleRoots,←eq,
    show Q=q.map σ.toRingHom from rfl,natDegree_map_eq_of_injective σ.injective,b.natDegree_minpoly]

#print axioms row_plane
#print axioms marked_row_separable
#print axioms scaled_row_degree
end Lower6960.MarkedEvaluation
