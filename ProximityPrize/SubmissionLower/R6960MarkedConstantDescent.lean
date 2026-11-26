import ProximityPrize.SubmissionLower.R6960MarkedNativeNorm
import ProximityPrize.SubmissionLower.R6960MonicChartActual

set_option Elab.async false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1650000
namespace Lower6960.MarkedEvaluation
open Polynomial Algebra Module Finset
open scoped Polynomial BigOperators
theorem splits_of_constant_basis {k F A H E I:Type} [Field k] [Field F] [Field A] [Field H]
    [Field E] [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E] [IsAlgClosed A] [Fintype I]
    (j:F→+*H) (t:k→+*A) (n:A→+*H) (co:∀a,j (algebraMap k F a)=n (t a))
    (q:(Polynomial F)) (ir:Irreducible q) (b:PowerBasis F E) (root:aeval b.gen q=0)
    (w:Basis I F E) (ints:∀i,IsIntegral k (w i)) : (q.map j).Splits := by
  classical
  let p:=q.map j
  let Ω:=p.SplittingField
  let inc:=algebraMap H Ω
  let h:=inc.comp j
  letI : Algebra F Ω:=h.toAlgebra
  apply Polynomial.Splits.of_splits_map_of_injective inc.injective (SplittingField.splits p)
  intro r hr
  have qr:(q.map j).eval₂ inc r=0 := by
    have hroot:=(Polynomial.mem_roots'.mp hr).2
    rwa [Polynomial.IsRoot,Polynomial.eval_map] at hroot
  have py:q.eval₂ h r=0 := by rwa [eval₂_map] at qr
  have sm : aeval r (minpoly F b.gen)=0 := by
    rw [←minpoly.eq_of_irreducible ir root,aeval_def,eval₂_mul]
    exact mul_eq_zero_of_left py _
  let ψ:=b.lift r sm
  have cf: (inc.comp n).comp t=ψ.toRingHom.comp (algebraMap k E) := by
    ext a
    change inc (n (t a))=ψ (algebraMap k E a)
    rw [IsScalarTower.algebraMap_apply k F E,ψ.commutes,←co];rfl
  have member (i:I):ψ (w i)∈inc.range := by
    obtain ⟨u,um,uz⟩:=ints i
    have rt : ((u.map t).map (inc.comp n)).IsRoot (ψ (w i)) := by
      rw [Polynomial.IsRoot,Polynomial.eval_map,eval₂_map,cf]
      exact (Polynomial.hom_eval₂ u (algebraMap k E) ψ.toRingHom (w i)).symm.trans
        ((congrArg ψ.toRingHom uz).trans (map_zero _))
    obtain ⟨a,eq⟩:=(IsAlgClosed.splits (u.map t)).mem_range_of_isRoot ((um.map _).ne_zero) rt
    exact ⟨n a,eq⟩
  rw [←b.lift_gen r sm,←w.sum_repr b.gen,map_sum]
  apply inc.range.sum_mem;intro i _
  rw [Algebra.smul_def,map_mul,ψ.commutes]
  exact inc.range.mul_mem ⟨j (w.repr b.gen i),rfl⟩ (member i)
open K1_14 (L)
open MonicChart (Scalar ChartField)
open RetainedLinear (Fn Seed toSeed GeometricallyLinear)
open RetainedCompression (view ordinate Curve)
open scoped Lower6960.MarkedEvaluation
local instance (priority:=2200) descentScalarBase : Algebra Scalar ChartField:=RatFunc.instAlgebraOfPolynomial Scalar Scalar
def genericToFraction : ChartField≃+*Fn Scalar:=(IsLocalization.algEquiv (nonZeroDivisors (Polynomial Scalar)) ChartField (Fn Scalar)).toRingEquiv
theorem actual_geometric_of_constants {E I:Type} [Field E] [Algebra ChartField E] [Fintype I] [Nonempty I]
    (P:CurvatureSquares.Ordinate) (ir:Irreducible P) (pos:0<P.natDegree) (b:PowerBasis ChartField E)
    (root:aeval b.gen ((toSeed P).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (w:I→E) (li:LinearIndependent ChartField w) (size:Fintype.card I=finrank ChartField E)
    (ints:∀i,IsIntegral Scalar (w i)) : GeometricallyLinear P := by
  let A:=AlgebraicClosure Scalar
  let c:=RetainedLinear.rationalConstants (F:=Scalar) (E:=A)
  let j:=c.comp genericToFraction.toRingHom
  let n: A→+*Fn A:=(RetainedLinear.incl A).comp Polynomial.C
  let B:=basisOfLinearIndependentOfCardEqFinrank li size
  have bEq (i:I):B i=w i:=congrFun (coe_basisOfLinearIndependentOfCardEqFinrank li size) i
  have fieldMap (p:(Polynomial Scalar)):genericToFraction (algebraMap (Polynomial Scalar) ChartField p)=RetainedLinear.incl Scalar p :=
    (IsLocalization.algEquiv (nonZeroDivisors (Polynomial Scalar)) ChartField (Fn Scalar)).commutes p
  have mapEq:j.comp (algebraMap (Polynomial Scalar) ChartField)=RetainedLinear.base (F:=Scalar) (E:=A) := by
    apply RingHom.ext;intro p
    change c (genericToFraction ((algebraMap (Polynomial Scalar) ChartField) p))=_
    rw [fieldMap];exact RetainedLinear.rationalConstants_incl p
  have co (a:Scalar):j (algebraMap Scalar ChartField a)=n (algebraMap Scalar A a) := by
    change j (RatFunc.C a)=_
    rw [←RatFunc.algebraMap_C]
    have eq:=DFunLike.congr_fun mapEq (Polynomial.C a)
    exact eq.trans (congrArg (RetainedLinear.incl A) (Polynomial.map_C (algebraMap Scalar A)))
  have pi:=RetainedLinear.toSeed_irreducible ir pos
  have qp:Irreducible ((toSeed P).map (algebraMap (Polynomial Scalar) ChartField)) :=
    (pi.isPrimitive (by rw [RetainedLinear.toSeed_degree];omega)).irreducible_iff_irreducible_map_fraction_map.mp pi
  have split:=splits_of_constant_basis j (algebraMap Scalar A) n co _ qp b root B (fun i=>bEq i ▸ ints i)
  rw [Polynomial.map_map,mapEq] at split
  exact split
end Lower6960.MarkedEvaluation
