import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import ProximityPrize.SubmissionLower.R6961MonicChartFinite
import Mathlib.LinearAlgebra.Basis.SMul

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 3600000

namespace Lower6961.MonicChart
open Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial Differential

private def scaleBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (b : PowerBasis F E) (u : Fˣ) : PowerBasis F E where
  gen := algebraMap F E (u:F)*b.gen
  dim := b.dim
  basis := b.basis.unitsSMul (fun j=>u^j.val)
  basis_eq_pow j := by
    rw [Module.Basis.unitsSMul_apply,Units.smul_def,Units.val_pow_eq_pow_val,b.basis_eq_pow,
      Algebra.smul_def,map_pow,mul_pow]

section Infinity

variable {K E : Type*} [Field K] [Infinite K] [DecidableEq (RatFunc K)]
    [Field E] [Algebra (RatFunc K) E] [Algebra (Polynomial K) E]
    [IsScalarTower (Polynomial K) (RatFunc K) E]
    [Algebra (Infinity K) E] [IsScalarTower (Infinity K) (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Differential (Infinity K)] [Differential E] [DifferentialAlgebra (Infinity K) E]

local notation "S" => Infinity K
local notation "F" => RatFunc K

private theorem primitive_unit_infty (p : (Polynomial (Polynomial K))) (prim : p.IsPrimitive) :
    ∃ i, IsUnit ((p.map (inftyRingEval K)).coeff i) := by
  by_contra! no
  have dvd : C (Polynomial.X : (Polynomial K))∣p := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro j
    apply X_dvd_iff.mpr
    by_contra nz
    exact no j (by rw [coeff_map]; exact inftyRingEval_isUnit _ nz)
  exact not_isUnit_X ((isPrimitive_iff_isUnit_of_C_dvd.mp prim) _ dvd)

/-- The weighted infinity chart controls derivatives by its own padded
resultant. Primitive part is taken before choosing the monic chart, and
its content factor is returned to the resultant. -/
theorem clears_homogeneous_infinity (b : PowerBasis F E) (f : (Polynomial (Polynomial K))) (H d : ℕ)
    (e2 : 2≤f.natDegree) (dim : f.natDegree=b.dim)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (root : aeval b.gen f=0) (x : E) (hx : IsIntegral S x) :
    IsIntegral S (algebraMap S E ((inftyRingEval K (paddedRes (weightedInfinity f H d)))^2)*x′) := by
  classical
  letI : NormalizedGCDMonoid (Polynomial K) := Classical.choice inferInstance
  let e := f.natDegree
  let t := ((RatFunc.X : F)⁻¹)
  let a := t^d
  have an : a≠0 := pow_ne_zero _ (inv_ne_zero RatFunc.X_ne_zero)
  let v := scaleBasis b (Units.mk0 a an)
  have vg : v.gen=algebraMap F E a*b.gen := rfl
  have vd : v.dim=b.dim := rfl
  let fI := weightedInfinity f H d
  let j := inftyRingEval K
  let r := fI.map j
  let p := fI.primPart.map j
  let c := j fI.content
  let ι := algebraMap S F
  have rdegree : r.natDegree=e := (natDegree_map_eq_of_injective inftyRingEval_injective _).trans
    (infinity_degree f H d)
  have pdegree : p.natDegree=e := by
    rw [natDegree_map_eq_of_injective inftyRingEval_injective,natDegree_primPart,infinity_degree]
  have rawSplit : r=C c*p := by
    have eq := congrArg (Polynomial.map j) fI.eq_C_content_mul_primPart
    simpa only [Polynomial.map_mul,Polynomial.map_C] using eq
  have cn : c≠0 := by
    intro zero
    rw [rawSplit,zero,C_0,zero_mul,natDegree_zero] at rdegree
    omega
  have mapped_r : r.map ι=fI.map (AtInfinity K) := by
    rw [Polynomial.map_map]
    rfl
  have rroot : aeval v.gen r=0 := by
    rw [← aeval_map_algebraMap F,mapped_r,infinity_field f H d weights,map_mul]
    have baseRoot : aeval b.gen (f.map (algebraMap (Polynomial K) F))=0 := by
      rw [aeval_map_algebraMap]
      exact root
    have newRoot : aeval v.gen ((f.map (algebraMap (Polynomial K) F)).scaleRoots a)=0 := by
      rw [vg]
      exact scaleRoots_eval₂_eq_zero (algebraMap F E) baseRoot
    rw [newRoot,mul_zero]
  have proot : aeval v.gen p=0 := by
    rw [rawSplit,map_mul,aeval_C] at rroot
    have injective : Function.Injective (algebraMap S E) := by
      rw [IsScalarTower.algebraMap_eq S F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective _ _)
    exact (mul_eq_zero.mp rroot).resolve_left ((map_ne_zero_iff _ injective).mpr cn)
  let emb : K→+*IsLocalRing.ResidueField S := (IsLocalRing.residue S).comp (j.comp C)
  letI : Infinite (IsLocalRing.ResidueField S) := Infinite.of_injective emb emb.injective
  have unit : ∃ i, IsUnit (p.coeff i) := primitive_unit_infty _ fI.isPrimitive_primPart
  have bounded := raw_square_clears_local v p unit (pdegree.trans (dim.trans vd.symm))
    (pdegree.symm ▸ e2) proot x hx
  have mapped_result : j (paddedRes fI)=paddedRes r := by
    unfold paddedRes
    rw [←resultant_map_map,←derivative_map]
    have d := natDegree_map_eq_of_injective inftyRingEval_injective fI
    rw [←d]
  have content_result : paddedRes r=c^(e+(e-1))*paddedRes p := by
    unfold paddedRes
    rw [rdegree,rawSplit,derivative_C_mul,resultant_C_mul_left,resultant_C_mul_right,←mul_assoc,←pow_add]
    rw [show e-1+e=e+(e-1) by omega,←pdegree]
  rw [mapped_result,content_result,mul_pow,map_mul,mul_assoc]
  exact isIntegral_algebraMap.mul bounded

end Infinity

#print axioms clears_homogeneous_infinity
end
end Lower6961.MonicChart
