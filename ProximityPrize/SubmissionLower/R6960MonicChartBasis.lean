import ProximityPrize.SubmissionLower.R6960MonicChartReverse
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2200000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial

section Basis

variable {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E]

abbrev reciprocal (b : PowerBasis F E) (c : A) : E :=
  (b.gen-algebraMap A E c)⁻¹

private theorem reciprocal_generates (b : PowerBasis F E) (c : A) :
    IntermediateField.adjoin F ({reciprocal b c} : Set E)=⊤ := by
  let K := IntermediateField.adjoin F ({reciprocal b c} : Set E)
  have rb : reciprocal b c∈K := IntermediateField.subset_adjoin F _ (Set.mem_singleton _)
  have off : algebraMap A E c∈K := by
    rw [IsScalarTower.algebraMap_apply A F E]
    exact K.algebraMap_mem _
  have eq : (reciprocal b c)⁻¹+algebraMap A E c=b.gen := by
    simp [reciprocal]
  have gen : b.gen∈K := eq ▸ K.add_mem (K.inv_mem rb) off
  have le : Algebra.adjoin F ({b.gen} : Set E) ≤ K.toSubalgebra := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact gen
  rw [b.adjoin_gen_eq_top] at le
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.top_toSubalgebra]
  exact le_antisymm le_top le

/-- The reciprocal generator gives a power basis for the original root
field, with the transformed integral equation as its minimal polynomial. -/
theorem chart_basis (b : PowerBasis F E) (f : A[X]) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) (degree : f.natDegree=b.dim) (root : aeval b.gen f=0) :
    ∃ v : PowerBasis F E, v.gen=reciprocal b c ∧
      IsIntegral A v.gen ∧ minpoly A v.gen=equation f c u := by
  let s := IntermediateField.adjoin F ({reciprocal b c} : Set E)
  let β := reciprocal b c
  have root' : aeval β (equation f c u)=0 :=
    equation_root (algebraMap A E) f c u hu root
  have monic := equation_monic f c u hu
  have hA : IsIntegral A β := ⟨equation f c u,monic,root'⟩
  letI : FiniteDimensional F E := b.finite
  let e : s ≃ₐ[F] E :=
    (IntermediateField.equivOfEq (reciprocal_generates b c)).trans IntermediateField.topEquiv
  let v : PowerBasis F E :=
    (IntermediateField.adjoin.powerBasis (K:=F) (x:=β) (Algebra.IsIntegral.isIntegral β)).map e
  have vg : v.gen=β := rfl
  have integ : IsIntegral A v.gen := vg.symm ▸ hA
  have dimension : v.dim=b.dim := v.finrank.symm.trans b.finrank
  let j := algebraMap A F
  have ji : Function.Injective j := IsFractionRing.injective _ _
  let g := (equation f c u).map j
  have gm : g.Monic := monic.map j
  have rootF : aeval v.gen g=0 := by
    rw [aeval_map_algebraMap,vg]
    exact root'
  have gdeg : g.natDegree=v.dim := by
    rw [natDegree_map_eq_of_injective ji,equation_degree f c u hu,degree,dimension]
  have equal : g=minpoly F v.gen := by
    apply minpoly.unique_of_degree_le_degree_minpoly F v.gen gm rootF
    rw [degree_eq_natDegree gm.ne_zero,degree_eq_natDegree (minpoly.ne_zero v.isIntegral_gen),
      gdeg,v.natDegree_minpoly]
  refine ⟨v,vg,integ,?_⟩
  apply Polynomial.map_injective _ ji
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' F integ]
  exact equal.symm

theorem original_equation (b : PowerBasis F E) (f : A[X])
    (degree : f.natDegree=b.dim) (positive : 0<f.natDegree) (root : aeval b.gen f=0) :
    f.map (algebraMap A F)=C (algebraMap A F f.leadingCoeff)*minpoly F b.gen := by
  let j := algebraMap A F
  have ji : Function.Injective j := IsFractionRing.injective _ _
  have positive' : f≠0 := by rintro rfl; simp at positive
  let P := f.map j
  let l := j f.leadingCoeff
  have ln : l≠0 := (map_ne_zero_iff _ ji).mpr (leadingCoeff_ne_zero.mpr positive')
  let g := C l⁻¹*P
  have monic : g.Monic := by
    unfold Monic g P
    rw [leadingCoeff_mul,leadingCoeff_C,leadingCoeff_map_of_injective ji]
    exact inv_mul_cancel₀ ln
  have rooted : aeval b.gen g=0 := by
    rw [map_mul,show P=f.map j from rfl,aeval_map_algebraMap,root,mul_zero]
  have gdeg : g.natDegree=b.dim := by
    rw [natDegree_C_mul (inv_ne_zero ln),natDegree_map_eq_of_injective ji,degree]
  have minimal : g=minpoly F b.gen := by
    apply minpoly.unique_of_degree_le_degree_minpoly F b.gen monic rooted
    rw [degree_eq_natDegree monic.ne_zero,degree_eq_natDegree (minpoly.ne_zero b.isIntegral_gen),
      gdeg,b.natDegree_minpoly]
  rw [← minimal]
  change P=C l*(C l⁻¹*P)
  rw [← mul_assoc,← C_mul,mul_inv_cancel₀ ln,C_1,one_mul]

#print axioms chart_basis
end Basis
end
end Lower6960.MonicChart
