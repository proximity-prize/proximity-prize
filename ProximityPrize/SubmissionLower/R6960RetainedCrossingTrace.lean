import ProximityPrize.SubmissionLower.R6960RetainedCrossingBasis
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedCrossingBasis
open Algebra Module Matrix
open scoped TensorProduct BigOperators
variable {A F E k ι : Type*} [CommRing A] [Field F] [Field E] [Field k]
  [Algebra A F] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [Algebra A k]
  [Fintype ι] [DecidableEq ι]

private theorem specialized_coordinates (b : Basis ι F E) (ib : ∀ i,IsIntegral A (b i))
    (B : Basis ι k (k ⊗[A] Order A E)) (val : ∀ i,B i=1 ⊗ₜ[A] (⟨b i,ib i⟩ : Order A E))
    (d : A) (x : Order A E) (c : ι→A)
    (coord : ∀ i, algebraMap A F (c i)=algebraMap A F d*b.repr (x:E) i) (i : ι) :
    algebraMap A k d * B.repr (1 ⊗ₜ[A] x) i=algebraMap A k (c i) := by
  let v (i:ι) : Order A E := ⟨b i,ib i⟩
  have before : d • x=∑ i,c i • v i := by
    apply Subtype.ext
    change d • (x:E)=_
    push_cast
    rw [←IsScalarTower.algebraMap_smul F d (x:E)]
    calc _ = ∑ i,(algebraMap A F d*b.repr (x:E) i) • b i := by
               simp only [mul_smul,←Finset.smul_sum,b.sum_repr]
         _ = _ := by
               apply Finset.sum_congr rfl
               intro j _
               rw [←coord,algebraMap_smul]
  have after : algebraMap A k d • (1 ⊗ₜ[A] x) = ∑ j, algebraMap A k (c j) • B j := by
    simpa only [TensorProduct.tmul_sum,TensorProduct.tmul_smul,algebraMap_smul,val,v] using
      congrArg (fun y : Order A E => (1:k) ⊗ₜ[A] y) before
  simpa only [B.repr_self,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,
    ite_true] using congrArg (fun y => B.repr y i) after

theorem specialize_trace [IsDomain A] [IsFractionRing A F]
    (b : Basis ι F E) (ib : ∀ i,IsIntegral A (b i))
    (B : Basis ι k (k ⊗[A] Order A E)) (val : ∀ i,B i=1 ⊗ₜ[A] (⟨b i,ib i⟩ : Order A E))
    (d : A) (dn : algebraMap A k d≠0)
    (coords : ∀ x : Order A E, ∀ j, ∃ c : A,algebraMap A F c=algebraMap A F d*b.repr (x:E) j)
    (x : Order A E) (t : A) (ht : algebraMap A F t=trace F E x.val) :
    algebraMap A k t=trace k (k ⊗[A] Order A E) (1 ⊗ₜ[A] x) := by
  let v (i:ι) : Order A E := ⟨b i,ib i⟩
  choose C hc using fun i j=>coords (x*v i) j
  have before : d*t=∑ i,C i i := by
    apply IsFractionRing.injective A F
    rw [map_mul,ht,trace_eq_matrix_trace b,Matrix.trace,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Matrix.diag,Algebra.leftMulMatrix_eq_repr_mul,Subalgebra.coe_mul,v] using (hc i i).symm
  apply mul_left_cancel₀ dn
  rw [←map_mul,before,map_sum,trace_eq_matrix_trace B,Matrix.trace,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag,Algebra.leftMulMatrix_eq_repr_mul]
  change algebraMap A k (C i i)=algebraMap A k d*B.repr ((1 ⊗ₜ[A] x)*B i) i
  rw [val,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  exact (specialized_coordinates b ib B val d (x*v i) (C i) (hc i) i).symm

#print axioms specialize_trace
end Lower6960.RetainedCrossingBasis
