import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.RingTheory.AdjoinRoot

set_option Elab.async false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.LineEuler
noncomputable section
open Polynomial Module Submodule
open scoped Polynomial BigOperators

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- For a square polynomial matrix of nonzero determinant, its cokernel
has finite dimension over the coefficient field, equal to the degree of
the determinant. -/
theorem polynomial_cokernel (A : Matrix ι ι k[X]) (nonzero : A.det≠0) :
    FiniteDimensional k ((ι→k[X]) ⧸ LinearMap.range (Matrix.toLin' A)) ∧
    Module.finrank k ((ι→k[X]) ⧸ LinearMap.range (Matrix.toLin' A)) = A.det.natDegree := by
  let f := Matrix.toLin' A
  let N := LinearMap.range f
  have inj : Function.Injective f :=
    Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_ne_zero.mpr nonzero)
  let e : (ι→k[X]) ≃ₗ[k[X]] N := LinearEquiv.ofInjective f inj
  have rank : Module.finrank k[X] N = Module.finrank k[X] (ι→k[X]) := e.finrank_eq.symm
  let b := Pi.basisFun k[X] ι
  let top := smithNormalFormTopBasis b rank
  let bot := smithNormalFormBotBasis b rank
  let a := smithNormalFormCoeffs b rank
  have anz (i : ι) : a i≠0 := smithNormalFormCoeffs_ne_zero b rank i
  let e' : (ι→k[X]) ≃ₗ[k[X]] N := top.equiv bot (Equiv.refl ι)
  let g : (ι→k[X]) →ₗ[k[X]] (ι→k[X]) := N.subtype ∘ₗ e'.toLinearMap
  have comp : N.subtype ∘ₗ e.toLinearMap = f := by ext x; rfl
  have asso := LinearMap.associated_det_comp_equiv N.subtype e e'
  rw [comp] at asso
  change Associated (LinearMap.det f) (LinearMap.det g) at asso
  have mat : LinearMap.toMatrix top top g = Matrix.diagonal a := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply]
    change top.repr (↑(e' (top j)) : ι→k[X]) i = _
    have ej : (↑(e' (top j)) : ι→k[X])=a j • top j := calc
      _ = ↑(bot j) := congrArg Subtype.val (Basis.equiv_apply (b:=top) (b':=bot) (e:=Equiv.refl ι) (i:=j))
      _ = _ := smithNormalFormBotBasis_def b rank j
    rw [ej,top.repr.map_smul,Finsupp.smul_apply,Basis.repr_self,Matrix.diagonal_apply]
    by_cases same : j=i
    · subst i
      simp only [Finsupp.single_eq_same,smul_eq_mul,mul_one,ite_true]
    · rw [Finsupp.single_eq_of_ne (Ne.symm same),smul_zero]
      simp only [Ne.symm same,ite_false]
  rw [LinearMap.det_toLin',←LinearMap.det_toMatrix top,mat,Matrix.det_diagonal] at asso
  let : ∀ i, FiniteDimensional k (k[X] ⧸ Ideal.span ({a i} : Set k[X])) :=
    fun i=>(AdjoinRoot.powerBasis (anz i)).finite
  let dec := N.quotientEquivPiSpan b rank
  have finite : FiniteDimensional k ((ι→k[X]) ⧸ N) :=
    FiniteDimensional.of_injective (dec.restrictScalars k).toLinearMap dec.injective
  refine ⟨finite,?_⟩
  calc
    Module.finrank k ((ι→k[X]) ⧸ N) = ∑ i, Module.finrank k (k[X] ⧸ Ideal.span ({a i} : Set k[X])) :=
      Submodule.finrank_quotient_eq_sum k b rank
    _ = ∑ i, (a i).natDegree := Finset.sum_congr rfl fun i _=>(AdjoinRoot.powerBasis (anz i)).finrank
    _ = (∏ i,a i).natDegree := (natDegree_prod _ _ (fun i _=>anz i)).symm
    _ = A.det.natDegree := (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated asso)).symm

#print axioms polynomial_cokernel
end
end Lower6960.LineEuler
