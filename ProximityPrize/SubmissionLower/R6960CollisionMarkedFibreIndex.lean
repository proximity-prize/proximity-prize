import ProximityPrize.SubmissionLower.R6960CollisionMarkedFibreNormalization
import ProximityPrize.SubmissionLower.R6960CollisionTameDiscriminant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open Algebra Module Matrix Polynomial CollisionTame
open scoped Matrix Polynomial BigOperators

variable {A K B V : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing B] [Algebra A B] [CommRing V] [IsReduced V] [Algebra A V]
  [Algebra K V] [IsScalarTower A K V] [FiniteDimensional K V]

/-- A genuine finite free order in the reduced generic fibre has a
comparison determinant against its normalization. The determinant clears
every integral element, including the word idempotent, back into the
original order. -/
theorem reduced_fibre_index {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℕ) [CharP K p] (small : finrank K V<p)
    (φ : B→ₐ[A]V) (b : Basis I A B)
    (bk : Basis I K V) (induced : ∀ i,bk i=φ (b i)) :
    ∃ (n : Basis I A (integralClosure A V)) (D : Matrix I I A),
      D.det≠0 ∧ (traceMatrix A n).det≠0 ∧
      (∃ lift : B→ₐ[A]integralClosure A V,
        (∀ x,(lift x:V)=φ x) ∧ D=n.toMatrix (fun i=>lift (b i))) ∧
      traceMatrix A b=D.transpose*traceMatrix A n*D ∧
      (∀ v : V,IsIntegral A v→∃ u : B,φ u=algebraMap A V D.det*v) := by
  classical
  let N := integralClosure A V
  let : Module.Finite A B := Module.Finite.of_basis b
  let lift : B→ₐ[A]N := φ.codRestrict N (fun x=>(Algebra.IsIntegral.isIntegral x).map φ)
  obtain ⟨n0,nk0,h0⟩ := reduced_normalization_basis (A:=A) p small
  let t : Fin (finrank K V) ≃ I := (Fintype.equivFinOfCardEq (finrank_eq_card_basis bk).symm).symm
  let n := n0.reindex t
  let nk := nk0.reindex t
  have hn (i : I) : nk i=(n i:V) := by
    rw [show nk i=nk0 (t.symm i) from Basis.reindex_apply _ _ _,
      show n i=n0 (t.symm i) from Basis.reindex_apply _ _ _]
    exact h0 _
  let D : Matrix I I A := fun i j=>n.repr (lift (b j)) i
  let j := algebraMap A K
  have expand (i : I) : (∑ l,j (D l i) • nk l)=bk i := by
    calc
      _ = (↑(∑ l,D l i • n l : N):V) := by
        rw [show ((∑ l,D l i • n l : N):V)=∑ l,((D l i • n l : N):V) from map_sum N.val _ _]
        apply Finset.sum_congr rfl
        intro l _
        rw [hn,Subalgebra.coe_smul,IsScalarTower.algebraMap_smul]
      _ = (lift (b i):V) := congrArg Subtype.val (n.sum_repr (lift (b i)))
      _ = _ := (induced i).symm
  have ae : D.map j=nk.toMatrix bk := by
    apply Matrix.ext
    intro i l
    change j (D i l)=nk.repr (bk l) i
    rw [←expand l,nk.repr_sum_self]
  have an : (D.map j).det≠0 := by
    have h : (bk.toMatrix nk)*(D.map j)=1 := by rw [ae,Basis.toMatrix_mul_toMatrix_flip]
    exact Matrix.det_ne_zero_of_left_inverse h
  have dn : D.det≠0 := fun zero=>an (((RingHom.map_det j D).symm).trans (zero ▸ map_zero j))
  have map_b : (traceMatrix A b).map j=traceMatrix K bk :=
    trace_matrix_map_of_basis j b bk φ.toRingHom (fun a=>(φ.commutes a).trans (IsScalarTower.algebraMap_apply A K V a))
      (fun i=>(induced i).symm)
  have map_n : (traceMatrix A n).map j=traceMatrix K nk :=
    trace_matrix_map_of_basis j n nk N.val.toRingHom (fun a=>IsScalarTower.algebraMap_apply A K V a)
      (fun i=>(hn i).symm)
  have identity : traceMatrix A b=D.transpose*traceMatrix A n*D := by
    apply Matrix.map_injective (f:=j) (IsFractionRing.injective A K)
    have joined : (D.transpose*traceMatrix A n*D).map j =
        D.transpose.map j * (traceMatrix A n).map j * D.map j := by
      change j.mapMatrix (D.transpose*traceMatrix A n*D)=
        j.mapMatrix D.transpose * j.mapMatrix (traceMatrix A n) * j.mapMatrix D
      rw [map_mul,map_mul]
    change (traceMatrix A b).map j=(D.transpose*traceMatrix A n*D).map j
    rw [map_b,joined]
    have trans : D.transpose.map j=(D.map j).transpose := rfl
    change tupleGram (traceForm K V) bk=D.transpose.map j * (traceMatrix A n).map j * D.map j
    rw [trans,map_n]
    change tupleGram (traceForm K V) bk=(D.map j).transpose*tupleGram (traceForm K V) nk*(D.map j)
    rw [←tupleGram_change]
    exact congrArg (tupleGram (traceForm K V)) (funext fun i=>(expand i).symm)
  have nn : (traceMatrix A n).det≠0 := by
    have nd : (traceForm K V).Nondegenerate := by
      apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
      apply bot_unique
      intro x hx
      change x=0
      exact IsReduced.eq_zero x ((Lower6960.TraceSpecialization.trace_radical p small x).mp hx)
    have mat : traceMatrix K nk=(traceForm K V).toMatrix nk := by
      apply Matrix.ext
      intro i l
      rw [traceMatrix_apply,LinearMap.BilinForm.toMatrix_apply]
    intro zero
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero nk).mp nd
    rw [←mat,←map_n]
    change (j.mapMatrix (traceMatrix A n)).det = 0
    rw [←RingHom.map_det]
    exact zero ▸ map_zero j
  refine ⟨n,D,dn,nn,⟨lift,fun _=>rfl,rfl⟩,identity,?_⟩
  intro v hv
  let x : N := ⟨v,hv⟩
  let c := D.adjugate *ᵥ n.equivFun x
  let u := b.equivFun.symm c
  have ueq : u=∑ i,c i • b i := b.equivFun_symm_apply c
  have mapped : n.equivFun (lift u)=D*ᵥc := by
    rw [ueq,map_sum,map_sum]
    funext i
    simp only [Finset.sum_apply,Basis.equivFun_apply,Matrix.mulVec,dotProduct,D]
    apply Finset.sum_congr rfl
    intro l _
    have csmul : lift (c l • b l) = c l • lift (b l) := lift.toLinearMap.map_smul _ _
    rw [csmul,n.repr.map_smul,Finsupp.smul_apply,smul_eq_mul,mul_comm]
  have by_det : D*ᵥc=D.det • n.equivFun x := by
    change D*ᵥ(D.adjugate*ᵥn.equivFun x)=_
    rw [Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]
  have lift_eq : lift u=D.det • x := by
    apply n.equivFun.injective
    rw [mapped,by_det,n.equivFun.map_smul]
  refine ⟨u,?_⟩
  have h := congrArg Subtype.val lift_eq
  rw [Subalgebra.coe_smul] at h
  change φ u = (D.det:A) • v at h
  simpa only [Algebra.smul_def] using h

omit [IsPrincipalIdealRing A] [IsReduced V] in
/-- The marked projector is always integral over the base, independently
of whether it belongs to the original order. -/
theorem idempotent_integral (v : V) (idem : v^2=v) : IsIntegral A v := by
  refine ⟨Polynomial.X^2-Polynomial.X,monic_X_pow_sub (by rw [degree_X]; norm_num),?_⟩
  simp [idem]

#print axioms reduced_fibre_index
end
end Lower6960.CollisionMarked
