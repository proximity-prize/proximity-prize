import ProximityPrize.SubmissionLower.R6960CollisionMarkedMonicTrace
import Mathlib.LinearAlgebra.Matrix.BilinearForm

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial Algebra Module
open scoped Polynomial TensorProduct

section Specialized
variable {A K : Type*} [CommRing A] [Field K]

/-- A separable ordinate quotient has no nilpotents, including when the
polynomial has more than one irreducible factor. -/
theorem separable_adjoinRoot_reduced (q : (Polynomial K)) (sep : q.Separable) : IsReduced (AdjoinRoot q) := by
  constructor
  intro x h
  induction x using AdjoinRoot.induction_on with
  | _ r =>
    obtain ⟨n,hn⟩ := h
    by_cases nn : n=0
    · have one0 : (1:AdjoinRoot q)=0 := by simpa only [nn,pow_zero] using hn
      calc AdjoinRoot.mk q r = 1*AdjoinRoot.mk q r := (one_mul _).symm
        _ = 0 := by rw [one0,zero_mul]
    · have qr : q∣r^n := AdjoinRoot.mk_eq_zero.mp (by rw [map_pow]; exact hn)
      exact AdjoinRoot.mk_eq_zero.mpr ((sep.squarefree.dvd_pow_iff_dvd nn).mp qr)

/-- A separable specialized monic equation has nonzero power-basis
trace discriminant in characteristic larger than its degree, even when
the quotient is a product. -/
theorem monic_disc_nonzero_at {f : (Polynomial A)} (hf : f.Monic) (j : A→+*K)
    (p : ℕ) [CharP K p] (small : f.natDegree<p) (sep : (f.map j).Separable) :
    j (monicDisc hf)≠0 := by
  let q := f.map j
  have hq : q.Monic := hf.map j
  have deg : q.natDegree=f.natDegree := hf.natDegree_map j
  let v := AdjoinRoot.powerBasis' hq
  let b : Basis (Fin f.natDegree) K (AdjoinRoot q) := v.basis.reindex (finCongr deg)
  have pw (i : Fin f.natDegree) : b i=AdjoinRoot.root q^(i:ℕ) := by
    rw [show b i=v.basis ((finCongr deg).symm i) from Basis.reindex_apply _ _ _,v.basis_eq_pow]
    rfl
  have root : aeval (AdjoinRoot.root q) q=0 := by rw [AdjoinRoot.aeval_eq,AdjoinRoot.mk_self]
  have identity : j (monicDisc hf)=Algebra.discr K b := monic_disc_of_basis hf j _ root b pw
  rw [identity,Algebra.discr_def]
  let : FiniteDimensional K (AdjoinRoot q) := Module.Finite.of_basis b
  have dims : finrank K (AdjoinRoot q)<p := (finrank_eq_card_basis b).trans_lt (by simpa using small)
  let : IsReduced (AdjoinRoot q) := separable_adjoinRoot_reduced q sep
  have nd : (Algebra.traceForm K (AdjoinRoot q)).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    apply bot_unique
    intro x hx
    change x=0
    exact IsReduced.eq_zero x ((Lower6960.TraceSpecialization.trace_radical p dims x).mp hx)
  have mat : Algebra.traceMatrix K b=(Algebra.traceForm K (AdjoinRoot q)).toMatrix b := by
    apply Matrix.ext
    intro i j
    rw [Algebra.traceMatrix_apply,LinearMap.BilinForm.toMatrix_apply]
  rw [mat]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp nd
end Specialized

section Fibre
variable {A F E K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [FiniteDimensional F E]
  [Field K]

/-- Specialize the original integral closure at the selected field map.
At a good monic equation it is the full separable ordinate quotient, with
the ordinate represented by the actual lifted root. -/
theorem monic_fibre_equiv {f : (Polynomial A)} (hf : f.Monic) (γ : E) (root : aeval γ f=0)
    (b : Basis (Fin f.natDegree) F E) (pow : ∀ i,b i=γ^(i:ℕ))
    (j : A→+*K) (p : ℕ) [CharP K p] (small : f.natDegree<p) (sep : (f.map j).Separable) :
    let : Algebra A K := j.toAlgebra
    ∃ e : AdjoinRoot (f.map j) ≃ₐ[K] (K⊗[A] integralClosure A E),
      e (AdjoinRoot.root (f.map j))= (1:K) ⊗ₜ[A] (⟨γ,⟨f,hf,root⟩⟩:integralClosure A E) := by
  let : Algebra A K := j.toAlgebra
  let B := integralClosure A E
  let q := f.map j
  let x : B := ⟨γ,⟨f,hf,root⟩⟩
  have ib (i : Fin f.natDegree) : IsIntegral A (b i) := pow i ▸ x.property.pow _
  have disc : algebraMap A K (monicDisc hf)≠0 := monic_disc_nonzero_at hf j p small sep
  obtain ⟨bt,hbt⟩ := RetainedCrossingBasis.specialized_basis b ib (monicDisc hf)
    (fun x i=>monic_coordinates hf γ root b pow x i) K disc
  let image : B→ₐ[A] (K⊗[A] B) := Algebra.TensorProduct.includeRight
  have xroot : aeval x f=0 := by
    apply Subtype.ext
    exact (aeval_algHom_apply B.val x f).symm.trans root
  have imroot : aeval (image x) f=0 :=
    (aeval_algHom_apply image x f).trans (by rw [xroot,map_zero])
  have rootq : aeval (image x) q=0 := by
    change aeval (image x) (f.map (algebraMap A K))=0
    rw [aeval_map_algebraMap]
    exact imroot
  have qdeg : q.natDegree=f.natDegree := hf.natDegree_map j
  let bq : Basis (Fin f.natDegree) K (AdjoinRoot q) :=
    (AdjoinRoot.powerBasis' (hf.map j)).basis.reindex (finCongr qdeg)
  let h : AdjoinRoot q→ₐ[K](K⊗[A] B) :=
    AdjoinRoot.liftAlgHom q (Algebra.ofId _ _) (image x) rootq
  have β (i : Fin f.natDegree) : bt i=(image x)^(i:ℕ) := by
    rw [hbt,←map_pow]
    congr 1
    apply Subtype.ext
    exact pow i
  let e := bq.equiv bt (Equiv.refl _)
  have mapL : h.toLinearMap=e.toLinearMap := by
    apply bq.ext
    intro i
    change h (bq i)=e (bq i)
    have bi : bq i=AdjoinRoot.root q^(i:ℕ) := by
      rw [show bq i=(AdjoinRoot.powerBasis' (hf.map j)).basis ((finCongr qdeg).symm i) from
        Basis.reindex_apply _ _ _,(AdjoinRoot.powerBasis' (hf.map j)).basis_eq_pow]
      rfl
    rw [show e (bq i)=bt i from Basis.equiv_apply (b:=bq) (b':=bt) (e:=Equiv.refl _) (i:=i),
      bi,map_pow,AdjoinRoot.liftAlgHom_root,β]
  have bij : Function.Bijective h := by
    change Function.Bijective h.toLinearMap
    rw [mapL]
    exact e.bijective
  change ∃ e : AdjoinRoot q ≃ₐ[K] (K⊗[A] B),e (AdjoinRoot.root q)=image x
  refine ⟨AlgEquiv.ofBijective h bij,?_⟩
  change h (AdjoinRoot.root q)=image x
  exact AdjoinRoot.liftAlgHom_root q (Algebra.ofId K (K⊗[A] B)) (image x) rootq
end Fibre

#print axioms monic_disc_nonzero_at
#print axioms monic_fibre_equiv
end
end Lower6960.CollisionMarked
