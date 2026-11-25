import ProximityPrize.SubmissionLower.R6960RetainedPairedResidues
import ProximityPrize.SubmissionLower.R6960CollisionTameBranch
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.BilinearForm

set_option Elab.async false

-- merged module R6960CollisionMarkedMonicTrace
section Merged_R6960CollisionMarkedMonicTrace
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial Algebra Module Matrix
open scoped Polynomial Matrix BigOperators
section Trace
variable {A R U V ι : Type*} [CommRing A] [CommRing R] [CommRing U] [CommRing V]
  [Algebra A U] [Algebra R V] [Fintype ι] [DecidableEq ι]
theorem trace_matrix_map_of_basis (j : A→+*R) (a : Basis ι A U) (b : Basis ι R V) (φ : U→+*V)
    (scalar : ∀ c,φ (algebraMap A U c)=algebraMap R V (j c))
    (basis : ∀ i,φ (a i)=b i) : (traceMatrix A a).map j=traceMatrix R b := by
  have coords (x : U) (i : ι) : b.repr (φ x) i=j (a.repr x i) := by
    have expand : φ x=∑ l,j (a.repr x l) • b l := by
      rw [←a.sum_repr x,map_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Algebra.smul_def,map_mul,scalar,basis,←Algebra.smul_def]
      simp only [a.repr_sum_self]
    rw [expand,b.repr_sum_self]
  have trace_map (x : U) : j (Algebra.trace A U x)=Algebra.trace R V (φ x) := by
    rw [trace_eq_matrix_trace a,trace_eq_matrix_trace b]
    unfold Matrix.trace
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply,Matrix.diag_apply,leftMulMatrix_eq_repr_mul,leftMulMatrix_eq_repr_mul,
      ←basis,←map_mul,coords]
  apply Matrix.ext
  intro i l
  simp only [Matrix.map_apply,traceMatrix_apply,traceForm_apply,←basis,←map_mul,trace_map]
end Trace
section Monic
variable {A R V : Type*} [CommRing A] [CommRing R] [CommRing V] [Algebra R V]
def monicDisc {p : (Polynomial A)} (hp : p.Monic) : A := (traceMatrix A (AdjoinRoot.powerBasis' hp).basis).det
theorem monic_basis_trace {p : (Polynomial A)} (hp : p.Monic) (j : A→+*R)
    (γ : V) (root : aeval γ (p.map j)=0)
    (b : Basis (Fin p.natDegree) R V) (pow : ∀ i,b i=γ^(i:ℕ)) :
    (traceMatrix A (AdjoinRoot.powerBasis' hp).basis).map j=traceMatrix R b := by
  let ev := (algebraMap R V).comp j
  have rr : p.eval₂ ev γ=0 := by
    rw [aeval_def,eval₂_map] at root
    exact root
  let φ := AdjoinRoot.lift ev γ rr
  have scalar (c : A) : φ (algebraMap A (AdjoinRoot p) c)=algebraMap R V (j c) := by
    change AdjoinRoot.lift ev γ rr (AdjoinRoot.of p c)=_
    exact AdjoinRoot.lift_of rr
  have powers (i : Fin p.natDegree) : φ ((AdjoinRoot.powerBasis' hp).basis i)=b i := by
    rw [(AdjoinRoot.powerBasis' hp).basis_eq_pow,pow,map_pow]
    congr 1
    exact AdjoinRoot.lift_root rr
  exact trace_matrix_map_of_basis j (AdjoinRoot.powerBasis' hp).basis b φ scalar powers
theorem monic_disc_of_basis {p : (Polynomial A)} (hp : p.Monic) (j : A→+*R)
    (γ : V) (root : aeval γ (p.map j)=0)
    (b : Basis (Fin p.natDegree) R V) (pow : ∀ i,b i=γ^(i:ℕ)) :
    j (monicDisc hp)=Algebra.discr R b := by
  unfold monicDisc
  rw [Algebra.discr_def]
  exact (RingHom.map_det j _).trans (congrArg Matrix.det (monic_basis_trace hp j γ root b pow))
end Monic
section Coordinates
variable {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra A E] [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]
theorem monic_coordinates {p : (Polynomial A)} (hp : p.Monic) (γ : E) (root : aeval γ p=0)
    (b : Basis (Fin p.natDegree) F E) (pow : ∀ i,b i=γ^(i:ℕ))
    (x : integralClosure A E) :
    ∀ i,∃ c : A,algebraMap A F c=algebraMap A F (monicDisc hp)*b.repr (x:E) i := by
  classical
  let j := algebraMap A F
  have baseRoot : aeval γ (p.map j)=0 := by rw [aeval_map_algebraMap]; exact root
  let T : Matrix (Fin p.natDegree) (Fin p.natDegree) A := traceMatrix A (AdjoinRoot.powerBasis' hp).basis
  have eqT : T.map j=traceMatrix F b := monic_basis_trace hp j γ baseRoot b pow
  have integral : IsIntegral A γ := ⟨p,hp,root⟩
  have ib (i : Fin p.natDegree) : IsIntegral A (b i) := pow i ▸ integral.pow _
  choose t ht using fun i : Fin p.natDegree=>IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (L:=F) (x.property.mul (ib i)))
  have exp : (T.map j)*ᵥb.equivFun (x:E)=fun i=>j (t i) := by
    rw [eqT,Algebra.traceMatrix_of_basis_mulVec]
    exact funext fun i=>(ht i).symm
  let v := T.adjugate *ᵥ t
  intro i
  refine ⟨v i,?_⟩
  have all : (fun i=>j (v i))=j T.det • b.equivFun (x:E) := by
    change (fun i=>j ((T.adjugate*ᵥt) i))=_
    have mv : (fun i=>j ((T.adjugate*ᵥt) i))=T.adjugate.map j *ᵥ (fun i=>j (t i)) :=
      funext fun i=>RingHom.map_mulVec j _ _ i
    have adj : T.adjugate.map j=(T.map j).adjugate := j.map_adjugate T
    rw [mv,adj,←exp,Matrix.mulVec_mulVec,
      Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec,RingHom.map_det]
    rfl
  exact congrFun all i
theorem monic_order_eq_normalization {p : (Polynomial A)} (hp : p.Monic) (γ : E) (root : aeval γ p=0)
    (b : Basis (Fin p.natDegree) F E) (pow : ∀ i,b i=γ^(i:ℕ))
    (unit : IsUnit (monicDisc hp)) : Algebra.adjoin A {γ}=integralClosure A E := by
  let B := Algebra.adjoin A ({γ}:Set E)
  have gi : IsIntegral A γ := ⟨p,hp,root⟩
  apply le_antisymm
  · exact Algebra.adjoin_le (fun y hy=>(Set.mem_singleton_iff.mp hy).symm ▸ gi)
  · intro x hx
    choose c hc using monic_coordinates hp γ root b pow (⟨x,hx⟩:integralClosure A E)
    obtain ⟨d,hd⟩ := unit
    have dx : algebraMap A F (monicDisc hp) • x=∑ i,algebraMap A F (c i) • b i := by
      rw [←b.sum_repr x,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul,←hc i]
    have isin : monicDisc hp • x∈B := by
      rw [←IsScalarTower.algebraMap_smul F,dx]
      apply B.sum_mem
      intro i _
      rw [IsScalarTower.algebraMap_smul F,pow]
      exact B.smul_mem (B.pow_mem (Algebra.subset_adjoin (Set.mem_singleton γ)) _) _
    have cancel : (↑d⁻¹:A) • (monicDisc hp • x)=x := by
      rw [smul_smul,←hd,Units.inv_mul,one_smul]
    exact cancel ▸ B.smul_mem isin _
end Coordinates
#print axioms monic_disc_of_basis
#print axioms monic_coordinates
#print axioms monic_order_eq_normalization
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedMonicTrace

-- merged module R6960CollisionMarkedMonicFibre
section Merged_R6960CollisionMarkedMonicFibre
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

end Merged_R6960CollisionMarkedMonicFibre
