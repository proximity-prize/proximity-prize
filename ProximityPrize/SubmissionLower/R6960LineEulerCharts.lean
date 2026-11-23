import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option Elab.async false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.LineEuler
noncomputable section
open LaurentPolynomial Polynomial Module Submodule
open scoped Polynomial BigOperators

abbrev Laurent (k : Type*) [Field k] := LaurentPolynomial k

variable {k ι : Type*} [Field k]

/-- The affine frame at infinity sends the polynomial variable to `t⁻¹`. -/
def infinityEmbedding : k[X] →ₐ[k] Laurent k := invert.toAlgHom.comp Polynomial.toLaurentAlg

@[simp] theorem infinityEmbedding_apply (f : k[X]) :
    infinityEmbedding f=invert f.toLaurent := rfl

theorem infinityEmbedding_injective : Function.Injective (infinityEmbedding (k:=k)) :=
  (invert (R:=k)).injective.comp Polynomial.toLaurent_injective

/-- Multiply the infinity chart by `t^N`, allowing all powers through `N`. -/
def shiftPolynomial (N : ℕ) : k[X] →ₗ[k] Laurent k :=
  (LinearMap.mul k (Laurent k) (T (N:ℤ))).comp infinityEmbedding.toLinearMap

@[simp] theorem shiftPolynomial_apply (N : ℕ) (f : k[X]) :
    shiftPolynomial N f=T (N:ℤ)*infinityEmbedding f := rfl

theorem coeff_shift (f : Laurent k) (N m : ℤ) : (T N*f).coeff m=f.coeff (m-N) := by
  change ((AddMonoidAlgebra.single N 1)*f).coeff m=_
  rw [AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (m-N) (by intro v _; omega),one_mul]

private theorem range_finitePolynomial :
    LinearMap.range (Polynomial.toLaurentAlg (R:=k)).toLinearMap =
      AddMonoidAlgebra.supported k k (Set.Ici (0:ℤ)) := by
  apply le_antisymm
  · rintro _ ⟨p,rfl⟩
    change ↑p.toLaurent.coeff.support ⊆ Set.Ici (0:ℤ)
    rw [support_coeff_toLaurent]
    intro n hn
    obtain ⟨m,_,rfl⟩ := Finset.mem_map.mp hn
    exact Int.natCast_nonneg m
  · rw [AddMonoidAlgebra.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨m,hm,rfl⟩
    refine ⟨Polynomial.X ^ m.toNat,?_⟩
    change (Polynomial.X ^ m.toNat : k[X]).toLaurent=T m
    rw [Polynomial.toLaurent_X_pow,Int.toNat_of_nonneg hm]

theorem range_shiftPolynomial (N : ℕ) :
    LinearMap.range (shiftPolynomial (k:=k) N) = AddMonoidAlgebra.supported k k (Set.Iic (N:ℤ)) := by
  apply le_antisymm
  · rintro _ ⟨p,rfl⟩
    apply AddMonoidAlgebra.mem_supported'.mpr
    intro m hm
    rw [shiftPolynomial_apply,coeff_shift,infinityEmbedding_apply,invert_apply]
    apply Finsupp.notMem_support_iff.mp
    rw [support_coeff_toLaurent]
    intro h
    obtain ⟨j,_,hj⟩ := Finset.mem_map.mp h
    change (j:ℤ)= -(m-(N:ℤ)) at hj
    change ¬m≤(N:ℤ) at hm
    omega
  · rw [AddMonoidAlgebra.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨m,hm,rfl⟩
    refine ⟨Polynomial.X ^ ((N:ℤ)-m).toNat,?_⟩
    change shiftPolynomial N _=T m
    rw [shiftPolynomial_apply,infinityEmbedding_apply,Polynomial.toLaurent_X_pow,invert_T,←T_add]
    congr 1
    change m≤(N:ℤ) at hm
    omega

private theorem shiftPolynomial_injective (N : ℕ) : Function.Injective (shiftPolynomial (k:=k) N) := by
  intro p q eq
  apply infinityEmbedding_injective
  have cancel := congrArg (fun x : Laurent k=>T (-(N:ℤ))*x) eq
  simpa only [shiftPolynomial_apply,←mul_assoc,←T_add,neg_add_cancel,T_zero,one_mul] using cancel

/-- The polynomial lattice in the finite chart, in the common Laurent space. -/
def finiteLattice (k ι : Type*) [Field k] : Submodule k (ι→Laurent k) :=
  Submodule.pi Set.univ fun _=>AddMonoidAlgebra.supported k k (Set.Ici (0:ℤ))

/-- The reference infinity lattice shifted by `t^N`. -/
def upperLattice (k ι : Type*) [Field k] (N : ℕ) : Submodule k (ι→Laurent k) :=
  Submodule.pi Set.univ fun _=>AddMonoidAlgebra.supported k k (Set.Iic (N:ℤ))

theorem mem_finiteLattice (v : ι→Laurent k) : v∈finiteLattice k ι ↔
    ∃ p : ι→k[X], ∀ i,(p i).toLaurent=v i := by
  classical
  change (∀ i : ι,i∈Set.univ→v i∈AddMonoidAlgebra.supported k k (Set.Ici (0:ℤ))) ↔ _
  simp only [Set.mem_univ,forall_true_left,←range_finitePolynomial,LinearMap.mem_range]
  exact ⟨fun h=>⟨fun i=>(h i).choose,fun i=>(h i).choose_spec⟩,fun ⟨p,hp⟩ i=>⟨p i,hp i⟩⟩

def shiftVector (N : ℕ) : (ι→k[X]) →ₗ[k] (ι→Laurent k) :=
  LinearMap.pi fun i=>(shiftPolynomial N).comp (LinearMap.proj i)

@[simp] theorem shiftVector_apply (N : ℕ) (p : ι→k[X]) (i : ι) :
    shiftVector N p i=T (N:ℤ)*infinityEmbedding (p i) := rfl

theorem range_shiftVector (N : ℕ) : LinearMap.range (shiftVector (k:=k) (ι:=ι) N)=upperLattice k ι N := by
  classical
  ext v
  change (∃ p : ι→k[X],shiftVector N p=v) ↔
    ∀ i : ι,i∈Set.univ→ v i∈AddMonoidAlgebra.supported k k (Set.Iic (N:ℤ))
  simp only [Set.mem_univ,forall_true_left,←range_shiftPolynomial,LinearMap.mem_range]
  constructor
  · rintro ⟨p,rfl⟩ i
    exact ⟨p i,rfl⟩
  · intro h
    choose p hp using h
    exact ⟨p,funext hp⟩

/-- The chosen polynomial basis at infinity identifies with the full
shifted lattice, using its actual element of the Laurent overlap. -/
def upperEquiv (N : ℕ) : (ι→k[X]) ≃ₗ[k] upperLattice k ι N := by
  let j := (shiftVector (k:=k) (ι:=ι) N).codRestrict (upperLattice k ι N)
    (fun p=>(range_shiftVector (k:=k) (ι:=ι) N) ▸ LinearMap.mem_range_self _ p)
  refine LinearEquiv.ofBijective j ⟨?_,?_⟩
  · intro p q h
    exact funext fun i=>shiftPolynomial_injective N (congrFun (congrArg Subtype.val h) i)
  · intro q
    have mq : (q:ι→Laurent k)∈(shiftVector (k:=k) (ι:=ι) N).range := (range_shiftVector (k:=k) (ι:=ι) N).symm ▸ q.property
    obtain ⟨p,hp⟩ := mq
    exact ⟨p,Subtype.ext hp⟩

@[simp] theorem upperEquiv_val (N : ℕ) (p : ι→k[X]) :
    ((upperEquiv N p):ι→Laurent k)=shiftVector N p := rfl

theorem finite_sup_upper (N : ℕ) : finiteLattice k ι⊔upperLattice k ι N=⊤ := by
  classical
  apply eq_top_iff.mpr
  intro v _
  let vf (i : ι) : Laurent k := AddMonoidAlgebra.ofCoeff ((v i).coeff.filter (fun n=>0≤n))
  refine Submodule.mem_sup.mpr ⟨vf,?_,v-vf,?_,by abel⟩
  · intro i _
    apply AddMonoidAlgebra.mem_supported'.mpr
    intro m hm
    change ¬0≤m at hm
    change ((v i).coeff.filter (fun n=>0≤n)) m=0
    simp [hm]
  · intro i _
    apply AddMonoidAlgebra.mem_supported'.mpr
    intro m hm
    change ¬m≤(N:ℤ) at hm
    have p : 0≤m := by omega
    change ((v i).coeff-((v i).coeff.filter (fun n=>0≤n))) m=0
    simp [p]

variable [Fintype ι]

/-- On the comparison lattice the common sections are exactly the
coefficient vectors in powers `0,…,N`. -/
theorem finite_inter_upper (N : ℕ) :
    FiniteDimensional k ↥(finiteLattice k ι⊓upperLattice k ι N) ∧
      finrank k ↥(finiteLattice k ι⊓upperLattice k ι N)=Fintype.card ι*(N+1) := by
  classical
  let I := Set.Icc (0:ℤ) (N:ℤ)
  let S := AddMonoidAlgebra.supported k k I
  let V := finiteLattice k ι⊓upperLattice k ι N
  let e : V ≃ₗ[k] (ι→S) := {
    toFun := fun v i=>⟨v.1 i,fun m hm=>⟨v.property.1 i (Set.mem_univ _) hm,v.property.2 i (Set.mem_univ _) hm⟩⟩
    invFun := fun v=>⟨fun i=>v i,⟨fun i _ m hm=>(v i).property hm |>.1,fun i _ m hm=>(v i).property hm |>.2⟩⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl
    map_add' := fun _ _=>rfl
    map_smul' := fun _ _=>rfl }
  let e' : V ≃ₗ[k] (ι→I→₀ k) := e.trans (LinearEquiv.piCongrRight fun _=>AddMonoidAlgebra.supportedEquivFinsupp I)
  have memI (m : ℤ) : m∈Finset.Icc (0:ℤ) (N:ℤ) ↔ m∈I := Finset.mem_Icc
  let : Fintype I := Fintype.ofFinset (Finset.Icc (0:ℤ) (N:ℤ)) memI
  have card : Fintype.card I=N+1 := (Fintype.card_ofFinset _ memI).trans (by rw [Int.card_Icc]; omega)
  have finite : FiniteDimensional k V := FiniteDimensional.of_injective e'.toLinearMap e'.injective
  refine ⟨finite,?_⟩
  change finrank k V=_
  rw [e'.finrank_eq,Module.finrank_pi_fintype]
  simp [Module.finrank_finsupp_self,card]

#print axioms range_shiftVector
#print axioms finite_sup_upper
#print axioms finite_inter_upper
end
end Lower6960.LineEuler
