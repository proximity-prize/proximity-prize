import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ProximityPrize.SubmissionLower.R6960LineEulerComparison
import ProximityPrize.SubmissionLower.R6960LineEulerPolynomial
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Module

-- merged module R6960LineEulerCharts
section Merged_R6960LineEulerCharts
set_option Elab.async false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.LineEuler
noncomputable section
open LaurentPolynomial Polynomial Module Submodule
open scoped Polynomial BigOperators
abbrev Laurent (k : Type*) [Field k] := LaurentPolynomial k
variable {k ι : Type*} [Field k]
def infinityEmbedding : (Polynomial k) →ₐ[k] Laurent k := invert.toAlgHom.comp Polynomial.toLaurentAlg
@[simp] theorem infinityEmbedding_apply (f : (Polynomial k)) :
    infinityEmbedding f=invert f.toLaurent := rfl
theorem infinityEmbedding_injective : Function.Injective (infinityEmbedding (k:=k)) :=
  (invert (R:=k)).injective.comp Polynomial.toLaurent_injective
def shiftPolynomial (N : ℕ) : (Polynomial k) →ₗ[k] Laurent k :=
  (LinearMap.mul k (Laurent k) (T (N:ℤ))).comp infinityEmbedding.toLinearMap
@[simp] theorem shiftPolynomial_apply (N : ℕ) (f : (Polynomial k)) :
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
    change (Polynomial.X ^ m.toNat : (Polynomial k)).toLaurent=T m
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
def finiteLattice (k ι : Type*) [Field k] : Submodule k (ι→Laurent k) :=
  Submodule.pi Set.univ fun _=>AddMonoidAlgebra.supported k k (Set.Ici (0:ℤ))
def upperLattice (k ι : Type*) [Field k] (N : ℕ) : Submodule k (ι→Laurent k) :=
  Submodule.pi Set.univ fun _=>AddMonoidAlgebra.supported k k (Set.Iic (N:ℤ))
theorem mem_finiteLattice (v : ι→Laurent k) : v∈finiteLattice k ι ↔
    ∃ p : ι→(Polynomial k), ∀ i,(p i).toLaurent=v i := by
  classical
  change (∀ i : ι,i∈Set.univ→v i∈AddMonoidAlgebra.supported k k (Set.Ici (0:ℤ))) ↔ _
  simp only [Set.mem_univ,forall_true_left,←range_finitePolynomial,LinearMap.mem_range]
  exact ⟨fun h=>⟨fun i=>(h i).choose,fun i=>(h i).choose_spec⟩,fun ⟨p,hp⟩ i=>⟨p i,hp i⟩⟩
def shiftVector (N : ℕ) : (ι→(Polynomial k)) →ₗ[k] (ι→Laurent k) :=
  LinearMap.pi fun i=>(shiftPolynomial N).comp (LinearMap.proj i)
@[simp] theorem shiftVector_apply (N : ℕ) (p : ι→(Polynomial k)) (i : ι) :
    shiftVector N p i=T (N:ℤ)*infinityEmbedding (p i) := rfl
theorem range_shiftVector (N : ℕ) : LinearMap.range (shiftVector (k:=k) (ι:=ι) N)=upperLattice k ι N := by
  classical
  ext v
  change (∃ p : ι→(Polynomial k),shiftVector N p=v) ↔
    ∀ i : ι,i∈Set.univ→ v i∈AddMonoidAlgebra.supported k k (Set.Iic (N:ℤ))
  simp only [Set.mem_univ,forall_true_left,←range_shiftPolynomial,LinearMap.mem_range]
  constructor
  · rintro ⟨p,rfl⟩ i
    exact ⟨p i,rfl⟩
  · intro h
    choose p hp using h
    exact ⟨p,funext hp⟩
def upperEquiv (N : ℕ) : (ι→(Polynomial k)) ≃ₗ[k] upperLattice k ι N := by
  let j := (shiftVector (k:=k) (ι:=ι) N).codRestrict (upperLattice k ι N)
    (fun p=>(range_shiftVector (k:=k) (ι:=ι) N) ▸ LinearMap.mem_range_self _ p)
  refine LinearEquiv.ofBijective j ⟨?_,?_⟩
  · intro p q h
    exact funext fun i=>shiftPolynomial_injective N (congrFun (congrArg Subtype.val h) i)
  · intro q
    have mq : (q:ι→Laurent k)∈(shiftVector (k:=k) (ι:=ι) N).range := (range_shiftVector (k:=k) (ι:=ι) N).symm ▸ q.property
    obtain ⟨p,hp⟩ := mq
    exact ⟨p,Subtype.ext hp⟩
@[simp] theorem upperEquiv_val (N : ℕ) (p : ι→(Polynomial k)) :
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

end Merged_R6960LineEulerCharts

-- merged module R6960LineEulerTransition
section Merged_R6960LineEulerTransition
set_option Elab.async false
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.LineEuler
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped Polynomial BigOperators
variable {k ι : Type*} [Field k]
theorem unit_monomial (f : Laurent k) (h : IsUnit f) :
    ∃ (c : k) (j : ℤ),c≠0 ∧ f=LaurentPolynomial.C c*T j := by
  obtain ⟨u,rfl⟩ := h
  obtain ⟨n,a,ea⟩ := LaurentPolynomial.exists_T_pow (u:Laurent k)
  obtain ⟨m,b,eb⟩ := LaurentPolynomial.exists_T_pow (↑u⁻¹:Laurent k)
  have product : a*b=(Polynomial.X : (Polynomial k))^(n+m) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul,ea,eb,Polynomial.toLaurent_X_pow]
    rw [mul_mul_mul_comm,Units.mul_inv,one_mul,←T_add]
    push_cast
    rfl
  obtain ⟨j,_,h⟩ := (dvd_prime_pow (Polynomial.prime_X (R:=k)) (n+m)).mp (show a∣_ from ⟨b,product.symm⟩)
  obtain ⟨v,hv⟩ := h.symm
  let c := (v:(Polynomial k)).coeff 0
  have vC : (v:(Polynomial k))=Polynomial.C c := eq_C_of_natDegree_eq_zero (natDegree_coe_units v)
  have cn : c≠0 := by
    intro z
    exact v.ne_zero (by rw [vC,z,map_zero])
  have aa : a=(Polynomial.X : (Polynomial k))^j*Polynomial.C c := by
    rw [vC] at hv
    exact hv.symm
  refine ⟨c,(j:ℤ)-n,cn,?_⟩
  have shifted : (u:Laurent k)*T (n:ℤ)=LaurentPolynomial.C c*T (j:ℤ) := by
    rw [←ea,aa,map_mul,Polynomial.toLaurent_X_pow,Polynomial.toLaurent_C,mul_comm]
  calc
    (u:Laurent k) = ((u:Laurent k)*T (n:ℤ))*T (-(n:ℤ)) := by
      rw [mul_assoc,←T_add,add_neg_cancel,T_zero,mul_one]
    _ = LaurentPolynomial.C c*T ((j:ℤ)-n) := by rw [shifted,mul_assoc,T_sub]
variable [Fintype ι]
theorem clear_transition (G : Matrix ι ι (Laurent k)) :
    ∃ (N : ℕ) (A : Matrix ι ι (Polynomial k)), G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k)) := by
  classical
  let N := Finset.univ.sup fun i : ι=>Finset.univ.sup fun j : ι=>(G i j).coeff.support.sup Int.toNat
  have bound (i j : ι) {m : ℤ} (hm : m∈(G i j).coeff.support) : m≤(N:ℤ) := by
    have a := Finset.le_sup (f:=Int.toNat) hm
    have b := Finset.le_sup (f:=fun j : ι=>(G i j).coeff.support.sup Int.toNat) (Finset.mem_univ j)
    have c : (Finset.univ.sup fun j : ι=>(G i j).coeff.support.sup Int.toNat)≤N :=
      Finset.le_sup (f:=fun i : ι=>Finset.univ.sup fun j : ι=>(G i j).coeff.support.sup Int.toNat)
        (Finset.mem_univ i)
    have d := a.trans (b.trans c)
    omega
  have fit (i j : ι) : ∃ p : (Polynomial k),shiftPolynomial N p=G i j := by
    change G i j∈LinearMap.range (shiftPolynomial N)
    rw [range_shiftPolynomial]
    exact AddMonoidAlgebra.mem_supported.mpr (fun _ hm=>bound i j hm)
  choose a ha using fit
  refine ⟨N,a,?_⟩
  apply Matrix.ext
  intro i j
  exact (ha i j).symm
variable [DecidableEq ι]
theorem transition_degree (G : Matrix ι ι (Laurent k)) (unit : IsUnit G)
    (N : ℕ) (A : Matrix ι ι (Polynomial k)) (clear : G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k))) :
    A.det≠0 ∧ ∃ d : ℤ, G.det.degree=(d:WithBot ℤ) ∧
      d=(Fintype.card ι:ℤ)*(N:ℤ)-(A.det.natDegree:ℤ) := by
  let M : ℤ := (Fintype.card ι:ℤ)*(N:ℤ)
  have unitDet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp unit
  have mapDet : (A.map (infinityEmbedding (k:=k))).det=infinityEmbedding A.det :=
    ((infinityEmbedding (k:=k)).toRingHom.map_det A).symm
  have factor : G.det = (T M : Laurent k)*infinityEmbedding A.det := by
    rw [clear,Matrix.det_smul,mapDet,LaurentPolynomial.T_pow]
  have nz : A.det≠0 := by
    intro h
    exact unitDet.ne_zero (by rw [factor,h,map_zero,mul_zero])
  obtain ⟨c,d,cn,hd⟩ := unit_monomial G.det unitDet
  have monomial : infinityEmbedding A.det=LaurentPolynomial.C c*T (d-M) := calc
    _ = (T (-M):Laurent k)*G.det := by rw [factor,←mul_assoc,←T_add,neg_add_cancel,T_zero,one_mul]
    _ = _ := by rw [hd,mul_left_comm,←T_add]; congr 2; omega
  have direct : A.det.toLaurent = LaurentPolynomial.C c*T (M-d) := by
    have eq := congrArg (invert (R:=k)) monomial
    simpa only [infinityEmbedding_apply,involutive_invert A.det.toLaurent,map_mul,invert_C,invert_T,neg_sub] using eq
  have supp : A.det.toLaurent.coeff.support={M-d} := by
    rw [direct,support_coeff_C_mul_T_of_ne_zero cn]
  have degreeMem : (A.det.natDegree:ℤ)∈A.det.toLaurent.coeff.support := by
    rw [support_coeff_toLaurent]
    exact Finset.mem_map.mpr ⟨_,natDegree_mem_support_of_nonzero nz,rfl⟩
  have deg := Finset.mem_singleton.mp (supp ▸ degreeMem)
  exact ⟨nz,d,by rw [hd,degree_C_mul_T _ _ cn],by change d=M-_; omega⟩
#print axioms unit_monomial
#print axioms transition_degree
end
end Lower6960.LineEuler

end Merged_R6960LineEulerTransition

-- merged module R6960LineEuler
section Merged_R6960LineEuler
set_option Elab.async false
set_option maxHeartbeats 4400000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.LineEuler
noncomputable section
open LaurentPolynomial Polynomial Module Submodule
open scoped Polynomial BigOperators
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
def transitionLattice (G : Matrix ι ι (Laurent k)) : Submodule k (ι→Laurent k) :=
  (upperLattice k ι 0).map ((Matrix.toLin' G).restrictScalars k)
abbrev H0 (G : Matrix ι ι (Laurent k)) := ↥(finiteLattice k ι⊓transitionLattice G)
abbrev H1 (G : Matrix ι ι (Laurent k)) := (ι→Laurent k) ⧸ (finiteLattice k ι⊔transitionLattice G)
private theorem action_commutes (G : Matrix ι ι (Laurent k)) (N : ℕ) (A : Matrix ι ι (Polynomial k))
    (clear : G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k))) (v : ι→(Polynomial k)) :
    Matrix.toLin' G (shiftVector 0 v)=shiftVector N (Matrix.toLin' A v) := by
  funext i
  rw [Matrix.toLin'_apply,shiftVector_apply,Matrix.toLin'_apply]
  change (∑ j, G i j * (T (0:ℤ)*infinityEmbedding (v j))) =
    T (N:ℤ)*infinityEmbedding (∑ j, A i j*v j)
  rw [clear,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,T_zero,one_mul,map_mul,mul_assoc]
theorem transition_eq_cleared (G : Matrix ι ι (Laurent k)) (N : ℕ) (A : Matrix ι ι (Polynomial k))
    (clear : G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k))) :
    transitionLattice G=((Matrix.toLin' A).range.restrictScalars k).map (shiftVector N) := by
  rw [transitionLattice,←range_shiftVector 0]
  ext v
  constructor
  · rintro ⟨w,⟨p,rfl⟩,rfl⟩
    exact ⟨Matrix.toLin' A p,⟨p,rfl⟩,(action_commutes G N A clear p).symm⟩
  · rintro ⟨w,⟨p,rfl⟩,rfl⟩
    exact ⟨shiftVector 0 p,⟨p,rfl⟩,action_commutes G N A clear p⟩
private def relative_quotient (G : Matrix ι ι (Laurent k)) (N : ℕ) (A : Matrix ι ι (Polynomial k))
    (clear : G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k))) :
    ((ι→(Polynomial k)) ⧸ (Matrix.toLin' A).range) ≃ₗ[k]
      ((upperLattice k ι N) ⧸ (transitionLattice G).comap (upperLattice k ι N).subtype) := by
  let B := upperLattice k ι N
  let D := (transitionLattice G).comap B.subtype
  let R := (Matrix.toLin' A).range.restrictScalars k
  change ((ι→(Polynomial k)) ⧸ R) ≃ₗ[k] (B ⧸ D)
  let e : (ι→(Polynomial k)) ≃ₗ[k] B := upperEquiv N
  refine Submodule.Quotient.equiv R D e ?_
  ext v
  change (∃ p∈R,e p=v) ↔ (v:ι→Laurent k)∈transitionLattice G
  rw [transition_eq_cleared G N A clear]
  change (∃ p∈R,e p=v) ↔ ∃ p∈R,shiftVector N p=(v:ι→Laurent k)
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨p,hp,rfl⟩
  · rintro ⟨p,hp,eq⟩
    exact ⟨p,hp,Subtype.ext eq⟩
theorem euler_index (G : Matrix ι ι (Laurent k)) (unit : IsUnit G) :
    FiniteDimensional k (H0 G) ∧ FiniteDimensional k (H1 G) ∧
    ∃ d : ℤ,G.det.degree=(d:WithBot ℤ) ∧
      (finrank k (H0 G):ℤ)-(finrank k (H1 G):ℤ)=(Fintype.card ι:ℤ)+d := by
  obtain ⟨N,A,clear⟩ := clear_transition G
  obtain ⟨an,d,d_eq,d_value⟩ := transition_degree G unit N A clear
  obtain ⟨finiteQ,degQ⟩ := polynomial_cokernel A an
  obtain ⟨finiteI,degI⟩ := finite_inter_upper (k:=k) (ι:=ι) N
  let B := upperLattice k ι N
  let C := transitionLattice G
  let F := finiteLattice k ι
  let equiv := relative_quotient G N A clear
  let : FiniteDimensional k (B ⧸ C.comap B.subtype) :=
    FiniteDimensional.of_surjective equiv.toLinearMap equiv.surjective
  have inc : C≤B := by
    intro v hv
    change v∈transitionLattice G at hv
    rw [transition_eq_cleared G N A clear] at hv
    obtain ⟨p,_,rfl⟩ := hv
    exact (upperEquiv N p).property
  have relativeDim : finrank k (B ⧸ C.comap B.subtype)=A.det.natDegree := equiv.finrank_eq.symm.trans degQ
  obtain ⟨finite0,finite1,eq⟩ := compare_lattices F C B inc (finite_sup_upper N)
  refine ⟨finite0,finite1,d,d_eq,?_⟩
  rw [relativeDim,degI] at eq
  change finrank k (H0 G)+A.det.natDegree=finrank k (H1 G)+Fintype.card ι*(N+1) at eq
  rw [Nat.mul_add,Nat.mul_one] at eq
  have eqZ := congrArg (fun n : ℕ=>(n:ℤ)) eq
  push_cast at eqZ
  omega
#print axioms euler_index
end
end Lower6960.LineEuler

end Merged_R6960LineEuler

-- merged module R6960LineEulerNormalization
section Merged_R6960LineEulerNormalization
set_option Elab.async false
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.LineEuler
noncomputable section
open Polynomial LaurentPolynomial Module
open scoped Polynomial BigOperators Matrix
variable {k : Type*} [Field k]
def chartEmbedding (infinity : Bool) : (Polynomial k) →ₐ[k] Laurent k :=
  if infinity then infinityEmbedding else Polynomial.toLaurentAlg
theorem chartLocalization (s : Bool) :
    let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
    IsLocalization.Away (Polynomial.X : (Polynomial k)) (Laurent k) := by
  let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  have inj : Function.Injective (chartEmbedding (k:=k) s) := by
    cases s
    · exact Polynomial.toLaurent_injective
    · exact infinityEmbedding_injective
  apply IsLocalization.Away.mk (Polynomial.X : (Polynomial k))
  · change IsUnit (chartEmbedding s (Polynomial.X : (Polynomial k)))
    have eq : chartEmbedding s (Polynomial.X : (Polynomial k))=T (if s then -1 else 1) := by
      cases s <;> simp [chartEmbedding,Polynomial.toLaurent_X]
    rw [eq]
    exact isUnit_T _
  · intro z
    cases s with
    | false =>
      obtain ⟨n,p,hp⟩ := LaurentPolynomial.exists_T_pow z
      refine ⟨n,p,?_⟩
      change z*(chartEmbedding false (Polynomial.X : (Polynomial k)))^n=chartEmbedding false p
      rw [←map_pow]
      change z*(Polynomial.X^n : (Polynomial k)).toLaurent=p.toLaurent
      simpa only [Polynomial.toLaurent_X_pow] using hp.symm
    | true =>
      obtain ⟨n,p,hp⟩ := LaurentPolynomial.exists_T_pow (invert z)
      refine ⟨n,p,?_⟩
      change z*(chartEmbedding true (Polynomial.X : (Polynomial k)))^n=chartEmbedding true p
      rw [←map_pow]
      change z*invert (Polynomial.X^n : (Polynomial k)).toLaurent=invert p.toLaurent
      have e := congrArg (invert (R:=k)) hp
      rw [map_mul,involutive_invert z,invert_T] at e
      simpa only [Polynomial.toLaurent_X_pow,invert_T] using e.symm
  · intro x y eq
    exact ⟨0,by rw [inj eq]⟩
variable {E : Type*} [Field E] [Algebra (Laurent k) E]
abbrev chartOrder (s : Bool) :=
  @integralClosure (Polynomial k) E _ _ ((algebraMap (Laurent k) E).comp (chartEmbedding s).toRingHom).toAlgebra
abbrev torusOrder := integralClosure (Laurent k) E
def chartOrderMap (s : Bool) : chartOrder (k:=k) (E:=E) s →+* torusOrder (k:=k) (E:=E) := by
  let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  let : Algebra (Polynomial k) E := ((algebraMap (Laurent k) E).comp (chartEmbedding s).toRingHom).toAlgebra
  let : IsScalarTower (Polynomial k) (Laurent k) E :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=Laurent k) (A:=E) fun _=>rfl
  exact Subring.inclusion (show (chartOrder (k:=k) (E:=E) s).toSubring≤(torusOrder (k:=k) (E:=E)).toSubring
    from fun _ hi=>IsIntegral.tower_top (show IsIntegral (Polynomial k) _ from hi))
@[simp] theorem chartOrderMap_val (s : Bool) (x : chartOrder (k:=k) (E:=E) s) :
    (chartOrderMap s x:E)=(x:E) := rfl
variable {ι : Type*}
private def localBasisData (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s)) :
    {B : Basis ι (Laurent k) (torusOrder (k:=k) (E:=E)) //
      (∀ i,B i=chartOrderMap s (b i)) ∧
      ∀ x i,B.repr (chartOrderMap s x) i=chartEmbedding s (b.repr x i)} := by
  let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  let : Algebra (Polynomial k) E := ((algebraMap (Laurent k) E).comp (chartEmbedding s).toRingHom).toAlgebra
  let : IsScalarTower (Polynomial k) (Laurent k) E :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=Laurent k) (A:=E) fun _=>rfl
  let A := chartOrder (k:=k) (E:=E) s
  let S := torusOrder (k:=k) (E:=E)
  let : Algebra (Polynomial k) S := ((algebraMap (Laurent k) S).comp (chartEmbedding s).toRingHom).toAlgebra
  let : Algebra A S := (chartOrderMap (k:=k) (E:=E) s).toAlgebra
  let : IsScalarTower (Polynomial k) (Laurent k) S :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=Laurent k) (A:=S) fun _=>rfl
  let : IsScalarTower A S E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=S) (A:=E) fun _=>rfl
  let : IsScalarTower (Polynomial k) A S :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=A) (A:=S) fun _=>rfl
  let : IsScalarTower (Polynomial k) S E :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=S) (A:=E) fun _=>rfl
  let : IsLocalization.Away (Polynomial.X : (Polynomial k)) (Laurent k) := chartLocalization (k:=k) s
  have ux : IsUnit (algebraMap (Polynomial k) E (Polynomial.X : (Polynomial k))) := by
    change IsUnit (algebraMap (Laurent k) E (chartEmbedding s (Polynomial.X : (Polynomial k))))
    have mapX : chartEmbedding s (Polynomial.X : (Polynomial k))=T (if s then -1 else 1) := by
      cases s <;> simp [chartEmbedding,Polynomial.toLaurent_X]
    rw [mapX]
    exact (isUnit_T _).map _
  let : IsLocalization.Away (algebraMap (Polynomial k) E (Polynomial.X : (Polynomial k))) E :=
    IsLocalization.away_of_isUnit_of_bijective E ux Function.bijective_id
  let : IsLocalization.Away (algebraMap (Polynomial k) A (Polynomial.X : (Polynomial k))) S :=
    IsLocalization.Away.integralClosure (S:=E) (Rf:=Laurent k) (Sf:=E) (Polynomial.X : (Polynomial k))
  let powers := Submonoid.powers (Polynomial.X : (Polynomial k))
  refine ⟨b.localizationLocalization (Laurent k) powers S,?_,?_⟩
  · intro i
    exact b.localizationLocalization_apply (Laurent k) powers S i
  · intro x i
    exact b.localizationLocalization_repr_algebraMap (Laurent k) powers S x i
def localBasis (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s)) :
    Basis ι (Laurent k) (torusOrder (k:=k) (E:=E)) := (localBasisData s b).1
@[simp] theorem localBasis_apply (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s)) (i : ι) :
    localBasis s b i=chartOrderMap s (b i) := (localBasisData s b).2.1 i
@[simp] theorem localBasis_repr (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s))
    (x : chartOrder (k:=k) (E:=E) s) (i : ι) :
    (localBasis s b).repr (chartOrderMap s x) i=chartEmbedding s (b.repr x i) := (localBasisData s b).2.2 x i
variable [Fintype ι] [DecidableEq ι]
def normalizedTransition (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) : Matrix ι ι (Laurent k) :=
  LinearMap.toMatrix' (((localBasis true bi).equivFun.symm.trans (localBasis false bf).equivFun).toLinearMap)
theorem normalizedTransition_unit (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) : IsUnit (normalizedTransition bf bi) := by
  let e := (localBasis true bi).equivFun.symm.trans (localBasis false bf).equivFun
  apply isUnit_iff_exists_inv.mpr
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap,?_⟩
  apply Matrix.toLin'.injective
  rw [normalizedTransition,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_toMatrix',Matrix.toLin'_one]
  exact e.comp_symm
theorem normalizedTransition_mulVec (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) (v : ι→Laurent k) :
    normalizedTransition bf bi *ᵥ v=(localBasis false bf).equivFun ((localBasis true bi).equivFun.symm v) := by
  rw [←Matrix.toLin'_apply,normalizedTransition,Matrix.toLin'_toMatrix']
  rfl
def chartMatrix {s : Bool} (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s))
    (u : ι→chartOrder (k:=k) (E:=E) s) : Matrix ι ι (Polynomial k) := fun i j=>b.repr (u j) i
theorem normalized_join (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true))
    (x : ι→chartOrder (k:=k) (E:=E) false) (y : ι→chartOrder (k:=k) (E:=E) true) (width : ι→ℕ)
    (agree : ∀ j,(x j:E)=algebraMap (Laurent k) E (T (width j:ℤ))*(y j:E)) :
    (chartMatrix bf x).map (Polynomial.toLaurent (R:=k)) = normalizedTransition bf bi *
      (chartMatrix bi y).map (infinityEmbedding (k:=k)) * Matrix.diagonal (fun j=>T (width j:ℤ)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_diagonal]
  change chartEmbedding false (bf.repr (x j) i) =
    ((normalizedTransition bf bi) *ᵥ (fun u=>chartEmbedding true (bi.repr (y j) u))) i * T (width j:ℤ)
  have coord : (fun u=>chartEmbedding true (bi.repr (y j) u)) =
      (localBasis true bi).equivFun (chartOrderMap true (y j)) := by
    funext u
    rw [Basis.equivFun_apply,localBasis_repr]
  rw [coord,normalizedTransition_mulVec,LinearEquiv.symm_apply_apply]
  have tor : chartOrderMap false (x j)=T (R:=k) (width j:ℤ) • chartOrderMap true (y j) := by
    apply Subtype.ext
    rw [chartOrderMap_val,Subalgebra.coe_smul,chartOrderMap_val,Algebra.smul_def]
    exact agree j
  calc
    _ = (localBasis false bf).equivFun (chartOrderMap false (x j)) i := by
      rw [Basis.equivFun_apply,localBasis_repr]
    _ = _ := by
      rw [tor,(localBasis false bf).equivFun.map_smul]
      change T (width j:ℤ)*(localBasis false bf).equivFun (chartOrderMap true (y j)) i=_
      exact mul_comm _ _
theorem normalized_euler (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) :
    FiniteDimensional k (H0 (normalizedTransition bf bi)) ∧
    FiniteDimensional k (H1 (normalizedTransition bf bi)) ∧
    ∃ d : ℤ,(normalizedTransition bf bi).det.degree=(d:WithBot ℤ) ∧
      (finrank k (H0 (normalizedTransition bf bi)):ℤ)-(finrank k (H1 (normalizedTransition bf bi)):ℤ)=
        (Fintype.card ι:ℤ)+d :=
  euler_index _ (normalizedTransition_unit bf bi)
#print axioms localBasis
#print axioms normalized_euler
end
end Lower6960.LineEuler

end Merged_R6960LineEulerNormalization

-- merged module R6960LineEulerFree
section Merged_R6960LineEulerFree
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.LineEuler
noncomputable section
open Polynomial LaurentPolynomial Module
open scoped Polynomial BigOperators Matrix
open Lower6960.LineEuler (chartLocalization)
variable {k ι M U V : Type*} [Field k]
  [AddCommGroup M] [Module (Laurent k) M]
  [AddCommGroup U] [Module (Polynomial k) U] [AddCommGroup V] [Module (Polynomial k) V]
abbrev ChartMap (s : Bool) (U M : Type*) [AddCommGroup U] [Module (Polynomial k) U]
    [AddCommGroup M] [Module (Laurent k) M] :=
  letI : Module (Polynomial k) M := Module.compHom M (chartEmbedding (k:=k) s).toRingHom
  U→ₗ[(Polynomial k)] M
def IsChartLocalization (s : Bool) (f : ChartMap (k:=k) s U M) : Prop :=
  let : Module (Polynomial k) M := Module.compHom M (chartEmbedding (k:=k) s).toRingHom
  IsLocalizedModule (Submonoid.powers (Polynomial.X : (Polynomial k))) f
theorem isChartLocalization_of_clearing (s : Bool) (f : ChartMap (k:=k) s U M)
    (inj : Function.Injective f)
    (clearing : ∀ v : M,∃ (n : ℕ) (u : U), (chartEmbedding s (Polynomial.X : (Polynomial k)))^n • v=f u) :
    IsChartLocalization s f := by
  let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  let : Module (Polynomial k) M := Module.compHom M (chartEmbedding (k:=k) s).toRingHom
  let powers := Submonoid.powers (Polynomial.X : (Polynomial k))
  let : IsLocalization powers (Laurent k) := Lower6960.LineEuler.chartLocalization (k:=k) s
  change IsLocalizedModule powers f
  constructor
  · intro a
    obtain ⟨u,hu⟩ := IsLocalization.map_units (Laurent k) a
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun v : M=>chartEmbedding s (a:(Polynomial k)) • v)
    change (u:Laurent k)=chartEmbedding s (a:(Polynomial k)) at hu
    rw [←hu]
    refine ⟨?_,?_⟩
    · intro x y eq
      have inv := congrArg (fun z : M=>(↑u⁻¹:Laurent k) • z) eq
      simpa only [←mul_smul,Units.inv_mul,one_smul] using inv
    · intro v
      refine ⟨(↑u⁻¹:Laurent k) • v,?_⟩
      change (u:Laurent k) • ((↑u⁻¹:Laurent k) • v)=v
      rw [←mul_smul,Units.mul_inv,one_smul]
  · intro v
    obtain ⟨n,u,eq⟩ := clearing v
    exact ⟨⟨u,⟨(Polynomial.X:(Polynomial k))^n,n,rfl⟩⟩,by
      change chartEmbedding s ((Polynomial.X:(Polynomial k))^n) • v=f u
      rw [map_pow,eq]⟩
  · intro x y eq
    exact ⟨1,by rw [inj eq]⟩
private def localFreeData (s : Bool) (b : Basis ι (Polynomial k) U) (f : ChartMap (k:=k) s U M)
    (loc : IsChartLocalization s f) :
    {B : Basis ι (Laurent k) M // (∀ i,B i=f (b i)) ∧
      ∀ u i,B.repr (f u) i=chartEmbedding s (b.repr u i)} := by
  let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  let : Module (Polynomial k) M := Module.compHom M (chartEmbedding (k:=k) s).toRingHom
  let : IsScalarTower (Polynomial k) (Laurent k) M := ⟨fun p r v=>by
    change (chartEmbedding s p*r) • v=chartEmbedding s p • (r • v)
    exact mul_smul _ _ _⟩
  let : IsLocalization.Away (Polynomial.X : (Polynomial k)) (Laurent k) :=
    Lower6960.LineEuler.chartLocalization (k:=k) s
  let powers := Submonoid.powers (Polynomial.X : (Polynomial k))
  let : IsLocalizedModule powers f := loc
  refine ⟨b.ofIsLocalizedModule (Laurent k) powers f,?_,?_⟩
  · intro i
    exact b.ofIsLocalizedModule_apply (Laurent k) powers f i
  · intro u i
    exact b.ofIsLocalizedModule_repr_apply (Laurent k) powers f u i
def localFreeBasis (s : Bool) (b : Basis ι (Polynomial k) U) (f : ChartMap (k:=k) s U M)
    (loc : IsChartLocalization s f) : Basis ι (Laurent k) M := (localFreeData s b f loc).1
@[simp] theorem localFreeBasis_apply (s : Bool) (b : Basis ι (Polynomial k) U) (f : ChartMap (k:=k) s U M)
    (loc : IsChartLocalization s f) (i : ι) : localFreeBasis s b f loc i=f (b i) :=
  (localFreeData s b f loc).2.1 i
@[simp] theorem localFreeBasis_repr (s : Bool) (b : Basis ι (Polynomial k) U) (f : ChartMap (k:=k) s U M)
    (loc : IsChartLocalization s f) (u : U) (i : ι) :
    (localFreeBasis s b f loc).repr (f u) i=chartEmbedding s (b.repr u i) :=
  (localFreeData s b f loc).2.2 u i
def chartLattice (s : Bool) : Submodule k (ι→Laurent k) :=
  if s then upperLattice k ι 0 else finiteLattice k ι
theorem chartLattice_iff (s : Bool) (v : ι→Laurent k) : v∈chartLattice s ↔
    ∃ q : ι→(Polynomial k),∀ i,chartEmbedding s (q i)=v i := by
  cases s with
  | false => exact mem_finiteLattice v
  | true =>
    change v∈upperLattice k ι 0 ↔ _
    rw [←range_shiftVector 0,LinearMap.mem_range]
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨q,fun i=>by simp [chartEmbedding]⟩
    · rintro ⟨q,hq⟩
      exact ⟨q,funext fun i=>by simpa [chartEmbedding] using hq i⟩
private theorem coordinate_image [Finite ι] (s : Bool) (b : Basis ι (Polynomial k) U)
    (f : ChartMap (k:=k) s U M) (loc : IsChartLocalization s f) (v : M) :
    (localFreeBasis s b f loc).equivFun v∈chartLattice s ↔ ∃ u : U,f u=v := by
  rw [chartLattice_iff]
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨b.equivFun.symm q,(localFreeBasis s b f loc).equivFun.injective (funext fun i=>?_ )⟩
    rw [Basis.equivFun_apply,localFreeBasis_repr,←Basis.equivFun_apply,LinearEquiv.apply_symm_apply]
    exact hq i
  · rintro ⟨u,rfl⟩
    exact ⟨b.equivFun u,fun i=>by rw [Basis.equivFun_apply,Basis.equivFun_apply,localFreeBasis_repr]⟩
variable [Fintype ι] [DecidableEq ι]
section Both
variable (bf : Basis ι (Polynomial k) U) (bi : Basis ι (Polynomial k) V)
    (ff : ChartMap (k:=k) false U M) (fi : ChartMap (k:=k) true V M)
    (lf : IsChartLocalization false ff) (li : IsChartLocalization true fi)
def freeTransition : Matrix ι ι (Laurent k) :=
  LinearMap.toMatrix' (((localFreeBasis true bi fi li).equivFun.symm.trans
    (localFreeBasis false bf ff lf).equivFun).toLinearMap)
theorem freeTransition_mulVec (v : ι→Laurent k) :
    freeTransition bf bi ff fi lf li *ᵥ v =
      (localFreeBasis false bf ff lf).equivFun ((localFreeBasis true bi fi li).equivFun.symm v) := by
  rw [←Matrix.toLin'_apply,freeTransition,Matrix.toLin'_toMatrix']
  rfl
theorem freeTransition_unit : IsUnit (freeTransition bf bi ff fi lf li) := by
  let e := (localFreeBasis true bi fi li).equivFun.symm.trans (localFreeBasis false bf ff lf).equivFun
  apply isUnit_iff_exists_inv.mpr
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap,?_⟩
  apply Matrix.toLin'.injective
  rw [freeTransition,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_toMatrix',Matrix.toLin'_one]
  exact e.comp_symm
omit [DecidableEq ι] in
theorem free_finite_iff (v : M) :
    (localFreeBasis false bf ff lf).equivFun v∈finiteLattice k ι ↔ ∃ u : U,ff u=v :=
  coordinate_image false bf ff lf v
theorem free_infinity_iff (v : M) :
    (localFreeBasis false bf ff lf).equivFun v∈transitionLattice (freeTransition bf bi ff fi lf li) ↔
      ∃ w : V,fi w=v := by
  have i : (localFreeBasis true bi fi li).equivFun v∈upperLattice k ι 0 ↔ ∃ w : V,fi w=v :=
    coordinate_image true bi fi li v
  constructor
  · rintro ⟨w,hw,eq⟩
    apply i.mp
    change (freeTransition bf bi ff fi lf li)*ᵥw=(localFreeBasis false bf ff lf).equivFun v at eq
    rw [freeTransition_mulVec] at eq
    have v_eq := (localFreeBasis false bf ff lf).equivFun.injective eq
    have w_eq : w=(localFreeBasis true bi fi li).equivFun v := by
      rw [←v_eq,LinearEquiv.apply_symm_apply]
    exact w_eq ▸ hw
  · intro vi
    refine ⟨_,i.mpr vi,?_⟩
    change (freeTransition bf bi ff fi lf li)*ᵥ((localFreeBasis true bi fi li).equivFun v)=_
    rw [freeTransition_mulVec,LinearEquiv.symm_apply_apply]
theorem free_global_iff (v : M) :
    (localFreeBasis false bf ff lf).equivFun v ∈
      finiteLattice k ι⊓transitionLattice (freeTransition bf bi ff fi lf li) ↔
    (∃ u : U,ff u=v) ∧ (∃ w : V,fi w=v) :=
  and_congr (free_finite_iff bf ff lf v) (free_infinity_iff bf bi ff fi lf li v)
theorem free_boundary_iff (v : M) :
    (localFreeBasis false bf ff lf).equivFun v ∈
      finiteLattice k ι⊔transitionLattice (freeTransition bf bi ff fi lf li) ↔
    ∃ (u : U) (w : V),ff u+fi w=v := by
  let e := (localFreeBasis false bf ff lf).equivFun
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x,hx,y,hy,eq⟩
    have ex : e (e.symm x)∈finiteLattice k ι := by rwa [LinearEquiv.apply_symm_apply]
    have ey : e (e.symm y)∈transitionLattice (freeTransition bf bi ff fi lf li) := by
      rwa [LinearEquiv.apply_symm_apply]
    obtain ⟨u,eu⟩ := (free_finite_iff bf ff lf (e.symm x)).mp ex
    obtain ⟨w,ew⟩ := (free_infinity_iff bf bi ff fi lf li (e.symm y)).mp ey
    refine ⟨u,w,e.injective ?_⟩
    rw [map_add,eu,ew,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    exact eq
  · rintro ⟨u,w,rfl⟩
    exact ⟨e (ff u),(free_finite_iff bf ff lf _).mpr ⟨u,rfl⟩,e (fi w),
      (free_infinity_iff bf bi ff fi lf li _).mpr ⟨w,rfl⟩,(e.map_add _ _).symm⟩
theorem free_euler :
    FiniteDimensional k (H0 (freeTransition bf bi ff fi lf li)) ∧
    FiniteDimensional k (H1 (freeTransition bf bi ff fi lf li)) ∧
    ∃ d : ℤ,(freeTransition bf bi ff fi lf li).det.degree=(d:WithBot ℤ) ∧
      (finrank k (H0 (freeTransition bf bi ff fi lf li)):ℤ)-
        (finrank k (H1 (freeTransition bf bi ff fi lf li)):ℤ)=(Fintype.card ι:ℤ)+d :=
  euler_index _ (freeTransition_unit bf bi ff fi lf li)
end Both
#print axioms isChartLocalization_of_clearing
#print axioms freeTransition_unit
#print axioms free_global_iff
#print axioms free_boundary_iff
#print axioms free_euler
end
end Lower6960.LineEuler

end Merged_R6960LineEulerFree
