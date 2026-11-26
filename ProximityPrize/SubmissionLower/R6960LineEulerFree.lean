import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.R6960LineEulerPolynomial

section Merged6967_R6960LineEulerFree
set_option Elab.async false












set_option Elab.async false

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

end Merged6967_R6960LineEulerFree

section Merged6967_R6966ProofNonlinearMarkDegrees
set_option Elab.async false


set_option Elab.async false

namespace Research6966.NonlinearMarkDegrees
open Polynomial Finset
open NonlinearMarkRows
open scoped Polynomial Differential
noncomputable section
set_option maxHeartbeats 600000
variable {σ F:Type*} [Field F] [Differential F]
attribute [local instance] GenericPhysicalCentre.seeds

/-- Degree across any chosen seed coordinates. Taking one indicator
measures one seed, while weight one measures total seed degree. -/
def cap (w:σ→ℕ) (u:ℕ) (P:Eqn σ F) : Prop :=
  ∀ i,P.coeff i∈MvPolynomial.restrictWeightAtMost w u

private theorem cap_add (w:σ→ℕ) {u:ℕ} {P Q:Eqn σ F} (p:cap w u P) (q:cap w u Q) :
    cap w u (P+Q) := fun i=>by rw [coeff_add];exact Submodule.add_mem _ (p i) (q i)

private theorem cap_sub (w:σ→ℕ) {u:ℕ} {P Q:Eqn σ F} (p:cap w u P) (q:cap w u Q) :
    cap w u (P-Q) := fun i=>by rw [coeff_sub];exact Submodule.sub_mem _ (p i) (q i)

private theorem cap_mul {w:σ→ℕ} {u v:ℕ} {P Q:Eqn σ F} (p:cap w u P) (q:cap w v Q) :
    cap w (u+v) (P*Q) := by
  intro i
  rw [coeff_mul]
  exact Submodule.sum_mem _ (fun ab _=>MvPolynomial.mul_mem_restrictWeightAtMost (p ab.1) (q ab.2))

private theorem cap_C (w:σ→ℕ) (c:F) : cap w 0 (C (MvPolynomial.C c)) := by
  intro i
  by_cases zero:i=0
  · subst i;rw [coeff_C_zero];exact MvPolynomial.C_mem_restrictWeightAtMost _ le_rfl _
  · rw [coeff_C,ite_eq_right zero];exact Submodule.zero_mem _

private theorem cap_X (w:σ→ℕ) : cap (F:=F) w 0 Polynomial.X := by
  intro i
  rw [coeff_X]
  split
  · exact MvPolynomial.C_mem_restrictWeightAtMost _ le_rfl (1:F)
  · exact Submodule.zero_mem _

private theorem cap_pow {w:σ→ℕ} {u:ℕ} {P:Eqn σ F} (p:cap w u P) (j:ℕ) :
    cap w (j*u) (P^j) := by
  induction j with
  | zero=>simpa only [pow_zero,zero_mul,map_one] using cap_C w (1:F)
  | succ j ih=>rw [pow_succ,Nat.succ_mul];exact cap_mul ih p

private theorem cap_deriv {w:σ→ℕ} {u:ℕ} {P:Eqn σ F} (p:cap w u P) :
    cap w u P.derivative := by
  intro i
  rw [coeff_derivative]
  rw [show (↑i+1:MvPolynomial σ F)=MvPolynomial.C (i+1:F) by simp,
    mul_comm,←MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (p _)

private theorem cap_dx {w:σ→ℕ} {u:ℕ} {P:Eqn σ F} (p:cap w u P) :
    cap w u (Differential.mapCoeffs P) := by
  intro i
  rw [Differential.coeff_mapCoeffs]
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro e he
  apply MvPolynomial.mem_restrictWeightAtMost.mp (p i) e
  apply MvPolynomial.mem_support_iff.mpr
  intro zero
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [GenericPhysicalCentre.deriv_coeff,zero,map_zero])

theorem numerator_seeds {w:σ→ℕ} {u:ℕ} {A B:Eqn σ F} (ha:cap w u A) (hb:cap w u B) (j:ℕ) :
    cap w ((2*j+1)*u) (QuadraticWeight.numerator A B j) := by
  have dir {P:Eqn σ F} {l:ℕ} (p:cap w l P) :
      cap w (u+l) (A*Differential.mapCoeffs P+B*P.derivative) :=
    cap_add _ (cap_mul ha (cap_dx p)) (cap_mul hb (cap_deriv p))
  induction j with
  | zero=>simpa [QuadraticWeight.numerator] using hb
  | succ j ih=>
    rw [QuadraticWeight.numerator]
    apply cap_sub
    · convert cap_mul ha (dir ih) using 1 <;> ring
    · have constant:cap w 0 ((↑(2*j+1):Eqn σ F)):=by
        simpa only [map_natCast] using cap_C w (↑(2*j+1):F)
      convert cap_mul (cap_mul constant ih) (dir ha) using 1 <;> ring

private theorem dx_degree (P:Eqn σ F) : (Differential.mapCoeffs P).natDegree≤P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n above
  rw [Differential.coeff_mapCoeffs,coeff_eq_zero_of_natDegree_lt above,map_zero]

theorem numerator_ordinate {r:ℕ} (rp:1≤r) {A B:Eqn σ F} (ha:A.natDegree≤r) (hb:B.natDegree≤r+1) (j:ℕ) :
    (QuadraticWeight.numerator A B j).natDegree≤(2*j+1)*r+1 := by
  have dir {P:Eqn σ F} {l:ℕ} (pos:0<l) (p:P.natDegree≤l) :
      (A*Differential.mapCoeffs P+B*P.derivative).natDegree≤r+l := by
    apply (natDegree_add_le ..).trans (max_le _ _)
    · exact natDegree_mul_le.trans (Nat.add_le_add ha ((dx_degree P).trans p))
    · exact (natDegree_mul_le.trans (Nat.add_le_add hb ((natDegree_derivative_le P).trans
        (Nat.sub_le_sub_right p 1)))).trans (by omega)
  induction j with
  | zero=>simpa [QuadraticWeight.numerator] using hb
  | succ j ih=>
    rw [QuadraticWeight.numerator]
    apply (natDegree_sub_le ..).trans (max_le _ _)
    · exact (natDegree_mul_le.trans (Nat.add_le_add ha (dir (Nat.succ_pos _) ih))).trans (by ring_nf;omega)
    · have num:((↑(2*j+1):Eqn σ F)).natDegree=0:=natDegree_natCast _
      have left:=natDegree_mul_le.trans (Nat.add_le_add num.le ih)
      exact (natDegree_mul_le.trans (Nat.add_le_add left (dir rp ha))).trans (by ring_nf;omega)

private theorem common_seed {w:σ→ℕ} {u:ℕ} {A B:Eqn σ F} (ha:cap w u A) (hb:cap w u B)
    (d j:ℕ) (le:j≤d) : cap w ((2*d-1)*u) (coeffRow A B d j) := by
  cases j with
  | zero=>simpa only [coeffRow,zero_add] using cap_mul (cap_X w) (cap_pow ha (2*d-1))
  | succ j=>
    have eq:(2*j+1)*u+(2*d-1-(2*j+1))*u=(2*d-1)*u:=by rw [←Nat.add_mul];congr 1;omega
    simpa only [coeffRow,eq] using cap_mul (numerator_seeds ha hb j) (cap_pow ha (2*d-1-(2*j+1)))

theorem node_seeds {w:σ→ℕ} {u:ℕ} {A B:Eqn σ F} (ha:cap w u A) (hb:cap w u B)
    (d:ℕ) (c x received:F) : cap w ((2*d-1)*u) (node A B d c x received) := by
  unfold node
  apply cap_sub
  · intro i
    rw [finsetSum_coeff]
    apply Submodule.sum_mem
    intro j hj
    exact (show cap w ((2*d-1)*u) _ from by
      simpa only [zero_add] using cap_mul (cap_C w ((x-c)^j/(j.factorial:F)))
        (common_seed ha hb d j (Nat.le_of_lt_succ (mem_range.mp hj)))) i
  · simpa only [zero_add] using cap_mul (cap_C w received) (cap_pow ha (2*d-1))

theorem node_ordinate {r:ℕ} (rp:1≤r) {A B:Eqn σ F} (ha:A.natDegree≤r) (hb:B.natDegree≤r+1)
    (d:ℕ) (c x received:F) : (node A B d c x received).natDegree≤(2*d-1)*r+1 := by
  have bound (j:ℕ) (le:j≤d) : (coeffRow A B d j).natDegree≤(2*d-1)*r+1 := by
    cases j with
    | zero=>exact (natDegree_mul_le.trans (Nat.add_le_add natDegree_X.le
        ((natDegree_pow_le ..).trans (Nat.mul_le_mul_left _ ha)))).trans (by omega)
    | succ j=>
      have add:2*j+1+(2*d-1-(2*j+1))=2*d-1:=by omega
      have cost:=natDegree_mul_le.trans (Nat.add_le_add (numerator_ordinate rp ha hb j)
        ((natDegree_pow_le ..).trans (Nat.mul_le_mul_left (2*d-1-(2*j+1)) ha)))
      simpa only [coeffRow] using cost.trans (show (2*j+1)*r+1+(2*d-1-(2*j+1))*r≤(2*d-1)*r+1 from
        by calc
          _ = ((2*j+1)+(2*d-1-(2*j+1)))*r+1 := by ring
          _ ≤ _ := by rw [add])
  unfold node
  apply (natDegree_sub_le ..).trans (max_le _ _)
  · apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_C_mul_le _ _).trans (bound j (Nat.le_of_lt_succ (mem_range.mp hj)))
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le ..).trans ((Nat.mul_le_mul_left _ ha).trans (by omega)))

#print axioms node_seeds
#print axioms node_ordinate
end
end Research6966.NonlinearMarkDegrees

end Merged6967_R6966ProofNonlinearMarkDegrees

section Merged6967_R6966ProofPadeRank
set_option Elab.async false




set_option Elab.async false

set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 12
namespace Research6966.PadeRank
open Polynomial Finset Module
open Pade (Row totalJet totalJet_le totalJet_mul)
open scoped Polynomial
noncomputable section

/-- Bounds are exclusive, so empty quotient boxes have dimension zero. -/
def positions (b j : ℕ) : Finset (ℕ×ℕ) :=
  ((range j) ×ˢ (range b)).filter (fun t=>t.1+t.2<b)

private theorem position {b j l i:ℕ} :
    (l,i)∈positions b j ↔ l<j ∧ i+l<b := by
  simp [positions,Nat.add_comm];omega

variable {K : Type*} [Field K]
abbrev Plane (K:Type*) [Semiring K] := K[X][X]

def box (K:Type*) [Field K] (b j:ℕ) : Submodule K (Plane K) where
  carrier := {P | ∀ l i, (l,i)∉positions b j → (P.coeff l).coeff i=0}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hp hq l i out
    simp only [coeff_add,hp l i out,hq l i out,add_zero]
  smul_mem' := by
    intro c P hp l i out
    simp [hp l i out]

private def readBox (b j:ℕ) : box K b j →ₗ[K] (positions b j→K) where
  toFun P x:=((P.val.coeff x.val.1).coeff x.val.2)
  map_add' := by intro x y;funext i;simp
  map_smul' := by intro r x;funext i;simp

private theorem read_injective (b j:ℕ) : Function.Injective (readBox (K:=K) b j) := by
  intro P Q eq
  apply Subtype.ext
  ext l i
  by_cases yes:(l,i)∈positions b j
  · exact congrFun eq ⟨(l,i),yes⟩
  · rw [P.property l i yes,Q.property l i yes]

private def pack (b j:ℕ) (f:positions b j→K) : Plane K :=
  ∑ s:positions b j,monomial s.val.1 (monomial s.val.2 (f s))

private theorem pack_coeff (b j:ℕ) (f:positions b j→K) (l i:ℕ) :
    ((pack b j f).coeff l).coeff i = if h:(l,i)∈positions b j then f ⟨(l,i),h⟩ else 0 := by
  classical
  simp only [pack,finsetSum_coeff]
  have zero (s:positions b j) (ne:s.val≠(l,i)) :
      (((monomial s.val.1 (monomial s.val.2 (f s)) : Plane K).coeff l).coeff i)=0 := by
    by_cases h:s.val.1=l
    · have q:s.val.2≠i:=fun e=>ne (Prod.ext h e)
      simp [coeff_monomial,h,q]
    · simp [coeff_monomial,h]
  split
  · rename_i yes
    let s:positions b j:=⟨(l,i),yes⟩
    rw [Finset.sum_eq_single s]
    · simp [s,coeff_monomial]
    · intro t _ ne;exact zero t (fun h=>ne (Subtype.ext h))
    · simp
  · rename_i no
    exact sum_eq_zero (fun s _=>zero s (fun eq=>no (eq ▸ s.property)))

instance (b j:ℕ) : FiniteDimensional K (box K b j) :=
  Module.Finite.of_injective (readBox b j) (read_injective b j)

theorem box_dimension (b j:ℕ) : finrank K (box K b j)=(positions b j).card := by
  classical
  have onto : Function.Surjective (readBox (K:=K) b j) := by
    intro f
    have member:pack b j f∈box K b j := by
      intro l i no;rw [pack_coeff,dite_eq_right no]
    refine ⟨⟨_,member⟩,?_⟩
    funext s
    change ((pack b j f).coeff s.val.1).coeff s.val.2=_
    rw [pack_coeff,dite_eq_left s.property]
  have eq:=LinearEquiv.ofBijective (readBox (K:=K) b j) ⟨read_injective b j,onto⟩
  simpa using eq.finrank_eq

theorem mem_box {P:Plane K} {b j:ℕ} (nz:P≠0) :
    P∈box K b j ↔ totalJet P<b ∧ P.natDegree<j := by
  constructor
  · intro inside
    have top₁ : P.coeff P.natDegree≠0 := by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr nz
    have top₂ : (P.coeff P.natDegree).coeff (P.coeff P.natDegree).natDegree≠0 := by
      rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr top₁
    have atTop := position.mp (show (_,_)∈positions b j from by by_contra no;exact top₂ (inside _ _ no))
    have bound:totalJet P≤b-1 := (totalJet_le _ _).mpr (by
      intro l i ne
      have hit := position.mp (show (l,i)∈positions b j from by by_contra no;exact ne (inside l i no))
      omega)
    exact ⟨by omega,atTop.1⟩
  · rintro ⟨total,slope⟩ l i no
    by_contra ne
    have sum := (totalJet_le P _).mp le_rfl l i ne
    have active:P.coeff l≠0 := by intro eq;exact ne (by rw [eq,coeff_zero])
    have top:=le_natDegree_of_ne_zero active
    exact no (position.mpr ⟨by omega,by omega⟩)

private def restriction (A B:K[X]) (j:ℕ) : Plane K →ₗ[K] K[X] where
  toFun Q:= ∑ i∈range j,Q.coeff i*B^i*A^(j-1-i)
  map_add' := by intro P Q;simp [add_mul,sum_add_distrib]
  map_smul' := by intro r P;simp [Finset.smul_sum]

private theorem restriction_eq (A B:K[X]) {Q:Plane K} {j:ℕ} (hj:Q.natDegree<j) :
    restriction A B j Q=TerminalProjection.cleared A B Q (j-1) := by
  rw [TerminalProjection.cleared,Q.sum_over_range' (fun _=>by simp) j hj]
  rfl

#print axioms box_dimension
#print axioms mem_box

private theorem restriction_zero (G:Row K) (gp:G.primitive) {P:Plane K} {j:ℕ}
    (cap:P.natDegree<j) (dv:G.polynomial∣P) : restriction G.a G.b j P=0 := by
  rw [restriction_eq G.a G.b cap]
  let L:=FractionRing K[X]
  let f:=algebraMap K[X] L
  have inj:=IsFractionRing.injective K[X] L
  have den:f G.a≠0 := (map_ne_zero_iff _ inj).mpr gp.1
  let t:=f G.b/f G.a
  have eq : f G.a*t=f G.b := by dsimp [t];field_simp
  apply inj
  rw [map_zero,TerminalProjection.map_cleared f _ _ _ eq _ _ (by omega)]
  obtain ⟨q,rfl⟩:=dv
  have root:eval₂ f t G.polynomial=0 := by simp [Row.polynomial,eq]
  rw [eval₂_mul,root,zero_mul,mul_zero]

private theorem mem_quotient_box {G:Row K} (gp:G.primitive) {Q:Plane K} {b j:ℕ}
    (mem:G.polynomial*Q∈box K b j) : Q∈box K (b-G.graphDegree) (j-1) := by
  by_cases z:Q=0
  · rw [z];exact (box ..).zero_mem
  obtain ⟨first,second⟩ := (mem_box (mul_ne_zero (G.polynomial_ne gp) z)).mp mem
  rw [totalJet_mul (G.polynomial_ne gp) z,G.total_polynomial gp] at first
  rw [natDegree_mul (G.polynomial_ne gp) z,G.slope_degree gp] at second
  exact (mem_box z).mpr ⟨by omega,by omega⟩

private theorem mem_product_box {G:Row K} (gp:G.primitive) {Q:Plane K} {b j:ℕ}
    (mem:Q∈box K (b-G.graphDegree) (j-1)) : G.polynomial*Q∈box K b j := by
  by_cases z:Q=0
  · rw [z,mul_zero];exact (box ..).zero_mem
  obtain ⟨first,second⟩ := (mem_box z).mp mem
  apply (mem_box (mul_ne_zero (G.polynomial_ne gp) z)).mpr
  rw [totalJet_mul (G.polynomial_ne gp) z,G.total_polynomial gp,
    natDegree_mul (G.polynomial_ne gp) z,G.slope_degree gp]
  exact ⟨by omega,by omega⟩

private theorem slope_lt {Q:Plane K} {b j:ℕ} (pos:0<j) (h:Q∈box K b j) : Q.natDegree<j := by
  by_cases z:Q=0
  · simpa [z] using pos
  exact ((mem_box z).mp h).2

private theorem effective_slope {Q:Plane K} {b j:ℕ} (bp:0<b) (jp:0<j) (h:Q∈box K b j) :
    Q.natDegree < min b j := by
  by_cases z:Q=0
  · simp only [z,natDegree_zero];exact lt_min bp jp
  have ⟨bt,sj⟩ := (mem_box z).mp h
  have ne:Q.coeff Q.natDegree≠0 := by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr z
  have le:=(totalJet_le Q _).mp le_rfl Q.natDegree (Q.coeff Q.natDegree).natDegree
    (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr ne)
  exact lt_min (by omega) sj

private theorem range_slice {G:Row K} (gp:G.primitive) (b j:ℕ) (bp:0<b) (jp:0<j) :
    finrank K ((restriction G.a G.b (min b j)).domRestrict (box K b j)).range ≤
      (positions b j).card - (positions (b-G.graphDegree) (j-1)).card := by
  classical
  let V:=box K b j
  let T:=box K (b-G.graphDegree) (j-1)
  have finiteV : FiniteDimensional K ↥V := by dsimp [V]; infer_instance
  let p:V→ₗ[K]K[X]:=(restriction G.a G.b (min b j)).comp V.subtype
  let mult: T →ₗ[K] V :=
    (((Algebra.lmul K (Plane K) G.polynomial).comp T.subtype).codRestrict V (fun q=>mem_product_box gp q.property))
  let inKer:T→ₗ[K]p.ker:=mult.codRestrict _ (by
    intro q
    change restriction G.a G.b (min b j) (G.polynomial*q.val)=0
    exact restriction_zero G gp (effective_slope bp jp (mem_product_box gp q.property)) (dvd_mul_right ..))
  have inject: Function.Injective inKer := by
    intro x y eq
    exact Subtype.ext (mul_left_cancel₀ (G.polynomial_ne gp)
      (congrArg (fun z:p.ker=>(z.val:Plane K)) eq))
  have finiteK : FiniteDimensional K ↥p.ker := Module.Finite.of_injective p.ker.subtype p.ker.subtype_injective
  have size:=LinearMap.finrank_le_finrank_of_injective inject
  have rank:=LinearMap.finrank_range_add_finrank_ker (K:=K) (V:=↥V) (V₂:=K[X]) p
  change finrank K T≤finrank K p.ker at size
  change finrank K p.range+finrank K p.ker=finrank K V at rank
  change finrank K p.range≤_
  rw [show finrank K T=(positions (b-G.graphDegree) (j-1)).card from box_dimension ..] at size
  rw [show finrank K V=(positions b j).card from box_dimension ..] at rank
  omega

private theorem divisible_dimension (U:Submodule K K[X]) (D:K[X]) (dn:D≠0) (length:ℕ)
    (div:∀P∈U,D∣P) (cap:∀P∈U,P≠0 → P.natDegree<length) :
    finrank K U≤length-D.natDegree := by
  let T:=U.comap (Algebra.lmul K K[X] D)
  let mult:T→ₗ[K]U:=((Algebra.lmul K K[X] D).comp T.subtype).codRestrict U (fun q=>q.property)
  have bij:Function.Bijective mult := by
    constructor
    · intro x y eq;exact Subtype.ext (mul_left_cancel₀ dn (congrArg Subtype.val eq))
    · intro p
      obtain ⟨q,eq⟩:=div p.val p.property
      exact ⟨⟨q,by change D*q∈U;rw [←eq];exact p.property⟩,Subtype.ext eq.symm⟩
  let L:=length-D.natDegree
  have sub:T≤degreeLT K L := by
    intro q hq
    by_cases zero:q=0
    · rw [zero];exact (degreeLT K L).zero_mem
    have paid:=cap (D*q) hq (mul_ne_zero dn zero)
    rw [natDegree_mul dn zero] at paid
    apply (mem_degreeLT).mpr
    rw [degree_eq_natDegree zero,Nat.cast_lt]
    dsimp [L];omega
  rw [←(LinearEquiv.ofBijective mult bij).finrank_eq]
  apply (Submodule.finrank_mono sub).trans
  have eq:finrank K (degreeLT K L)=L := by simpa using (degreeLTEquiv K L).finrank_eq
  exact eq.le

/-- Number of independent restrictions remaining after the n independent
ordinate conditions, in an exclusive (b,j) box. -/
def imageAllowance (b j a n k:ℕ) := b+(a-1)*min (b-1) (j-1) - n*k

private theorem restricted_range {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀ y∈ys,G.err v y=0) (b j k:ℕ) (bp:0<b) (jp:0<j)
    (V:Submodule K (Plane K)) (sub:V≤box K b j)
    (contact:∀ (Q:Plane K),Q∈V → ∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k) :
    finrank K ((restriction G.a G.b (min b j)).domRestrict V).range ≤ imageAllowance b j G.graphDegree ys.card k := by
  classical
  let p:V→ₗ[K] K[X]:=(restriction G.a G.b (min b j)).comp V.subtype
  let d:K[X]:=(∏ y∈ys,(«X»-C y))^k
  have nz:d≠0:=pow_ne_zero _ (prod_ne_zero_iff.mpr (fun y _=>X_sub_C_ne_zero y))
  have dn:d.natDegree=ys.card*k := by
    dsimp [d];rw [natDegree_pow,natDegree_prod _ _ (fun y _=>X_sub_C_ne_zero y)]
    simp [Nat.mul_comm]
  let n:=b+(G.graphDegree-1)*min (b-1) (j-1)
  change finrank K p.range≤n-ys.card*k
  rw [←dn]
  apply divisible_dimension p.range d nz n
  · rintro _ ⟨Q,rfl⟩
    have fit:=effective_slope bp jp (sub Q.property)
    change d∣restriction G.a G.b (min b j) Q.val
    rw [restriction_eq G.a G.b fit]
    apply TerminalProjection.all_sheets G.a G.b _ ys v _ k (by omega)
    intro y hy
    have hit:=sub_eq_zero.mp (graph y hy)
    have regular:G.a.eval y≠0 := by
      intro zero
      change G.a.eval y*v y=G.b.eval y at hit
      obtain ⟨l,w,bz⟩:=gp.2
      have test:=congrArg (eval y) bz
      simp [←hit,zero] at test
    exact ⟨regular,hit,contact Q.val Q.property y hy⟩
  · rintro _ ⟨Q,rfl⟩ pn
    have qn:Q.val≠0:=by intro z;apply pn;change restriction G.a G.b (min b j) Q.val=0;rw [z,map_zero]
    obtain ⟨bt,sj⟩ := (mem_box qn).mp (sub Q.property)
    have fit := effective_slope bp jp (sub Q.property)
    change (restriction G.a G.b (min b j) Q.val).natDegree<n
    rw [restriction_eq G.a G.b fit]
    have width:=TerminalProjection.ordinate_width G.a G.b Q.val ((min b j)-1) G.graphDegree (b-1)
      (by omega) (by unfold Row.graphDegree;omega) (by unfold Row.graphDegree;omega)
      (le_max_right ..) (fun i hi=>by
        have ne:=mem_support_iff.mp hi
        have bh:=(totalJet_le Q.val _).mp le_rfl i (Q.val.coeff i).natDegree
          (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr ne)
        omega)
    dsimp [n];rw [show min (b-1) (j-1)=min b j-1 by omega];omega

/-- Rank gained by successively restricting to the same graph. The two
shape arguments are exclusive lengths. -/
def gain (a n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,_,_=>0
  | k+1,b,j=>
    if b=0 ∨ j=0 then 0 else
      (positions b j).card - (positions (b-a) (j-1)).card - imageAllowance b j a n (k+1) +
        gain a n k (b-a) (j-1)

/-- The recurrence bounds any subspace of the actual contact kernel, over
any field. Thus the choices of slope and chart at the selected ordinates
do not enter the numerical rank receipt. -/
theorem gain_bound {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀ y∈ys,G.err v y=0) (k b j:ℕ) (V:Submodule K (Plane K))
    (sub:V≤box K b j) (contact:∀ Q∈V,∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k) :
    finrank K V + gain G.graphDegree ys.card k b j ≤ (positions b j).card := by
  classical
  have basic := (Submodule.finrank_mono sub).trans_eq (box_dimension b j)
  induction k generalizing b j V with
  | zero => simpa [gain] using basic
  | succ k ih =>
    by_cases empty : b=0 ∨ j=0
    · simpa [gain,empty] using basic
    have bp:0<b:=by omega
    have jp:0<j:=by omega
    let a:=G.graphDegree
    let cut:=restriction G.a G.b (min b j)
    let f:=cut.domRestrict V
    let T:Submodule K (Plane K):=(V ⊓ cut.ker).comap (Algebra.lmul K (Plane K) G.polynomial)
    have fit:T≤box K (b-a) (j-1) := by
      intro Q h
      exact mem_quotient_box gp (sub h.1)
    have newContact : ∀ Q∈T,∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k := by
      intro Q h y hy
      have hit:=sub_eq_zero.mp (graph y hy)
      have reg:G.a.eval y≠0 := by
        intro z
        change G.a.eval y*v y=G.b.eval y at hit
        obtain ⟨l,w,bz⟩:=gp.2
        have bad:=congrArg (eval y) bz
        simp [←hit,z] at bad
      exact PadeJetOrder.strip G.a G.b Q y (v y) k reg hit (contact _ h.1 y hy)
    let mult:T→ₗ[K]V:=((Algebra.lmul K (Plane K) G.polynomial).comp T.subtype).codRestrict V
      (fun q=>q.property.1)
    let into:T→ₗ[K]f.ker:=mult.codRestrict _ (fun q=>q.property.2)
    have bij:Function.Bijective into := by
      constructor
      · intro x y eq
        exact Subtype.ext (mul_left_cancel₀ (G.polynomial_ne gp) (congrArg (fun z:f.ker=>(z.val:Plane K)) eq))
      · intro p
        have div:G.polynomial∣(p.val:Plane K) := by
          by_contra nd
          have hj:=effective_slope bp jp (sub p.val.property)
          have no:=TerminalProjection.nonzero_of_avoids G.a G.b (p.val:Plane K) (min b j-1)
            (by omega) gp.1 (G.polynomial_primitive gp) nd
          apply no
          rw [←restriction_eq G.a G.b hj]
          exact p.property
        obtain ⟨q,eq⟩:=div
        have qt:q∈T := by
          change G.polynomial*q∈V ⊓ cut.ker
          rw [←eq]
          exact ⟨p.val.property,p.property⟩
        exact ⟨⟨q,qt⟩,Subtype.ext (Subtype.ext eq.symm)⟩
    have kerRank:finrank K T=finrank K f.ker := (LinearEquiv.ofBijective into bij).finrank_eq
    have finV : FiniteDimensional K ↥V := Module.Finite.of_injective (Submodule.inclusion sub) (Submodule.inclusion_injective sub)
    have dim:=LinearMap.finrank_range_add_finrank_ker (K:=K) (V:=↥V) (V₂:=K[X]) f
    have imageFits : f.range≤(cut.domRestrict (box K b j)).range := by
      rintro _ ⟨x,rfl⟩;exact ⟨⟨x.val,sub x.property⟩,rfl⟩
    have slice:finrank K f.range≤(positions b j).card-(positions (b-a) (j-1)).card :=
      (Submodule.finrank_mono imageFits).trans (range_slice gp b j bp jp)
    have roots:=restricted_range gp ys v graph b j (k+1) bp jp V sub contact
    change finrank K f.range ≤ imageAllowance b j a ys.card (k+1) at roots
    have previous:=ih (b-a) (j-1) T fit newContact
      ((Submodule.finrank_mono fit).trans_eq (box_dimension (b-a) (j-1)))
    have contain : positions (b-a) (j-1) ⊆ positions b j := by
      rintro ⟨l,i⟩ h
      have h':=position.mp h
      exact position.mpr ⟨by omega,by omega⟩
    have count:=card_le_card contain
    rw [gain,ite_eq_right empty]
    change finrank K V+((positions b j).card-(positions (b-a) (j-1)).card-
      imageAllowance b j a ys.card (k+1)+gain a ys.card k (b-a) (j-1))≤_
    change finrank K T+gain a ys.card k (b-a) (j-1)≤_ at previous
    omega

#print axioms gain_bound
end
end Research6966.PadeRank

end Merged6967_R6966ProofPadeRank

section Merged6967_R6966ProofWordSurfacePrice
set_option Elab.async false



set_option Elab.async false

namespace Research6966.WordSurfacePrice
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation WordSurfaceCount WordSurfaceMarks
variable {K ι I :Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype ι]
noncomputable section
set_option maxHeartbeats 800000

private theorem box_loss (x y z a b c:ℕ) (ha:a≤x) (hb:b≤y) (hc:c≤z) :
    x*y*z ≤ (x-a)*(y-b)*(z-c) + (a*y*z+b*x*z+c*x*y) := by
  obtain ⟨x,rfl⟩:=Nat.exists_eq_add_of_le ha
  obtain ⟨y,rfl⟩:=Nat.exists_eq_add_of_le hb
  obtain ⟨z,rfl⟩:=Nat.exists_eq_add_of_le hc
  simp only [Nat.add_sub_cancel_left]
  nlinarith only [Nat.zero_le (a*b*c),Nat.zero_le (a*b*z),Nat.zero_le (a*c*y),Nat.zero_le (b*c*x)]

private theorem two_choose (k:ℕ) : k^2≤2*(k+1).choose 2 := by
  have eq:=Nat.choose_succ_right_eq (k+1) 1
  rw [Nat.choose_one_right,Nat.add_sub_cancel] at eq
  nlinarith

def side (n a d height:ℕ) : ℕ := (n-a)*height+(a-d)

def mixed (v h:Fin 3→ℕ) : ℕ:=v 0*h 1*h 2+v 1*h 0*h 2+v 2*h 0*h 1

/-- A word family on one trivariate equation costs its mixed tridegree
times the square of the agreement ratio. The argument counts words
even if the parameter-map fibre has positive dimension or the surface
is singular at a marked lift. -/
theorem count (points:ι→Fin 3→K) (rows:I→Pol (Fin 3) K) (H:Pol (Fin 3) K) (hn:H≠0)
    (onSurface:∀ x,eval (points x) H=0) (v height:Fin 3→ℕ) (vp:∀ i,H.degreeOf i≤v i)
    (rp:∀ j i,(rows j).degreeOf i≤height i)
    (A d:ℕ) (gap:d<A) (enough:∀ z,A≤(hits (points z) rows).card)
    (shared:∀ x y,x≠y → ((hits (points x) rows)∩(hits (points y) rows)).card≤d) :
    Fintype.card ι*(A-d)^2 ≤ 2*mixed v (fun i=>side (Fintype.card I) A d (height i)) := by
  classical
  let n:=Fintype.card I
  let delta:=A-d
  let t:=2+(∑i,v i)
  let k:=t*delta
  let beta (i:Fin 3):=(n-A)*height i+delta
  let cap (i:Fin 3):=t*(n-A)*height i+(k-1)
  let small (i:Fin 3):=cap i-v i
  have dt:0<delta:=by dsimp [delta];omega
  have tp:2≤t:=by dsimp [t];omega
  have tk:t≤k:=by simpa only [mul_one] using Nat.mul_le_mul_left t (show 1≤delta from dt)
  have k2:2≤k:=tp.trans tk
  have full (i:Fin 3):cap i+1=t*beta i := by
    dsimp only [cap,beta]
    rw [Nat.add_assoc,Nat.sub_add_cancel (by omega)]
    dsimp [k];ring
  have vi (i:Fin 3):v i≤cap i := by
    have vv:v i≤∑j,v j:=Finset.single_le_sum (fun j _=>Nat.zero_le (v j)) (Finset.mem_univ i)
    dsimp only [cap];dsimp only [t] at tk;omega
  have sm (i:Fin 3):small i+1=t*beta i-v i := by
    dsimp only [small];rw [←full];have:=vi i;omega
  obtain ⟨seps,degree,own,other⟩:=separators points rows height rp A d t enough shared
  have onto:=interpolate points k (by omega) (fun j=>t*(n-A)*height j) seps degree own other
  have jets:=trivariate_budget points (k-2) cap small H hn (fun i=>by
    dsimp only [small];have:=vi i;have:=vp i;omega) onSurface (by
      rw [show k-2+2=k by omega];exact onto)
  rw [show k-2+3=k+1 by omega] at jets
  simp only [sm,full,Fin.prod_univ_three] at jets
  have fits (i:Fin 3):v i≤t*beta i:=by rw [←full];exact (vi i).trans (Nat.le_succ _)
  have loss:=box_loss (t*beta 0) (t*beta 1) (t*beta 2) (v 0) (v 1) (v 2) (fits 0) (fits 1) (fits 2)
  let weight:=v 0*beta 1*beta 2+v 1*beta 0*beta 2+v 2*beta 0*beta 1
  have lead:Fintype.card ι*(k+1).choose 2≤t^2*weight := by
    dsimp only [weight]
    nlinarith only [jets,loss]
  have chooseBound:=Nat.mul_le_mul_left (Fintype.card ι) (two_choose k)
  have cancel:Fintype.card ι*delta^2≤2*weight := by
    have scaled:t^2*(Fintype.card ι*delta^2)≤t^2*(2*weight) := by
      dsimp only [k] at chooseBound
      nlinarith only [chooseBound,lead]
    exact Nat.le_of_mul_le_mul_left scaled (by positivity)
  exact cancel

#print axioms count

theorem word_overlap {σ:Type*} [Fintype σ] [DecidableEq σ] (points:ι→σ→K) (rows:I→Pol σ K)
    (nodes:I→K) (distinct:Function.Injective nodes) (received:I→K)
    (words:ι→Polynomial K) (unique:Function.Injective words) (d:ℕ) (degree:∀ z,(words z).natDegree≤d)
    (detect:∀ z i,eval (points z) (rows i)=0 ↔ (words z).eval (nodes i)=received i) :
    ∀ x y,x≠y → ((hits (points x) rows)∩(hits (points y) rows)).card≤d := by
  classical
  intro x y ne
  let T:=hits (points x) rows ∩ hits (points y) rows
  have nz:words x-words y≠0:=sub_ne_zero.mpr (fun e=>ne (unique e))
  have sub:T.image nodes ⊆ (words x-words y).roots.toFinset := by
    rintro z hz
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hz
    obtain ⟨hx,hy⟩:=mem_inter.mp hi
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots nz).mpr
    change (words x-words y).eval (nodes i)=0
    rw [Polynomial.eval_sub,(detect x i).mp (hit.mp hx),(detect y i).mp (hit.mp hy),sub_self]
  change T.card≤d
  rw [←card_image_of_injective T distinct]
  exact (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
    ((Polynomial.natDegree_sub_le ..).trans (max_le (degree x) (degree y)))))


/-- Distinct polynomial words supply the pairwise constraint themselves.
The row equations only need to detect agreement on the chosen lifts. -/
theorem count_words (points:ι→Fin 3→K) (rows:I→Pol (Fin 3) K) (H:Pol (Fin 3) K) (hn:H≠0)
    (onSurface:∀ x,eval (points x) H=0) (v height:Fin 3→ℕ) (vp:∀ i,H.degreeOf i≤v i)
    (rp:∀ j i,(rows j).degreeOf i≤height i)
    (nodes:I→K) (distinct:Function.Injective nodes) (received:I→K)
    (words:ι→Polynomial K) (unique:Function.Injective words) (A d:ℕ) (gap:d<A)
    (degree:∀ z,(words z).natDegree≤d)
    (detect:∀ z i,eval (points z) (rows i)=0 ↔ (words z).eval (nodes i)=received i)
    (enough:∀ z,A≤(hits (points z) rows).card) :
    Fintype.card ι*(A-d)^2 ≤ 2*mixed v (fun i=>side (Fintype.card I) A d (height i)) := by
  classical
  apply count points rows H hn onSurface v height vp rp A d gap enough
  exact word_overlap points rows nodes distinct received words unique d degree detect

#print axioms count_words
end
end Research6966.WordSurfacePrice

end Merged6967_R6966ProofWordSurfacePrice
