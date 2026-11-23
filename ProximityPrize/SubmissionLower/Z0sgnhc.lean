import ProximityPrize.SubmissionLower.ZE3M1Qc
import ProximityPrize.SubmissionLower.ZmWYYoa
import ProximityPrize.SubmissionLower.Z1qPXJc
import ProximityPrize.SubmissionLower.Zg1hxlb
import ProximityPrize.SubmissionLower.Z8duOVc
set_option Elab.async false
open _root_ renaming Algebra.TensorProduct.comm → zOQ, Algebra.TensorProduct.comm_tmul → zrb, Algebra.TensorProduct.includeRight → zgi, CommRing → za6, Field → zrc, Finsupp.sum → zt1, Finsupp.weight_apply → zDM, Fintype → z85, Ideal → znc, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, IsLocalization.map_eq_zero_iff → zw9, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.map → zDK, MvPolynomial.map_X → z7N, MvPolynomial.ringHom_ext → zXT, Nat.add_le_add_right → zlr, Nat.le_add_right → z8K, Polynomial.mapRingHom → zhd, RingHom.comp_apply → zQb, RingHom.ker → zdq
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_6_1
noncomputable section
open P5_7_3_3_4_1_6 MvPolynomial
open private mem_radical_annihilator_of_torsion pow_inf_eq_bot from ProximityPrize.SubmissionLower.ZmWYYoa
variable {F:Type} [zrc F] {n:ℕ}
private def ke (s :Bool) :znc (Dq F n) :=
  Ideal.span (z9v '' {v :HomVars n | block v=s})
private theorem cutDegree_weight (s :Bool) (v :HomVars n) :
    an0 s (weight v)=if block v=s then 1 else 0:= by
  cases s <;> cases h:block v <;> simp [an0,weight,h,step,seedStep,coeffStep]
private theorem homogeneous_mem_cutIdeal_pow (s :Bool) {p:Dq F n} {d:ℕ×ℕ}
    (hp:p.IsWeightedHomogeneous weight d) :p∈ke s^an0 s d:= by
  classical
  rw [p.as_sum]
  apply Ideal.sum_mem
  intro m hm
  have hwt: (m.sum fun v i=>i•an0 s (weight v))=an0 s d:= by
    rw [← hp (mem_support_iff.mp hm)]
    cases s <;> simp [an0,zDM,zt1,Prod.fst_sum,Prod.snd_sum]
  rw [monomial_eq]
  apply Ideal.mul_mem_left
  rw [Finsupp.prod,← hwt,zt1,← Finset.prod_pow_eq_pow_sum]
  apply Ideal.prod_mem_prod
  intro v _
  rw [cutDegree_weight]
  split
  · rename_i hv
    have hvar :z9v v∈(ke s :znc (Dq F n)) :=
      Ideal.subset_span ⟨v,hv,rfl⟩
    simpa only [Nat.nsmul_eq_mul,Nat.mul_one] using Ideal.pow_mem_pow hvar (m v)
  · simp only [nsmul_zero,pow_zero,Ideal.one_eq_top,Submodule.mem_top]
theorem eventual_injective_of_torsion (J:znc (Dq F n)) (s :Bool) (g:Dq F n)
    (h : ∀ v :HomVars n,block v=s →
      ∀ z :Dq F n,g*z∈J → ∃ m:ℕ,z9v v^m*z∈J) :
    ∃ N :ℕ,∀ d:ℕ×ℕ,N≤an0 s d → ∀ z :Dq F n,
      z.IsWeightedHomogeneous weight d→ g*z∈J→z∈J:= by
  let R:=Dq F n ⧸ J
  let π:Dq F n →+* R:=zVv J
  let M:znc R:=(ke s).map π
  let K:Submodule R R:=LinearMap.ker (LinearMap.mulLeft R (π g))
  have hM:M≤K.annihilator.radical:= by
    change (ke s).map π≤_
    rw [ke,Ideal.map_span,Ideal.span_le]
    rintro _ ⟨_,⟨v,hv,rfl⟩,rfl⟩
    apply mem_radical_annihilator_of_torsion
    intro x hx
    obtain ⟨z,rfl⟩:=zld (I:=J) x
    have hgz :g*z∈J:=Ideal.Quotient.eq_zero_iff_mem.mp (by
      rw [map_mul]
      exact LinearMap.mem_ker.mp hx)
    obtain ⟨m,hm⟩:=h v hv z hgz
    refine ⟨m,?_⟩
    change π (z9v v)^m*π z=0
    rw [← map_pow,← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  obtain ⟨N,hN⟩:=pow_inf_eq_bot M K hM
  refine ⟨N,?_⟩
  intro d hd z hz hg
  have hmem:π z∈(M^an0 s d:Submodule R R) ⊓ K:= by
    constructor
    · change π z∈M^an0 s d
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem π (homogeneous_mem_cutIdeal_pow s hz)
    · change π g*π z=0
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hg
  rw [hN _ hd] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [Submodule.mem_bot] using hmem)
end
end P5_7_3_3_4_1_6_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_6_1
noncomputable section
open P5_7_3_3_4_1_6 MvPolynomial
variable {n:ℕ} {F:Type} [zrc F]
variable (B:znc (z3y (bzm n) F))
@[simp] theorem dehom_C (c:F) :
    ew (n:=n) (C c)=C c:= by simp [ew]
@[simp] theorem dehom_affine (v :bzm n) :
    ew (z9v (Sum.inr v) :Dq F n)=z9v v := by simp [ew]
@[simp] theorem dehom_homogenizer (s :Bool) :
    ew (z9v (Sum.inl s) :Dq F n)=1 := by simp [ew]
private theorem dehom_rename (p:z3y (bzm n) F) :
    ew (rename Sum.inr p)=p:= by
  have h: (ew (F:=F) (n:=n)).comp (rename Sum.inr).toRingHom=RingHom.id _:= by
    apply zXT <;> intros <;> simp
  exact DFunLike.congr_fun h p
private theorem weight_affine (m:bzm n →₀ ℕ) :
    Finsupp.weight weight (m.mapDomain Sum.inr) =
      (∑ i:Fin 2,m (Sum.inl i),∑ i:Fin n,m (Sum.inr i)) := by
  rw [zDM,Finsupp.sum_mapDomain_index_inj Sum.inr_injective,
    m.sum_fintype (fun a b=>b•weight (Sum.inr a)) (fun _=>zero_nsmul _),
    Fintype.sum_sum_type]
  simp [weight,block,step,seedStep,coeffStep,Prod.smul_mk,Prod.ext_iff,
    Prod.fst_sum,Prod.snd_sum]
theorem bmt {a b a' b' : ℕ} (ha :a≤a') (hb:b≤b')
    {x :z3y (bzm n) F ⧸ B} (hx :x∈Box B a b) :x∈Box B a' b' := by
  obtain ⟨p,hp,rfl⟩:=Submodule.mem_map.mp hx
  have hm:p∈BoxPoly F n a' b' := fun m h =>
    ⟨(hp h).1.trans ha,(hp h).2.trans hb⟩
  exact Submodule.mem_map.mpr ⟨p,hm,rfl⟩
theorem ev8 {a b:ℕ} {x :z3y (bzm n) F ⧸ B}
    (hx :x∈Box B a b) :
    ∃ z :Dq F n,z.IsWeightedHomogeneous weight (a,b)∧an3 B z=x := by
  classical
  obtain ⟨p,hp,rfl⟩:=Submodule.mem_map.mp hx
  let d₁ (m:bzm n →₀ ℕ) := ∑ i:Fin 2,m (Sum.inl i)
  let d₂ (m:bzm n →₀ ℕ) := ∑ i:Fin n,m (Sum.inr i)
  let lift (m:bzm n →₀ ℕ) :=
    z9v (Sum.inl true)^(a - d₁ m) *
      (z9v (Sum.inl false)^(b - d₂ m)*rename Sum.inr (monomial m (p.coeff m)))
  refine ⟨∑ m∈p.support,lift m,?_,?_⟩
  · apply IsWeightedHomogeneous.sum
    intro m hm
    have hb:d₁ m≤a∧d₂ m≤b:=hp hm
    have h₁:=(isWeightedHomogeneous_X (R:=F) weight (Sum.inl true :HomVars n)).pow (a - d₁ m)
    have h₂:=(isWeightedHomogeneous_X (R:=F) weight (Sum.inl false :HomVars n)).pow (b - d₂ m)
    have h₃: (rename Sum.inr (monomial m (p.coeff m)) :Dq F n).IsWeightedHomogeneous
        weight (d₁ m,d₂ m) := by
      rw [rename_monomial]
      exact isWeightedHomogeneous_monomial _ _ _ (weight_affine m)
    convert h₁.mul (h₂.mul h₃) using 1
    exact Prod.ext (by simp [weight,block,step,seedStep,coeffStep]; omega)
      (by simp [weight,block,step,seedStep,coeffStep]; omega)
  · change zVv B (ew _)=zVv B p
    congr 1
    rw [map_sum]
    simpa only [lift,map_mul,map_pow,dehom_homogenizer,one_pow,one_mul,dehom_rename]
      using p.as_sum.symm
@[simp] theorem reesMap_X (v :HomVars n) :
    reesMap B (z9v v) =
      AddMonoidAlgebra.single (weight v) (an3 B (z9v v)) := by
  simp [reesMap]
@[simp] theorem reesMap_C (c:F) :
    reesMap B (C c)=AddMonoidAlgebra.single 0 (zVv B (C c)) := by
  simp [reesMap,AddMonoidAlgebra.singleZeroRingHom]
private theorem reesMap_monomial (m:HomVars n →₀ ℕ) (c:F) :
    reesMap B (monomial m c) =
      AddMonoidAlgebra.single (Finsupp.weight weight m) (an3 B (monomial m c)) := by
  rw [monomial_eq]
  simp only [map_mul,reesMap_C,Finsupp.prod,map_prod,map_pow,reesMap_X,
    AddMonoidAlgebra.single_pow,AddMonoidAlgebra.prod_single,AddMonoidAlgebra.single_mul_single,
    zero_add,zDM,zt1,zQb,dehom_C,an3]
theorem reesMap_homogeneous {z :Dq F n} {d:ℕ×ℕ}
    (hz :z.IsWeightedHomogeneous weight d) :
    reesMap B z=AddMonoidAlgebra.single d (an3 B z) := by
  classical
  conv_lhs=>rw [z.as_sum]
  conv_rhs=>rw [z.as_sum]
  simp only [map_sum,reesMap_monomial]
  change _=AddMonoidAlgebra.singleAddHom d (∑ m∈z.support,
    an3 B (monomial m (z.coeff m)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hz (mem_support_iff.mp hm)]
  rfl
private theorem class_C_mem (c:F) :
    zVv B (C c)∈Box B 0 0:= by
  apply Submodule.mem_map.mpr
  refine ⟨_,?_,rfl⟩
  intro m hm
  have hzero :m=0:=Finset.mem_singleton.mp (support_C_subset hm)
  subst m
  simp [aCt]
private theorem class_X_mem (v :HomVars n) :
    an3 B (z9v v)∈Box B (weight v).1 (weight v).2 := by
  classical
  cases v with
  | inl s =>
      change zVv B (ew (z9v (Sum.inl s)))∈_
      rw [dehom_homogenizer,← map_one (C:F →+* _)]
      exact bmt B (Nat.zero_le _) (Nat.zero_le _) (class_C_mem B 1)
  | inr v =>
      change zVv B (ew (z9v (Sum.inr v)))∈_
      rw [dehom_affine]
      apply Submodule.mem_map.mpr
      refine ⟨_,?_,rfl⟩
      intro m hm
      change m∈(z9v v :z3y (bzm n) F).support at hm
      rw [support_X,Finset.mem_singleton] at hm
      subst m
      cases v <;> simp [aCt,weight,block,step,seedStep,coeffStep,Finsupp.single_apply,
        eq_comm]
      rename_i i
      fin_cases i <;> decide
private theorem reesMap_coeff_mem (z :Dq F n) (d:ℕ×ℕ) :
    (reesMap B z).coeff d∈Box B d.1 d.2 := by
  classical
  induction z using MvPolynomial.induction_on generalizing d with
  | C c =>
      by_cases hd: (0:ℕ×ℕ)=d
      · subst d
        simpa using class_C_mem B c
      · simp [reesMap_C,hd]
  | add p q hp hq =>
      simpa only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply] using
        (Box B d.1 d.2).add_mem (hp d) (hq d)
  | mul_X p v hp =>
      rw [map_mul,reesMap_X,mul_comm (reesMap B p)]
      by_cases hd : ∃ e,weight v+e=d
      · obtain ⟨e,rfl⟩:=hd
        rw [AddMonoidAlgebra.coeff_single_mul_add]
        have h:=class_X_mem B v
        obtain ⟨q,hq,he⟩:=Submodule.mem_map.mp h
        change zVv B q= _ at he
        rw [← he]
        simpa only [Prod.fst_add,Prod.snd_add,Nat.add_comm] using bmu hq (hp e)
      · rw [AddMonoidAlgebra.coeff_single_mul_of_forall_add_ne _ _ (fun e he=>hd ⟨e,he⟩)]
        exact Submodule.zero_mem _
theorem boundary_mem_iff (side :Bool) (d:ℕ×ℕ) {z :Dq F n}
    (hz :z.IsWeightedHomogeneous weight (step side+d)) :
    z∈boundary B side↔an3 B z∈Box B d.1 d.2 := by
  classical
  let h:Dq F n:=z9v (Sum.inl side)
  have hh:reesMap B h=AddMonoidAlgebra.single (step side) 1 := by
    simp [h,weight,block,an3]
  constructor
  · intro hzB
    obtain ⟨s,hs,t,ht,he⟩:=Submodule.mem_sup.mp hzB
    change t∈Ideal.span {h} at ht
    obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp ht
    have hs' : reesMap B s=0:=hs
    have he' := congrArg (fun p=>(reesMap B p).coeff (step side+d)) he
    simp only [map_add,map_mul,hs',zero_add,hh,reesMap_homogeneous B hz,
      AddMonoidAlgebra.coeff_single_mul_add,one_mul,AddMonoidAlgebra.coeff_single] at he'
    change (reesMap B r).coeff d=(Finsupp.single _ (an3 B z)) (step side+d) at he'
    rw [Finsupp.single_eq_same] at he'
    exact he' ▸ reesMap_coeff_mem B r d
  · intro hzB
    obtain ⟨r,hr,he⟩:=ev8 B hzB
    let t:=h*r
    have eq :reesMap B t=reesMap B z := by
      rw [show reesMap B t=reesMap B h*reesMap B r from map_mul _ _ _,hh,
        reesMap_homogeneous B hr,reesMap_homogeneous B hz,
        AddMonoidAlgebra.single_mul_single,one_mul,he]
    apply Submodule.mem_sup.mpr
    refine ⟨z - t,?_,t,Ideal.mem_span_singleton.mpr ⟨r,rfl⟩,sub_add_cancel z t⟩
    change reesMap B (z - t)=0
    rw [map_sub,eq,sub_self]
end
end P5_7_3_3_4_1_6_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_6_1
noncomputable section
open P5_7_3_3_4_1_6 MvPolynomial
open cu (FX)
open DQ (jY)
open Cu (Gc)
def c1 :Prop :=
  ∀ (n:ℕ) (B:znc (Gc n)) (cut side :Bool),
    let E :=jY (blockSize n cut)
    extendHom (boundary B side) E=boundary (gN B E) side
def c2 :Prop :=
  ∀ (n:ℕ) (J:znc (Dq FX n)) (cut:Bool) (v :HomVars n),block v=cut →
    let E :=jY (blockSize n cut)
    ∀ z :Dq E n,homForm n cut*z∈extendHom J E →
      ∃ m:ℕ,(z9v v :Dq E n)^m*z∈extendHom J E
theorem cutVar_block {n:ℕ} (cut:Bool) (i:Option (Fin (blockSize n cut))) :
    block (cutVar cut i)=cut:= by
  cases cut <;> cases i <;> rfl
theorem exists_cutVar {n:ℕ} (cut:Bool) (v :HomVars n) (hv :block v=cut) :
    ∃ i,cutVar cut i=v := by
  rcases v with s | (i | i)
  · have h:s=cut:=hv
    subst s
    exact ⟨none,rfl⟩
  · have h:true=cut:=hv
    subst cut
    exact ⟨some i,rfl⟩
  · have h:false=cut:=hv
    subst cut
    exact ⟨some i,rfl⟩
private theorem homForm_weight (n:ℕ) (cut:Bool) :
    (homForm n cut).IsWeightedHomogeneous weight (step cut) := by
  unfold homForm
  have h (i:Option (Fin (blockSize n cut))) :
      IsWeightedHomogeneous weight
        (z9v (cutVar cut i) :Dq (jY (blockSize n cut)) n) (step cut) := by
    simpa only [weight,cutVar_block] using
      (isWeightedHomogeneous_X (R:=jY (blockSize n cut)) weight (cutVar cut i))
  apply IsWeightedHomogeneous.sub
  · apply IsWeightedHomogeneous.sum
    intro j _
    exact (h (some j)).C_mul _
  · exact (h none).C_mul _
private theorem dehom_homForm (n:ℕ) (cut:Bool) :
    ew (homForm n cut)=aEL (bml n cut) := by
  simp [homForm,cutVar,aEL]
private theorem dz1 {n:ℕ} (cut side :Bool)
    (J:znc (z3y (bzm n) (jY (blockSize n cut)))) (d:ℕ×ℕ)
    (hreg : ∀ z :Dq (jY (blockSize n cut)) n,
      z.IsWeightedHomogeneous weight (step side+d) →
      homForm n cut*z∈boundary J side→z∈boundary J side)
    {x :z3y (bzm n) (jY (blockSize n cut)) ⧸ J}
    (hx :x∈Box J (step side+d).1 (step side+d).2)
    (hmul :zVv J (aEL (bml n cut))*x ∈
      Box J (d+step cut).1 (d+step cut).2) :
    x∈Box J d.1 d.2 := by
  obtain ⟨z,hz,he⟩:=ev8 J hx
  have hc:=(homForm_weight n cut).mul hz
  rw [show step cut+(step side+d)=step side+(d+step cut) by ac_rfl] at hc
  have hq:an3 J (homForm n cut*z)∈Box J (d+step cut).1 (d+step cut).2 := by
    rw [map_mul,he]
    simpa only [an3,zQb,dehom_homForm] using hmul
  have hzJ:=hreg z hz ((boundary_mem_iff J side (d+step cut) hc).mpr hq)
  rw [← he]
  exact (boundary_mem_iff J side d hz).mp hzJ
theorem of_children (h₁:c1) (h₂:c2) :P5_7_3_3_4_1_6.c1 := by
  classical
  intro n B cut
  let E :=jY (blockSize n cut)
  let J:=gN B E
  have reg (side :Bool) : ∃ N :ℕ,∀ d:ℕ×ℕ,N≤an0 cut d →
      ∀ z :Dq E n,z.IsWeightedHomogeneous weight d →
        homForm n cut*z∈boundary J side→z∈boundary J side := by
    rw [← h₁ n B cut side]
    exact eventual_injective_of_torsion _ cut _ (h₂ n (boundary B side) cut)
  obtain ⟨N₁,hN₁⟩:=reg true
  obtain ⟨N₂,hN₂⟩:=reg false
  refine ⟨max N₁ N₂,?_⟩
  intro a b ha hb x hqx
  have cutoff (N i j:ℕ) (hN :N≤ max N₁ N₂) (hi:a≤ i) (hj:b≤j) :
      N≤an0 cut (i,j) := by
    cases cut
    · exact hN.trans (hb.trans hj)
    · exact hN.trans (ha.trans hi)
  have shrinkSeed (r s :ℕ) (hx :x∈Box J (a+r) (b+s)) :
      x∈Box J a (b+s) := by
    induction r with
    | zero=>exact hx
    | succ r ih =>
      apply ih
      apply dz1 cut true J (a+r,b+s)
      · exact hN₁ _ (cutoff _ _ _ (le_max_left _ _) (by simp [step,seedStep]; omega)
          (by simp [step,coeffStep]))
      · simpa only [step,seedStep,coeffStep,ite_true,Bool.true_eq_false,ite_false,
          Prod.mk_add_mk,Nat.one_add,Nat.zero_add,Nat.add_succ] using hx
      · exact bmt J (zlr (z8K _ _) _)
          (zlr (z8K _ _) _) hqx
  have shrinkCoeff (s :ℕ) (hx :x∈Box J a (b+s)) :x∈Box J a b:= by
    induction s with
    | zero=>exact hx
    | succ s ih =>
      apply ih
      apply dz1 cut false J (a,b+s)
      · exact hN₂ _ (cutoff _ _ _ (le_max_right _ _) (by simp [step,seedStep])
          (by simp [step,coeffStep]; omega))
      · simpa only [step,seedStep,coeffStep,ite_true,Bool.false_eq_true,ite_false,
          Prod.mk_add_mk,Nat.one_add,Nat.zero_add,Nat.add_succ] using hx
      · exact bmt J le_rfl (zlr (z8K _ _) _) hqx
  obtain ⟨p,hp⟩:=zld (I:=J) x
  let d₁ (m:bzm n →₀ ℕ) := ∑ i:Fin 2,m (Sum.inl i)
  let d₂ (m:bzm n →₀ ℕ) := ∑ i:Fin n,m (Sum.inr i)
  let r :=p.support.sup d₁
  let s :=p.support.sup d₂
  have hpbox :p∈BoxPoly E n (a+r) (b+s) := fun m hm =>
    ⟨(Finset.le_sup (f :=d₁) hm).trans (Nat.le_add_left _ _),
      (Finset.le_sup (f :=d₂) hm).trans (Nat.le_add_left _ _)⟩
  exact shrinkCoeff s (shrinkSeed r s (Submodule.mem_map.mpr ⟨p,hpbox,hp⟩))
end
end P5_7_3_3_4_1_6_1
end
section
set_option autoImplicit true
namespace P5_7_1_5_4_2_1_2
noncomputable section
open Polynomial
open quN7Z4a (compressionWidth)
open qBajpRb (aia row_count)
open private compress fWf from ProximityPrize.SubmissionLower.Z8duOVc
variable {B R:Type} [za6 B] [za6 R]
private def specialize (φ:B →+* R) (u:R[X]) :B[X][X] →+* R[X] :=
  eval₂RingHom (zhd φ) u
private theorem specialize_X_pow (φ:B →+* R) (u:R[X]) (n:ℕ) :
    specialize φ u (Polynomial.C ((Polynomial.X:B[X])^n))=Polynomial.X^n:= by
  change (Polynomial.C _).eval₂ (zhd φ) u= _
  rw [eval₂_C,map_pow]
  simp only [coe_mapRingHom,map_X]
private theorem de6 {n D:ℕ} (hn:0<n) {G:B[X][X]}
    (hG : ∀ i a,(G.coeff i).coeff a≠0→a+i*D <n)
    (φ:B →+* R) {u:R[X]} (hu:u.natDegree≤D) :
    (specialize φ u G).natDegree<n:= by
  apply Nat.lt_of_le_pred hn
  change (G.eval₂ (zhd φ) u).natDegree≤n-1
  rw [eval₂_eq_sum,Polynomial.sum_def]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hne :G.coeff i≠0:=mem_support_iff.mp hi
  have hb:=hG i (G.coeff i).natDegree (leadingCoeff_ne_zero.mpr hne)
  have hm: ((G.coeff i).map φ).natDegree≤(G.coeff i).natDegree :=natDegree_map_le
  exact (natDegree_mul_le_of_le hm (natDegree_pow_le_of_le i hu)).trans (Nat.le_pred_of_lt hb)
theorem proof :q6CrDDe.c2 := by
  intro B _ _ _ V W _ _ D F hD hF hFd hcoeff hrank
  let n:=compressionWidth D 2
  have hn:0<n:= by unfold n compressionWidth; positivity
  have hrows :4*aia D 2=n:=row_count D 2
  have hpos :0<aia D 2 := by omega
  have hs :aia D 2*zsE cu.L (V*W) <
      n*zsE cu.L V:= by
    calc
      _<aia D 2*(4*zsE cu.L V) :=
        Nat.mul_lt_mul_of_pos_left hrank hpos
      _ = _:= by rw [← hrows]; ac_rfl
  obtain ⟨s,P,hP,hP0⟩:=fWf F hF
  have hc (i a :ℕ) : (P.coeff i).coeff a=(F.coeff i).coeff (a+s) := by
    rw [hP,coeff_C_mul,coeff_X_pow_mul]
  have hd:P.natDegree≤2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    apply Polynomial.ext
    intro a
    rw [hc,coeff_eq_zero_of_natDegree_lt (hFd.trans_lt hi),coeff_zero,coeff_zero]
  obtain ⟨H,G,J,hEq,hG0,hGd,hG,hsmall⟩ :=
    compress V W hn P hd (fun i a=> by rw [hc]; exact hcoeff i (a+s)) hP0 hs
  refine ⟨G,hG0,hGd,hG,hsmall,?_⟩
  intro R _ φ u hu hf
  rw [eval_map] at hf ⊢
  change specialize φ u F=0 at hf
  change specialize φ u G=0
  have hp:specialize φ u P=0:= by
    rw [hP,map_mul,specialize_X_pow] at hf
    ext a
    have h:=congrArg (fun T:R[X]=>T.coeff (a+s)) hf
    simpa only [coeff_X_pow_mul,coeff_zero] using h
  have hrel :=congrArg (specialize φ u) hEq
  rw [map_mul,map_add,map_mul,specialize_X_pow,hp,mul_zero] at hrel
  let a :=(specialize φ u G).natDegree
  have ha :a<n:=de6 hn hsmall φ hu
  apply leadingCoeff_eq_zero.mp
  change (specialize φ u G).coeff a=0
  have h:=congrArg (fun T:R[X]=>T.coeff a) hrel.symm
  simpa only [coeff_zero,coeff_add,coeff_X_pow_mul',ite_eq_right (Nat.not_le_of_gt ha),
    add_zero] using h
end
end P5_7_1_5_4_2_1_2
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_6_1_1
noncomputable section
open P5_7_3_3_4_1_6 (bzm blockSize)
open P5_7_3_3_4_1_6_1
open cu (FX)
open DQ (jY)
open czE (aPw quotientBaseChange_tmul)
open scoped TensorProduct
private def reesAlg {n:ℕ} {k :Type} [zrc k] (I:znc (z3y (bzm n) k)) :
    Dq k n →ₐ[k] AddMonoidAlgebra (z3y (bzm n) k ⧸ I) (ℕ×ℕ) where
  __:=reesMap I
  commutes' c:=reesMap_C I c
private theorem rees_kernel_map {n:ℕ} {k E :Type} [zrc k] [zrc E] [Algebra k E]
    (I:znc (z3y (bzm n) k)) :
    (zdq (reesMap I)).map (zDK (algebraMap k E)) =
      zdq (reesMap (I.map (zDK (algebraMap k E)))) := by
  have :Module.Free k E :=Module.Free.of_divisionRing k E
  have :Module.Flat k E :=Module.Flat.of_free
  let m:Dq k n →+* Dq E n:=zDK (algebraMap k E)
  let I' : znc (z3y (bzm n) E) :=I.map (zDK (algebraMap k E))
  let A:=z3y (bzm n) k ⧸ I
  let B:=z3y (bzm n) E ⧸ I'
  let M:=ℕ×ℕ
  let ec:E ⊗[k] A ≃ₐ[E] B:=aPw I
  let j:A →+* B :=
    ec.toRingEquiv.toRingHom.comp
      (zgi (A:=E) (R:=k)).toRingHom
  have hj (p:z3y (bzm n) k) :
      j (zVv I p)=zVv I' (zDK (algebraMap k E) p) := by
    change ec (1 ⊗ₜ[k] zVv I p)= _
    simpa only [one_smul] using (quotientBaseChange_tmul I (1 :E) p)
  have hgen: (AddMonoidAlgebra.mapRingHom (M:=M) j).comp (reesMap I) =
      (reesMap I').comp m:= by
    apply zXT
    · intro c
      change AddMonoidAlgebra.mapRingHom M j (reesMap I (MvPolynomial.C c)) =
        reesMap I' (zDK (algebraMap k E) (MvPolynomial.C c))
      rw [reesMap_C I c,AddMonoidAlgebra.mapRingHom_single,hj]
      simp only [MvPolynomial.map_C,reesMap_C]
    · intro v
      have hd:zDK (algebraMap k E) (ew (z9v v)) =
          ew (z9v v :Dq E n) := by
        cases v <;> simp
      change AddMonoidAlgebra.mapRingHom M j (reesMap I (z9v v)) =
        reesMap I' (zDK (algebraMap k E) (z9v v))
      rw [reesMap_X I v,AddMonoidAlgebra.mapRingHom_single]
      simp only [an3,zQb,hj,hd,z7N,reesMap_X]
  let es :E ⊗[k] Dq k n ≃ₐ[E] Dq E n :=
    MvPolynomial.algebraTensorAlgEquiv k E
  have hes_tmul (a :E) (p:Dq k n) :es (a ⊗ₜ[k] p)=a•m p :=
    MvPolynomial.algebraTensorAlgEquiv_tmul k E a p
  let et:E ⊗[k] AddMonoidAlgebra A M ≃ₐ[E] AddMonoidAlgebra B M :=
    (AddMonoidAlgebra.rTensorEquivAlgEquiv k E E A).trans (AddMonoidAlgebra.mapAlgEquiv E M ec)
  have het (a :E) (p:AddMonoidAlgebra A M) :
      et (a ⊗ₜ[k] p)=a•AddMonoidAlgebra.mapRingHom (M:=M) j p:= by
    dsimp only [et]
    rw [AlgEquiv.trans_apply,AddMonoidAlgebra.rTensorEquiv_tmulAlgEquiv,map_smul]
    refine congrArg (a • ·) ?_
    change AddMonoidAlgebra.mapAlgHom M ec.toAlgHom
        (AddMonoidAlgebra.mapAlgHom M (zgi (A:=E)) p) =
      AddMonoidAlgebra.mapRingHom M j p
    ext d
    simp only [AddMonoidAlgebra.coeff_mapAlgHom,AddMonoidAlgebra.coeff_mapRingHom,
      j,zQb]
    rfl
  let tf :=Algebra.TensorProduct.map (AlgHom.id k E) (reesAlg I)
  have hcomp: (reesMap I').comp es.toAlgHom.toRingHom =
      et.toAlgHom.toRingHom.comp tf.toRingHom:= by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a p =>
        change reesAlg I' (es (a ⊗ₜ[k] p))=et (a ⊗ₜ[k] reesMap I p)
        rw [hes_tmul,map_smul,het]
        exact congrArg (a • ·) (RingHom.congr_fun hgen p).symm
    | add x y hx hy =>
        rw [map_add,map_add,hx,hy]
  let ir :Dq k n →+* E ⊗[k] Dq k n :=
    (zgi (A:=E) (R:=k)).toRingHom
  have hker : (zdq (reesMap I')).comap es.toAlgHom.toRingHom =
      (zdq (reesMap I)).map ir := by
    rw [RingHom.comap_ker,hcomp]
    change zdq (et.toRingEquiv.toRingHom.comp tf.toRingHom)= _
    rw [RingHom.ker_equiv_comp,← Submodule.restrictScalars_inj k]
    change LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor k E (reesAlg I).toLinearMap)= _
    rw [Module.Flat.ker_lTensor_eq]
    exact TensorProduct.AlgebraTensorModule.range_lTensor_idealMap (R:=k) E k
      (zdq (reesMap I))
  have hes :es.toAlgHom.toRingHom.comp ir=m:= by
    apply RingHom.ext
    intro p
    change es (1 ⊗ₜ[k] p)=m p
    simpa only [one_smul] using hes_tmul 1 p
  calc
    (zdq (reesMap I)).map m =
        ((zdq (reesMap I')).comap es.toAlgHom.toRingHom).map es.toAlgHom.toRingHom:= by
      rw [hker,Ideal.map_map,hes]
    _=zdq (reesMap I') :=
      Ideal.map_comap_of_surjective es.toAlgHom.toRingHom es.surjective _
theorem proof :P5_7_3_3_4_1_6_1.c1 := by
  intro n B cut side
  let E :=jY (blockSize n cut)
  change (boundary B side).map (zDK (algebraMap FX E)) =
    boundary (B.map (zDK (algebraMap FX E))) side
  simp only [boundary,Ideal.map_sup,rees_kernel_map,Ideal.map_span,
    Set.image_singleton,z7N]
end
end P5_7_3_3_4_1_6_1_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_6_1_2
noncomputable section
open MvPolynomial
open scoped TensorProduct nonZeroDivisors

open czE (aPw quotientBaseChange_tmul)
open P5_7_3_3_4_1_6_1
private def form {ι A:Type} [z85 ι] [za6 A] (a :ι→A) :z3y ι A :=
  ∑ i,C (a i)*z9v i
private theorem chart_torsion {ι A:Type} [z85 ι] [za6 A]
    (a :ι→A) (i:ι) (t:A)
    (hu:IsUnit (algebraMap A (Localization.Away t) (a i)))
    (q:z3y ι A) (hq:form a*q=0) :
    ∃ m:ℕ,(C t)^m*q=0:= by
  classical
  let L:=Localization.Away t
  let M:=(Submonoid.powers t).map (C (σ:=ι))
  let B:=z3y ι L
  let _:Algebra (z3y ι A) B:=MvPolynomial.algebraMvPolynomial (R:=A) (S:=L)
  have :IsLocalization M B:=MvPolynomial.isLocalization (σ:=ι) (Submonoid.powers t) L
  let j:=algebraMap (z3y ι A) B
  let e :=(Equiv.optionSubtypeNe i).symm
  let F:=(renameEquiv L e).trans (optionEquivLeft L {k // k≠i})
  have hcoeff : (F (j (form a))).coeff 1=C (algebraMap A L (a i)) := by
    change (optionEquivLeft L _ (rename e (map (algebraMap A L) (form a)))).coeff 1= _
    simp only [form,map_sum,map_mul,map_C,map_X,rename_C,rename_X,Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro k _ hk
      simp only [e,Equiv.optionSubtypeNe_symm_of_ne hk,optionEquivLeft_X_some,
        optionEquivLeft_C,← Polynomial.C_mul]
      simp
    · simp
  have hreg:=Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
    (hcoeff ▸ (hu.map (C (σ := {k // k≠i}))).mem_nonZeroDivisors)
  have hzero :j q=0:= by
    apply F.injective
    rw [map_zero]
    exact hreg.1 _ (by rw [← map_mul,← map_mul,hq,map_zero,map_zero])
  obtain ⟨s,hs⟩:=(zw9 M B q).mp hzero
  obtain ⟨b,hb,he⟩:=s.property
  obtain ⟨m,rfl⟩:=hb
  exact ⟨m,by rw [← map_pow (C (σ:=ι)),he]; exact hs⟩
private theorem localized_torsion {R S:Type} [za6 R] [za6 S] [Algebra R S]
    (M:Submonoid R) [IsLocalization M S] (p a :R)
    (h : ∀ q:R,p*q=0 → ∃ n:ℕ,a^n*q=0)
    (z :S) (hz :algebraMap R S p*z=0) :
    ∃ n:ℕ,(algebraMap R S a)^n*z=0:= by
  obtain ⟨⟨q,s⟩,hs⟩:=IsLocalization.surj M z
  have hzq:algebraMap R S (p*q)=0:= by
    rw [map_mul,← hs,← mul_assoc,hz,zero_mul]
  obtain ⟨t,ht⟩:=(zw9 M S (p*q)).mp hzq
  obtain ⟨n,hn⟩:=h (↑t*q) (by rwa [mul_left_comm])
  refine ⟨n,(IsUnit.mul_left_eq_zero (IsLocalization.map_units S s)).mp ?_⟩
  rw [mul_assoc,hs,← map_pow,← map_mul]
  exact (zw9 M S (a^n*q)).mpr
    ⟨t,by rwa [mul_left_comm] at hn⟩
private abbrev sU (k ι:Type) [zrc k] :=FractionRing (z3y ι k)
private def parameter {k ι:Type} [zrc k] (i:ι) :sU k ι :=
  algebraMap (z3y ι k) (sU k ι) (z9v i)
private theorem tensor_torsion {k ι A:Type} [zrc k] [z85 ι] [za6 A] [Algebra k A]
    (a :ι→A) (i:ι) (t:A) (hu:IsUnit (algebraMap A (Localization.Away t) (a i)))
    (z :A ⊗[k] sU k ι)
    (hz : (∑ j,(a j ⊗ₜ[k] (1 :sU k ι))*(1 ⊗ₜ[k] parameter j))*z=0) :
    ∃ m:ℕ,(t ⊗ₜ[k] (1 :sU k ι))^m*z=0:= by
  let D:=z3y ι k
  let R:=A ⊗[k] D
  let M:=(nonZeroDivisors D).map (zgi (A:=A) (R:=k))
  let L:=Localization M
  let e :R ≃ₐ[A] z3y ι A:=algebraTensorAlgEquiv k A
  let E :=IsLocalization.tensorProductEquivOfMapIncludeRight k A (nonZeroDivisors D)
    (sU k ι) L
  let g:z3y ι A →+* L:=(algebraMap R L).comp e.symm.toRingEquiv.toRingHom
  have hE (b:A) (r :D) :
      E (b ⊗ₜ[k] algebraMap D (sU k ι) r)=g (e (b ⊗ₜ[k] r)) := by
    change E (b ⊗ₜ[k] _)=algebraMap R L (e.symm (e (b ⊗ₜ[k] r)))
    rw [IsLocalization.tensorProductEquivOfMapIncludeRight_tmul,e.symm_apply_apply]
  have hc (b:A) :E (b ⊗ₜ[k] (1 :sU k ι))=g (C b) := by
    have he :e (b ⊗ₜ[k] (1 :D))=C b:=e.commutes b
    simpa only [map_one,he] using hE b 1
  have hp (j:ι) :E ((1 :A) ⊗ₜ[k] parameter j)=g (z9v j) := by
    have he :e ((1 :A) ⊗ₜ[k] (z9v j:D))=z9v j:= by
      simpa only [e,one_smul,z7N] using
        algebraTensorAlgEquiv_tmul k A 1 (z9v j)
    simpa only [parameter,he] using hE 1 (z9v j)
  have hpre (w:R) (hw:e.symm (form a)*w=0) :
      ∃ m:ℕ,(e.symm (C t))^m*w=0:= by
    have hw' : form a*e w=0:= by
      simpa only [map_mul,e.apply_symm_apply,map_zero] using congrArg e hw
    obtain ⟨m,hm⟩:=chart_torsion a i t hu (e w) hw'
    exact ⟨m,e.injective (by simpa only [map_mul,map_pow,e.apply_symm_apply,map_zero] using hm)⟩
  have hzL:g (form a)*E z=0:= by
    simpa only [form,map_sum,map_mul,map_zero,hc,hp] using congrArg E hz
  obtain ⟨m,hm⟩:=localized_torsion M (e.symm (form a)) (e.symm (C t)) hpre (E z) hzL
  change (g (C t))^m*E z=0 at hm
  exact ⟨m,E.injective (by simpa only [map_mul,map_pow,hc,map_zero] using hm)⟩
private def avS {k σ η:Type} [zrc k] [z85 η] (u:Option η→σ) :
    z3y σ (sU k (Option η)) :=
  (∑ j:η,C (parameter (some j))*z9v (u (some j))) -
    C (parameter none)*z9v (u none)
private def signed {η A:Type} [Neg A] (x :Option η→A) :Option η→A
  | none => -x none
  | some j=>x (some j)
private theorem signed_unit {η A:Type} [za6 A] (x :Option η→A) (i:Option η) :
    IsUnit (algebraMap A (Localization.Away (x i)) (signed x i)) := by
  cases i with
  | none =>
    rw [signed,(algebraMap A (Localization.Away (x none))).map_neg]
    exact (IsLocalization.Away.algebraMap_isUnit (x none)).neg
  | some j=>exact IsLocalization.Away.algebraMap_isUnit (x (some j))
private theorem extension_torsion {k σ η:Type} [zrc k] [z85 η]
    (J:znc (z3y σ k)) (u:Option η→σ) (i:Option η)
    (z :z3y σ (sU k (Option η)))
    (hz :avS u*z∈J.map (zDK (algebraMap k (sU k (Option η))))) :
    ∃ m:ℕ,z9v (u i)^m*z ∈
      J.map (zDK (algebraMap k (sU k (Option η)))) := by
  let E :=sU k (Option η)
  let A:=z3y σ k ⧸ J
  let I:=J.map (zDK (algebraMap k E))
  let q:=zVv I
  let Q:=aPw (E :=E) J
  let F:A ⊗[k] E ≃+* (z3y σ E ⧸ I) :=
    (zOQ k A E).toRingEquiv.trans Q.toRingEquiv
  let f :A ⊗[k] E →+* (z3y σ E ⧸ I) :=F.toRingHom
  let x (j:Option η) :A:=zVv J (z9v (u j))
  have hc (j:Option η) :f (x j ⊗ₜ[k] (1 :E))=q (z9v (u j)) := by
    change Q ((zOQ k A E) (x j ⊗ₜ[k] (1 :E)))= _
    rw [zrb]
    simpa only [Q,x,q,I,one_smul,z7N] using
      quotientBaseChange_tmul (E :=E) J 1 (z9v (u j))
  have hp (j:Option η) :f ((1 :A) ⊗ₜ[k] parameter j)=q (C (parameter j)) := by
    change Q ((zOQ k A E) ((1 :A) ⊗ₜ[k] parameter j))= _
    rw [zrb]
    exact Q.commutes _
  let p:A ⊗[k] E := ∑ j,(signed x j ⊗ₜ[k] (1 :E))*(1 ⊗ₜ[k] parameter j)
  have hcut:f p=q (avS u) := by
    dsimp only [p]
    rw [avS,q.map_sub,map_sum q,Fintype.sum_option,f.map_add,map_sum f]
    have hneg:f (-(x none ⊗ₜ[k] (1 :E))) = -(f (x none ⊗ₜ[k] (1 :E))) :=
      map_neg f (x none ⊗ₜ[k] (1 :E))
    simp only [signed,TensorProduct.neg_tmul,f.map_mul,hneg,hc,hp,q.map_mul,
      sub_eq_neg_add,mul_comm]
    exact congrArg (fun y=>y + ∑ j:η,q (z9v (u (some j))) *
      q (C (parameter (some j)))) (neg_mul (q (z9v (u none))) (q (C (parameter none))))
  let w:=F.symm (q z)
  have hwq:f w=q z :=F.apply_symm_apply _
  have hw:p*w=0:= by
    apply F.injective
    change f (p*w)=f 0
    rw [f.map_mul,hcut,hwq,f.map_zero,← q.map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  obtain ⟨m,hm⟩:=tensor_torsion (k :=k) (signed x) i (x i) (signed_unit x i) w hw
  refine ⟨m,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  have fpow:f ((x i ⊗ₜ[k] (1 :E))^m)=(f (x i ⊗ₜ[k] (1 :E)))^m :=
    map_pow f (x i ⊗ₜ[k] (1 :E)) m
  change q (z9v (u i)^m*z)=0
  simpa only [f.map_mul,fpow,hc,hwq,f.map_zero,q.map_mul,q.map_pow] using congrArg f hm
theorem proof :P5_7_3_3_4_1_6_1.c2 := by
  intro n J cut v hv E z hz
  obtain ⟨i,rfl⟩:=exists_cutVar cut v hv
  exact extension_torsion J (cutVar cut) i z hz
end
end P5_7_3_3_4_1_6_1_2
end
