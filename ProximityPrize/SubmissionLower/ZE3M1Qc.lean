import ProximityPrize.SubmissionLower.Zmn8gnb
import ProximityPrize.SubmissionLower.ZEdS9yd
import ProximityPrize.SubmissionLower.Zgvu91a
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, CommRing → za6, Field → zrb, Finsupp.degree_eq_sum → zFi, Fintype.sum_sum_type → zbt, Function.Injective → zq4, Function.Surjective → zpX, Ideal → znc, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.span → zye, IsFractionRing.injective → zxb, LinearMap.ker → z83, LinearMap.mulLeft → zzN, LinearMap.range → zWl, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.X → z9v, PowerSeries → zpm, Submodule.mem_map_of_mem → zip
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_3_2
noncomputable section
open qAjZDhd
open scoped WithZero
def infinity (F:Type) [zrb F] :Valuation (RatFunc F) ℤᵐ⁰:= by
  classical
  exact RatFunc.inftyValuation F
abbrev seedField (k :Type) [zrb k] :=FractionRing (zpm k)
end
end P5_7_3_3_4_1_3_2
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace P5_7_3_3_4_1_3_2
noncomputable section
open qAjZDhd Polynomial
open scoped WithZero
variable {k :Type} [zrb k]
theorem b4F:zq4 (ek (k :=k)) :=
  (RatFunc.algebraMap_injective _).comp
    (Polynomial.map_injective _ (zxb (zpm k) _))
private theorem guards {R S F:Type} [za6 R] [za6 S] [zrb F]
    (f :R[X]) (g:ℕ) (a :R) (e :R →+* S) (j:R →+* F)
    (hj:zq4 j) (hg:0<g) (hd:f.natDegree=g)
    (hb:e (f.resultant f.derivative g (g - 1)*f.eval a)≠0) :
    (f.map j).Separable∧(f.map j).natDegree=g∧j (f.eval a)≠0:= by
  rw [map_mul] at hb
  have transfer {x :R} (h:e x≠0) :j x≠0 :=
    fun hz=>h (by rw [(map_eq_zero_iff _ hj).mp hz,map_zero])
  exact ⟨separable_map_of_resultant_derivative_padded_ne_zero j f hd.le hg
    (transfer (left_ne_zero_of_mul hb)),
    (natDegree_map_eq_of_injective hj _).trans hd,transfer (right_ne_zero_of_mul hb)⟩
theorem generic_guards {p:ℕ} (M:LocalMark k p) :
    (M.f.map ek).Separable∧(M.f.map ek).natDegree=M.g ∧
    ek (M.f.eval (reference M.a))≠0 :=
  guards M.f M.g (reference M.a) reduce ek b4F
    (Nat.zero_lt_two.trans_le M.two_le) M.degree M.branch_nonzero
theorem infinity_surjective (F:Type) [zrb F] :
    zpX (infinity F) := by
  classical
  intro b
  by_cases hb:b=0
  · exact ⟨0,by simp [hb]⟩
  refine ⟨(RatFunc.X:RatFunc F)^WithZero.log b,?_⟩
  rw [infinity,RatFunc.inftyValuation.X_zpow,WithZero.exp_log hb]
theorem normalized_poly (P:Physical k) (n:ℕ) (h:P≠0) :
    infinity (seedField k) (ek P*(RatFunc.X⁻¹:Generic k)^n) =
      WithZero.exp ((P.natDegree :ℤ) - n) := by
  classical
  let j:=algebraMap (zpm k) (seedField k)
  have hj:=zxb (zpm k) (seedField k)
  change infinity (seedField k)
    (algebraMap (seedField k)[X] (Generic k) (P.map j)*(RatFunc.X⁻¹:Generic k)^n)= _
  rw [map_mul,map_pow,map_inv₀,infinity,RatFunc.inftyValuation.X,
    RatFunc.inftyValuation_apply,RatFunc.inftyValuation.polynomial (seedField k)
      ((Polynomial.map_ne_zero_iff hj).mpr h),natDegree_map_eq_of_injective hj]
  simp [sub_eq_add_neg,← WithZero.exp_add]
theorem normalized_r {p:ℕ} (M:LocalMark k p) :
    infinity (seedField k) (ek M.r*(RatFunc.X⁻¹:Generic k)^M.r.natDegree)≤1 := by
  rw [normalized_poly _ _ M.monic.ne_zero,sub_self,WithZero.exp_zero]
theorem product_integral {R E :Type} [za6 R] [zrb E] (j:R →+* E)
    (s :Multiset E) (a :E) (hs : ∀ x∈s,j.IsIntegralElem (x*a)) (i:ℕ) :
    j.IsIntegralElem (((s.map fun x=>Polynomial.X - C x).prod.scaleRoots a).coeff i) := by
  let:zZE R E :=j.toAlgebra
  induction s using Multiset.induction_on generalizing i with
  | empty =>
    simpa only [Multiset.map_zero,Multiset.prod_zero,one_scaleRoots] using
      (show j.IsIntegralElem ((1 :E[X]).coeff i) from by
        rw [coeff_one]
        split_ifs
        · exact j.isIntegralElem_one
        · exact j.isIntegralElem_zero)
  | cons x s ih =>
    rw [Multiset.map_cons,Multiset.prod_cons,mul_scaleRoots_of_noZeroDivisors,
      X_sub_C_scaleRoots,coeff_mul]
    change IsIntegral R _
    apply IsIntegral.sum
    intro b _
    apply IsIntegral.mul
    · rw [coeff_sub,coeff_X,coeff_C]
      apply IsIntegral.sub
      · split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
      · split_ifs
        · exact hs x (Multiset.mem_cons_self _ _)
        · exact isIntegral_zero
    · exact ih (fun y hy=>hs y (Multiset.mem_cons_of_mem hy)) b.2
theorem weight_of_integral (Q:Equation k) (r :ℕ)
    (h : ∀ i,((algebraMap (Generic k) (AlgebraicClosure (Generic k))).comp
      (infinity (seedField k)).integer.subtype).IsIntegralElem
      (Polynomial.coeff (scaleRoots (Q.map bL9)
        (algebraMap (Generic k) (AlgebraicClosure (Generic k)) ((RatFunc.X⁻¹:Generic k)^r))) i)) :
    WeightBound r Q:= by
  let j:=algebraMap (Generic k) (AlgebraicClosure (Generic k))
  intro i hi
  by_cases hz :Q.coeff i=0
  · simp [hz]
  let n:=r*(Q.natDegree - i)
  specialize h i
  have hj:zq4 (bL9 (k :=k)) :=j.injective.comp (b4F (k :=k))
  rw [coeff_scaleRoots,natDegree_map_eq_of_injective hj Q,coeff_map] at h
  have he : ((bL9 (Q.coeff i)) *
      (j ((RatFunc.X⁻¹:Generic k)^r))^(Q.natDegree - i)) =
      j (ek (Q.coeff i)*(RatFunc.X⁻¹:Generic k)^n) := by
    simp only [n,pow_mul,map_mul,map_pow,bL9,RingHom.comp_apply,j]
  have hin:=RingHom.IsIntegralElem.of_map j.injective (he ▸ h)
  have hv :=(Valuation.integer.integers (infinity (seedField k))).isIntegral_iff_v_le_one.mp hin
  rw [normalized_poly _ _ hz,WithZero.exp_le_one_iff] at hv
  exact_mod_cast (sub_nonpos.mp hv : (↑(Q.coeff i).natDegree :ℤ)≤n)
end
end P5_7_3_3_4_1_3_2
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
namespace P5_7_3_3_4_1_3_2
noncomputable section
open qAjZDhd Polynomial
open q85rTDe (aNu extend_derivation)
open scoped WithZero
def c1 :Prop :=
  ∀ (k :Type) [zrb k],
    ∃ D:Derivation ℤ (Generic k) (Generic k),
      (∀ b:Physical k,D (ek b)=ek (seedDeriv b)) ∧
      ∀ b,infinity (seedField k) (D b)≤ infinity (seedField k) b
def c2 :Prop :=
  ∀ {F E :Type} [zrb F] [zrb E] [zZE F E] [zAa F E]
    [zw7 F E] [zZE ℤ F] [zZE ℤ E] (p:ℕ) [CharP F p],zsE F E<p →
    ∀ (v :Valuation F ℤᵐ⁰),zpX v →
    ∀ (D:Derivation ℤ F F) (d:Derivation ℤ E E),
      (∀ b,d (algebraMap F E b)=algebraMap F E (D b)) →
      (∀ b,v (D b)≤v b) →
      ∀ z :E,z≠0 →
        ((algebraMap F E).comp v.integer.subtype).IsIntegralElem (d z/z)
private theorem unscaled_integral (tame :c2) {k :Type} [zrb k] {p:ℕ} [CharP k p]
    (M:LocalMark k p) (D:Derivation ℤ (Generic k) (Generic k))
    (hD : ∀ b:Physical k,D (ek b)=ek (seedDeriv b))
    (hv : ∀ b,infinity (seedField k) (D b)≤ infinity (seedField k) b)
    {y :AlgebraicClosure (Generic k)} (hy :y∈(M.f.map bL9).roots) :
    ((algebraMap (Generic k) (AlgebraicClosure (Generic k))).comp
      (infinity (seedField k)).integer.subtype).IsIntegralElem
      (-(seedPartial M.f).eval₂ bL9 y/M.denominator.eval₂ bL9 y) := by
  let F:=Generic k
  let A:=AlgebraicClosure F
  let J:=M.f.map ek
  let j:=algebraMap F A
  obtain ⟨hJ,hdeg,href⟩:=generic_guards M
  have hyJ:aeval y J=0:= by
    rw [aeval_def]
    change (M.f.map ek).eval₂ j y=0
    rw [← eval_map,Polynomial.map_map]
    exact isRoot_of_mem_roots hy
  have hdiv :=minpoly.dvd F y hyJ
  have hysep:IsSeparable F y :=hJ.of_dvd hdiv
  let E :=IntermediateField.adjoin F ({y} : Set A)
  let a :E :=⟨y,IntermediateField.mem_adjoin_simple_self _ _⟩
  let i:E →+* A:=E.val.toRingHom
  let e :=algebraMap F E
  let m:=e.comp ek
  have hm (P:Equation k) :i (P.eval₂ m a)=P.eval₂ bL9 y :=
    (hom_eval₂ P m i a).trans rfl
  have ha :M.f.eval₂ m a=0:=i.injective (by
    rw [hm,map_zero,← eval_map]
    exact isRoot_of_mem_roots hy)
  have hd:M.f.derivative.eval₂ m a≠0:= by
    intro h
    apply hJ.aeval_derivative_ne_zero hyJ
    simpa only [J,aeval_def,derivative_map,eval₂_map,j,bL9,hm,map_zero]
      using congrArg i h
  have ha' : a - m (reference M.a)≠0:= by
    intro hh
    rw [sub_eq_zero.mp hh,eval₂_at_apply,← map_zero e] at ha
    exact href (e.injective ha)
  let:zw7 F E :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hysep
  let:zAa F E :=IntermediateField.adjoin.finiteDimensional hysep.isIntegral
  let:CharP F p:=charP_of_injective_ringHom
    (ek.comp (Polynomial.C.comp PowerSeries.C)).injective p
  have hsmall:zsE F E<p:= by
    rw [IntermediateField.adjoin.finrank hysep.isIntegral]
    exact (natDegree_le_of_dvd hdiv hJ.ne_zero).trans_lt (hdeg.symm ▸ M.tame)
  obtain ⟨d,hdext⟩:=extend_derivation (E :=E) D
  have hc:=aNu d m a M.f (seedPartial M.f) (fun l=> by
    change d (e (ek (M.f.coeff l)))=e (ek ((seedPartial M.f).coeff l))
    rw [hdext,hD]
    rfl)
  rw [ha,map_zero] at hc
  have hq:d a = -(seedPartial M.f).eval₂ m a/M.f.derivative.eval₂ m a := by
    apply (eq_div_iff hd).mpr
    linear_combination -hc
  have hz :d (a - m (reference M.a))=d a := by
    rw [map_sub,sub_eq_self]
    change d (e (ek (reference M.a)))=0
    rw [hdext,hD]
    have hzero :seedDeriv (reference M.a)=0:= by
      ext n:1
      change (PowerSeries.derivative (R:=k)) ((reference M.a).coeff n)= _
      rw [reference,coeff_C,coeff_zero]
      split_ifs <;> simp
    simp [hzero]
  have h:=(tame p hsmall (infinity (seedField k)) (infinity_surjective _) D d
    hdext hv _ ha').map i
  have hden:M.denominator.eval₂ m a =
      M.f.derivative.eval₂ m a*(a - m (reference M.a)) := by
    simp only [LocalMark.denominator,eval₂_mul,eval₂_sub,eval₂_X,eval₂_C]
  rw [hz,hq,div_div,← hden,map_div₀,map_neg,hm,hm] at h
  exact h
theorem of_children (base :c1) (tame :c2) :qAjZDhd.c2 := by
  intro k _ p _ M Q hQ
  obtain ⟨D,hD,hv⟩:=base k
  apply weight_of_integral Q M.r.natDegree
  intro i
  let j:=algebraMap (Generic k) (AlgebraicClosure (Generic k))
  let v :=infinity (seedField k)
  let b:=(RatFunc.X⁻¹:Generic k)^M.r.natDegree
  let u (y :AlgebraicClosure (Generic k)) :=
    (M.numerator false).eval₂ bL9 y/M.denominator.eval₂ bL9 y
  have hp:Q.map bL9=(((M.f.map bL9).roots.map u).map
      fun x=>Polynomial.X - C x).prod:= by
    simpa only [Multiset.map_map,Function.comp_def,RootProduct,u,← eval_map] using hQ
  rw [hp]
  apply product_integral
  intro x hx
  obtain ⟨y,hy,rfl⟩:=Multiset.mem_map.mp hx
  have h₁:=((Valuation.integer.integers v).isIntegral_iff_v_le_one.mpr
    (normalized_r M) :IsIntegral v.integer (ek M.r*b))
  have h₂:=unscaled_integral tame M D hD hv hy
  have he :u y*j b=j (ek M.r*b) *
      (-(seedPartial M.f).eval₂ bL9 y/M.denominator.eval₂ bL9 y) := by
    simp only [u,LocalMark.numerator,Bool.false_eq_true,ite_false,eval₂_mul,eval₂_neg,
      eval₂_C,map_mul,div_eq_mul_inv]
    change -(j (ek M.r))*_ *_ *_ = _
    ring
  rw [he]
  exact RingHom.IsIntegralElem.mul _ (RingHom.IsIntegralElem.map h₁ j) h₂
end
end P5_7_3_3_4_1_3_2
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P5_7_3_3_4_1_6
noncomputable section
open MvPolynomial
open cu (FX)
open czE (aPw quotientBaseChange_tmul)
open private interpolate from ProximityPrize.SubmissionLower.ZFFuWqa
open scoped Pointwise TensorProduct
variable {F:Type} [zrb F] {n:ℕ}
instance (a b:ℕ) :Finite (aCt n a b) :=
  ((Finsupp.finite_of_degree_le (a+b)).subset (by
    intro e he
    change e.degree≤a+b
    rw [zFi,zbt]
    exact Nat.add_le_add he.1 he.2)).to_subtype
instance (B:znc (z3y (bzm n) F)) (a b:ℕ) :
    zAa F (Box B a b) := by
  let:zAa F (BoxPoly F n a b) :=Module.Finite.of_basis (basisRestrictSupport F _)
  exact Module.Finite.map (BoxPoly F n a b) (Ideal.Quotient.mkₐ F B).toLinearMap
theorem bmu {B:znc (z3y (bzm n) F)} {a b u v :ℕ}
    {q:z3y (bzm n) F} (hq:q∈BoxPoly F n u v)
    {x :z3y (bzm n) F ⧸ B} (hx :x∈Box B a b) :
    zVv B q*x∈Box B (a+u) (b+v) := by
  classical
  obtain ⟨p,hp,rfl⟩:=Submodule.mem_map.mp hx
  refine ⟨p*q,?_,?_⟩
  · intro e he
    obtain ⟨s,hs,t,ht,rfl⟩:=Finset.mem_add.mp (support_mul p q he)
    have h₁:=(show ↑p.support⊆aCt n a b from hp) hs
    have h₂:=(show ↑q.support⊆aCt n u v from hq) ht
    exact ⟨by simpa only [Finsupp.add_apply,Finset.sum_add_distrib] using
        Nat.add_le_add h₁.1 h₂.1,
      by simpa only [Finsupp.add_apply,Finset.sum_add_distrib] using
        Nat.add_le_add h₁.2 h₂.2⟩
  · change zVv B (p*q)= _
    rw [map_mul,mul_comm]
    rfl
theorem box_rank_extend {E :Type} [zrb E] [zZE FX E]
    (B:znc (z3y (bzm n) FX)) (a b:ℕ) :
    zsE E (Box (gN B E) a b)=zsE FX (Box B a b) := by
  let T:=Box B a b
  let J:=gN B E
  let m:=MvPolynomial.map (σ:=bzm n) (algebraMap FX E)
  let e :=aPw (E :=E) B
  let f :=e.toLinearMap.comp (TensorProduct.AlgebraTensorModule.lTensor E E T.subtype)
  have hf :zq4 f :=e.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M:=E) T.subtype Subtype.val_injective)
  have hbox :zWl f=Box J a b:= by
    apply le_antisymm
    · rintro _ ⟨z,rfl⟩
      induction z using TensorProduct.inductionOn with
      | tmul c x =>
        obtain ⟨p,hp,hp'⟩:=Submodule.mem_map.mp x.property
        have hm:m p∈BoxPoly E n a b:= fun _ hd =>
          (show ↑p.support⊆aCt n a b from hp) (support_map_subset _ _ hd)
        change e (c ⊗ₜ[FX] (x :_))∈Box J a b
        rw [← hp']
        exact (quotientBaseChange_tmul B c p).symm ▸
          (Box J a b).smul_mem c (zip hm)
      | add x y hx hy=>rw [map_add]; exact (Box J a b).add_mem hx hy
    · rw [Box,BoxPoly,restrictSupport_eq_span,Submodule.map_span,Submodule.span_le]
      rintro _ ⟨_,⟨d,hd,rfl⟩,rfl⟩
      let p:z3y (bzm n) FX:=monomial d 1
      let x :T:=⟨zVv B p,zip
        ((monomial_mem_restrictSupport FX).mpr (Or.inl hd))⟩
      refine ⟨1 ⊗ₜ[FX] x,?_⟩
      change e (1 ⊗ₜ[FX] zVv B p)= _
      rw [quotientBaseChange_tmul,one_smul,MvPolynomial.map_monomial,map_one]
      rfl
  rw [← hbox,f.finrank_range_of_inj hf,Module.finrank_baseChange]
theorem cev {B:znc (z3y (bzm n) F)}
    (q:z3y (bzm n) F) (a b c d:ℕ)
    [zAa F (z3y (bzm n) F ⧸ (B ⊔ zye {q}))]
    (strict : ∀ x :z3y (bzm n) F ⧸ B,
      zVv B q*x∈Box B c d→x∈Box B a b) :
    zsE F (Box B c d)≤zsE F (Box B a b) +
      zsE F (z3y (bzm n) F ⧸ (B ⊔ zye {q})) := by
  let Q:=B ⊔ zye {q}
  let π:=(Ideal.Quotient.factorₐ F (le_sup_left:B≤Q)).toLinearMap.domRestrict (Box B c d)
  let ι:=(Box B c d).subtype.comp (z83 π).subtype
  let μ:=(zzN F (zVv B q)).domRestrict (Box B a b)
  have hk :zWl ι≤zWl μ:= by
    rintro _ ⟨z,rfl⟩
    obtain ⟨p,hp⟩:=zld (I:=B) z.1.1
    have hz :=LinearMap.mem_ker.mp z.2
    change Ideal.Quotient.factor (le_sup_left:B≤Q) z.1.1=0 at hz
    rw [← hp] at hz
    obtain ⟨s,hs,t,ht,hst⟩:=Submodule.mem_sup.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp ht
    have he :zVv B q* zVv B r=z.1.1 := by
      rw [← hp,← hst,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hs,zero_add,map_mul]
    exact ⟨⟨zVv B r,strict _ (he.symm ▸ z.1.2)⟩,he⟩
  have hi:zq4 ι:=Subtype.val_injective.comp Subtype.val_injective
  have hker :=(ι.finrank_range_of_inj hi).symm.le.trans
    ((Submodule.finrank_mono hk).trans μ.finrank_range_le)
  have hrange :=Submodule.finrank_le (zWl π)
  have hrank :=π.finrank_range_add_finrank_ker
  change _+_=zsE F (Box B c d) at hrank
  omega
theorem rank_marks {B:znc (z3y (bzm n) F)} [B.IsPrime]
    {ι:Type} [Fintype ι] (e :ι→(z3y (bzm n) F ⧸ B) →ₐ[F] F)
    (he :zq4 e) (q:z3y (bzm n) F) (u v :ℕ)
    (hdeg:q∈BoxPoly F n u v) (hq:q∉B)
    (hz : ∀ i,e i (zVv B q)=0) :
    ∃ N :ℕ,∀ a b:ℕ,N≤a→N≤b →
      zsE F (Box B a b)+Fintype.card ι ≤
        zsE F (Box B (a+u) (b+v)) := by
  classical
  obtain ⟨r,hr⟩:=interpolate e he
  choose p hp using fun i=>zld (I:=B) (r i)
  let N :=Finset.univ.sup fun i=>(p i).totalDegree
  refine ⟨N,fun a b ha hb => ?_⟩
  let U:=Box B a b
  let V:=Box B (a+u) (b+v)
  let π:=LinearMap.pi fun i=>(e i).toLinearMap.comp V.subtype
  have hm (i:ι) :r i∈V:= by
    refine ⟨p i,?_,hp i⟩
    intro m hm
    have h:=(le_totalDegree hm).trans
      (Finset.le_sup (f := fun i=>(p i).totalDegree) (Finset.mem_univ i))
    change m.degree≤N at h
    rw [zFi,zbt] at h
    exact ⟨by omega,by omega⟩
  have hπ:zpX π:= by
    intro f
    refine ⟨∑ i,f i•(⟨r i,hm i⟩:V),?_⟩
    funext j
    change ((e j).toLinearMap.comp V.subtype) (∑ i,f i•(⟨r i,hm i⟩:V))=f j
    simp [hr]
  let μ:=((zzN F (zVv B q)).domRestrict U).codRestrict V
    (fun x=>bmu hdeg x.property)
  have hμ : ∀ x,μ x∈z83 π:= by
    intro x
    refine LinearMap.mem_ker.mpr (funext fun i => ?_)
    change e i (zVv B q*x.val)=0
    rw [map_mul,hz,zero_mul]
  have hι:zq4 (μ.codRestrict _ hμ) := by
    intro x y hxy
    apply Subtype.ext
    exact mul_left_cancel₀ (mt Ideal.Quotient.eq_zero_iff_mem.mp hq)
      (congrArg (fun t:z83 π=>t.val.val) hxy)
  have hker :=LinearMap.finrank_le_finrank_of_injective hι
  have h:=π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ,finrank_top,Module.finrank_fintype_fun_eq_card] at h
  exact (Nat.add_le_add_right hker _).trans (by rw [Nat.add_comm]; exact h.le)
end
end P5_7_3_3_4_1_6
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_6_1
noncomputable section
open P5_7_3_3_4_1_6
open cu (FX)
open DQ (jY Qd)
open MvPolynomial
abbrev HomVars (n:ℕ) :=Bool ⊕ bzm n
abbrev Dq (F:Type) [za6 F] (n:ℕ) :=z3y (HomVars n) F
def block {n:ℕ} : HomVars n→Bool
  | .inl s=>s
  | .inr (.inl _)=>true
  | .inr (.inr _)=>false
def step (s :Bool) :ℕ×ℕ:=(seedStep s,coeffStep s)
def weight {n:ℕ} (v :HomVars n) :ℕ×ℕ:=step (block v)
def cutVar {n:ℕ} (s :Bool) :Option (Fin (blockSize n s))→HomVars n
  | none => .inl s
  | some i => .inr (bml n s i)
def an0 (s :Bool) (d:ℕ×ℕ) :ℕ:=if s then d.1 else d.2
variable {n:ℕ} {F:Type} [za6 F]
def ew:Dq F n →+* z3y (bzm n) F :=
  eval₂Hom MvPolynomial.C (Sum.elim (fun _=>1) z9v)
abbrev an3 (B:znc (z3y (bzm n) F)) :
    Dq F n →+* (z3y (bzm n) F ⧸ B) :=
  (zVv B).comp ew
def reesMap (B:znc (z3y (bzm n) F)) :
    Dq F n →+* AddMonoidAlgebra (z3y (bzm n) F ⧸ B) (ℕ×ℕ) :=
  eval₂Hom
    (AddMonoidAlgebra.singleZeroRingHom.comp ((zVv B).comp MvPolynomial.C))
    (fun v=>AddMonoidAlgebra.single (weight v) (an3 B (z9v v)))
def boundary (B:znc (z3y (bzm n) F)) (side :Bool) :znc (Dq F n) :=
  RingHom.ker (reesMap B) ⊔ zye {z9v (Sum.inl side)}
abbrev extendHom (J:znc (Dq FX n)) (E :Type) [zrb E] [zZE FX E] :=
  J.map (MvPolynomial.map (algebraMap FX E))
def homForm (n:ℕ) (s :Bool) :Dq (jY (blockSize n s)) n :=
  (∑ j:Fin (blockSize n s),C (Qd (some j)) *
    z9v (cutVar s (some j))) -
    C (Qd (n:=blockSize n s) none)*z9v (cutVar s none)
end
end P5_7_3_3_4_1_6_1
end
