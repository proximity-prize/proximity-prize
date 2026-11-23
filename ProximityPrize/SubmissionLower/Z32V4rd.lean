import ProximityPrize.SubmissionLower.ZPlZTHb
import ProximityPrize.SubmissionLower.Zpj8DDa
import ProximityPrize.SubmissionLower.ZEe4bHc
import ProximityPrize.SubmissionLower.ZjG08xb
import ProximityPrize.SubmissionLower.ZJVClxb
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsAlgebraic → zjH, Algebra.IsIntegral → zVK, Algebra.IsIntegral.of_finite → zux, CommRing → za6, Field → zrb, Function.Injective → zq4, Function.Surjective → zpX, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsLocalization.lift → zvq, IsLocalization.map_units → z0j, IsLocalization.mk' → zzm, IsLocalization.surj → zg4, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algebraMap_eq → zsL, Module.Finite → zAa, Polynomial.X → z7y, Polynomial.ext → zXJ, RingHom.comp_apply → zQb, RingHom.ext → zz4, Set.mem_Icc → zs2
section
section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
namespace qydrhVa
noncomputable section
open Polynomial WithZero
open scoped Classical WithZero nonZeroDivisors
open P5 (K)
open cu (L)

open qqi5QRb (pointVal)
open qb0hmCe (CurveModel)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb (Pencil Chart Vertical tu seedRing)
open qZn79Eb (TrivialSeed)
open qXARP7c (gauss base_eval)
open q9r9FBa (valuationDVR)
open private lift_poly scale_bound from ProximityPrize.SubmissionLower.Zpj8DDa
open private Ek bsA detect_normal from ProximityPrize.SubmissionLower.ZjG08xb
open private localValuation from ProximityPrize.SubmissionLower.ZDlyzqd
attribute [local instance] Polynomial.algebra
private theorem polynomialFraction {D E :Type} [za6 D] [IsDomain D] [zrb E]
  [zZE D E] [z0o D E] :z0o D[X] (tu E) := by
 have hi:zq4 (algebraMap D[X] E[X]) :=
  Polynomial.map_injective _ (zxb D E)
 letI:FaithfulSMul D[X] (tu E) :=(faithfulSMul_iff_algebraMap_injective ..).mpr
  ((zxb E[X] (tu E)).comp hi)
 have :IsLocalization (D⁰.map C) E[X] :=Polynomial.isLocalization D⁰ E
 apply IsFractionRing.of_field
 intro a
 obtain ⟨f,g,_,rfl⟩:=IsFractionRing.div_surjective E[X] a
 obtain ⟨⟨F,s⟩,hf⟩:=zg4 (D⁰.map C) f
 obtain ⟨⟨G,t⟩,hg⟩:=zg4 (D⁰.map C) g
 let j:=algebraMap E[X] (tu E)
 have hs :j (algebraMap D[X] E[X] (s :D[X]))≠0 :=
  (z0j E[X] s).map j |>.ne_zero
 have ht:j (algebraMap D[X] E[X] (t:D[X]))≠0 :=
  (z0j E[X] t).map j |>.ne_zero
 refine ⟨F*t,G*s,?_⟩
 simp only [zG3 D[X] E[X] (tu E),map_mul]
 rw [← hf,← hg,map_mul,map_mul,mul_assoc,mul_assoc,mul_comm (j (algebraMap D[X] E[X] t)),
  mul_div_mul_right _ _ (mul_ne_zero hs ht)]
private theorem seedScale {E M:Type} [zrb E] [zrb M] (u:Valuation E ℤᵐ⁰)
   (hu:zpX u) (v :Valuation M ℤᵐ⁰) (j:E →+* M)
   (hreg : ∀ a :u.valuationSubring,v (j a)≤1)
   (hnon : ¬ (∀ a :E,a≠0→v (j a)=1)) :
   ∃ n:ℕ,0<n ∧ ∀ a :E,v (j a)=u a^n:= by
 obtain ⟨t,ht⟩:=hu (exp (-1 :ℤ))
 have ht0:t≠0:= fun e=>exp_ne_zero (by rw [← ht,e,map_zero])
 have ht' : u t≤1 :=ht ▸ exp_le_one_iff.mpr (by decide : (-1 :ℤ)≤0)
 have ht1 :=hreg ⟨t,ht'⟩
 have hunit (a :E) (ha :u a=1) :v (j a)=1 := by
   let a' : u.valuationSubring :=⟨a,ha.le⟩
   have h:IsUnit a' := ((Valuation.valuationSubring.integers u).isUnit_iff_valuation_eq_one).mpr ha
   let f :=(j.comp u.valuationSubring.subtype).codRestrict v.valuationSubring.toSubring hreg
   exact ((Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one).mp (h.map f)
 have hrep (a :E) (ha :a≠0) :v (j a)=v (j t)^(-log (u a)) := by
   let k :=log (u a)
   have hk :u a=exp k :=(exp_log (u.ne_zero_iff.mpr ha)).symm
   have htk :u (a*t^k)=1 := by
     rw [map_mul,map_zpow₀,ht,hk,← exp_zsmul,← exp_add]
     simp only [Int.zsmul_eq_mul,mul_neg,mul_one,add_neg_cancel,exp_zero]
   have h:=hunit (a*t^k) htk
   rw [map_mul j,map_zpow₀ j,map_mul,map_zpow₀] at h
   exact (eq_inv_of_mul_eq_one_left h).trans (zpow_neg _ _).symm
 have htlt:v (j t)<1 := by
   refine lt_of_le_of_ne ht1 fun he=>hnon fun a ha => ?_
   rw [hrep a ha,he,one_zpow]
 have htn:v (j t)≠0:=v.ne_zero_iff.mpr ((_root_.map_ne_zero j).mpr ht0)
 let n:=(-log (v (j t))).toNat
 have hn0:=(log_lt_log htn one_ne_zero).mpr htlt
 rw [log_one] at hn0
 have hn: (n:ℤ) = -log (v (j t)) :=Int.toNat_of_nonneg (by omega)
 refine ⟨n,by omega,fun a => ?_⟩
 by_cases ha :a=0
 · rw [ha,map_zero,map_zero,map_zero,zero_pow (by omega :n≠0)]
 · nth_rw 1 [← exp_log (u.ne_zero_iff.mpr ha)]
   rw [hrep a ha,← exp_log htn,← exp_zsmul,← exp_nsmul,Int.zsmul_eq_mul,nsmul_eq_mul,hn]
   rw [neg_mul,neg_mul,mul_comm]
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S} {A:Pencil F} {γ:K} {hγ:γ∈F.marks} {B:L[X]}
private theorem cFh (T:Chart A γ hγ B) (g: (seedRing F γ)[X]) :
   ((eval₂RingHom (A.inChart γ) T.u g:A.bY γ) :A.M) =
     g.eval₂ ((algebraMap Cq.E A.M).comp (seedRing F γ).subtype) A.u:= by
 change (A.bY γ).subtype (g.eval₂ (A.inChart γ) T.u)= _
 rw [hom_eval₂]
 change g.eval₂ _ (T.u:A.M)= _
 rw [T.center]
 rfl
private theorem classify (T:Chart A γ hγ B) (v :Valuation A.M ℤᵐ⁰)
   (hv :zpX v) (P:Ideal ((seedRing F γ)[X])) [P.IsPrime]
   (nochain : ∀ I:Ideal ((seedRing F γ)[X]),I.IsPrime→ I ≠ ⊥ → I≤P→ I=P)
   (hreg : ∀ a :A.bY γ,v (a :A.M)≤1)
   (hP : ∀ g: (seedRing F γ)[X],v ((eval₂RingHom (A.inChart γ) T.u g:A.bY γ) :A.M)
     < 1↔g∈P) :
   TrivialSeed A v ∨ ∃ w:Vertical A (F.place γ),w.value=v := by
 let u:=(F.place γ).value
 let D:=seedRing F γ
 let j:=algebraMap Cq.E A.M
 let Q:=RingHom.ker (mapRingHom (IsLocalRing.residue D))
 have :Q.IsPrime :=RingHom.ker_isPrime _
 by_cases h:TrivialSeed A v
 · exact Or.inl h
 have hw (a :D) :v (j a)≤1 :=hreg (A.inChart γ a)
 obtain ⟨e,he,hscale⟩:=seedScale u (F.place γ).normalized v j hw h
 have hQ:Q≤P:= by
   rw [show Q=(IsLocalRing.maximalIdeal D).map (C:D →+* D[X]) by
     dsimp only [Q]
     rw [Polynomial.ker_mapRingHom,IsLocalRing.ker_residue]]
   rw [Ideal.map_le_iff_le_comap]
   intro a ha
   change C a∈P
   have hlt:u (a :Cq.E)<1 :=u.mem_maximalIdeal_iff.mp ha
   apply (hP (C a)).mp
   rw [cFh T,eval₂_C,zQb,hscale]
   exact pow_lt_one₀ zero_le hlt (Nat.ne_of_gt he)
 have hQ0:Q ≠ ⊥ := by
   obtain ⟨t,ht⟩:=(F.place γ).normalized (exp (-1 :ℤ))
   have hlt:u t<1 :=ht ▸ exp_lt_one_iff.mpr (by decide : (-1 :ℤ)<0)
   let a :D:=⟨t,hlt.le⟩
   have hqa :C a∈Q:= by
     change (C a).map (IsLocalRing.residue D)=0
     rw [map_C,C_eq_zero]
     exact (IsLocalRing.residue_eq_zero_iff _).mpr (u.mem_maximalIdeal_iff.mpr hlt)
   intro hzero
   rw [hzero,Ideal.mem_bot,C_eq_zero] at hqa
   exact exp_ne_zero (ht ▸ show u t=0 from by rw [show t=0 from congrArg Subtype.val hqa,map_zero])
 have hQP:=nochain Q inferInstance hQ0 hQ
 refine Or.inr ⟨⟨v,hv,e,he,?_⟩,rfl⟩
 intro g
 change v (g.eval₂ j A.u)=gauss u g^e
 by_cases hg:g=0
 · subst g
   change v ((0:Cq.E[X]).eval₂ j A.u)=((0:Cq.E[X]).support.sup _)^e
   simp [zero_pow (Nat.ne_of_gt he)]
 obtain ⟨i,hi,hs⟩:=g.support.exists_mem_eq_sup (support_nonempty.mpr hg)
   (fun i=>u (g.coeff i))
 let s :=g.coeff i
 have hs0:s≠0:=mem_support_iff.mp hi
 obtain ⟨G,hG⟩:=lift_poly u (scale_bound u hs.symm hs0)
 have hGi:G.coeff i=1 := by
   apply u.valuationSubring.subtype_injective
   rw [← coeff_map,hG,coeff_C_mul,map_one]
   exact inv_mul_cancel₀ hs0
 have hGP:G∉P:= by
   rw [← hQP]
   intro hmem
   change G.map (IsLocalRing.residue D)=0 at hmem
   have hc:=congrArg (fun f : (IsLocalRing.ResidueField D)[X]=>f.coeff i) hmem
   rw [coeff_map,coeff_zero] at hc
   change IsLocalRing.residue u.valuationSubring (G.coeff i)=0 at hc
   rw [hGi,map_one] at hc
   exact one_ne_zero hc
 have hunit :v ((eval₂RingHom (A.inChart γ) T.u G:A.bY γ) :A.M)=1 :=
   le_antisymm (hreg _) (le_of_not_gt fun ht=>hGP ((hP G).mp ht))
 rw [cFh T,← eval₂_map,hG,eval₂_mul,eval₂_C] at hunit
 change v (j s⁻¹*g.eval₂ j A.u)=1 at hunit
 rw [map_inv₀ j,map_mul,map_inv₀] at hunit
 change gauss u g=u s at hs
 rw [inv_mul_eq_iff_eq_mul₀ (v.ne_zero_iff.mpr ((_root_.map_ne_zero j).mpr hs0)),mul_one,
   hscale] at hunit
 rw [hs]
 exact hunit
theorem proof :qZn79Eb.c2 := by
  intro q Cq z S F A γ hγ B T x J b hb
  let D:=seedRing F γ
  let R:=D[X]
  let H :=tu Cq.E
  let M:=A.M
  let C₀:=A.bY γ
  letI:IsDiscreteValuationRing D:=valuationDVR (F.place γ).value (F.place γ).normalized
  letI:z0o R H :=polynomialFraction
  letI:zZE R C₀:=(eval₂RingHom (A.inChart γ) T.u).toAlgebra
  letI:zZE R M:=((algebraMap H M).comp (algebraMap R H)).toAlgebra
  letI:zsf R H M:=zsL fun _=>rfl
  letI:zsf R C₀ M:=zsL fun f=> by
    change algebraMap H M (algebraMap Cq.E[X] H (f.map D.subtype)) =
      ((eval₂RingHom (A.inChart γ) T.u f :C₀) :M)
    rw [base_eval A,eval₂_map]
    exact (cFh T f).symm
  letI:zAa R C₀:=T.finite
  letI:IsNoetherianRing C₀:=IsNoetherianRing.of_finite R C₀
  letI:zVK R C₀:=zux R C₀
  let N :=integralClosure C₀ M
  letI:zZE R N :=((algebraMap C₀ N).comp (algebraMap R C₀)).toAlgebra
  letI:zsf R C₀ N :=zsL fun _=>rfl
  letI:zsf R N M:=zsL
    (fun f=>zG3 R C₀ M f)
  letI:IsIntegralClosure N R M:=⟨Subtype.val_injective,fun {a} =>
    ⟨fun ha=>⟨⟨a,ha.tower_top⟩,rfl⟩,fun ⟨n,hn⟩ =>
      hn ▸ isIntegral_trans (R:=R) (n:M) n.property⟩⟩
  letI:Algebra.IsSeparable H M:=A.separable
  letI:zAa R N :=IsIntegralClosure.finite R H M N
  letI:zAa C₀ N :=Module.Finite.of_restrictScalars_finite R C₀ N
  letI:IsNoetherianRing N :=IsNoetherianRing.of_finite R N
  letI:z0o N M:=IsIntegralClosure.isFractionRing_of_finite_extension R H M N
  letI:IsIntegrallyClosed N :=(isIntegrallyClosed_iff_isIntegrallyClosedIn (R:=N) M).mpr inferInstance
  have hchart:A.bY γ≤J.ring := fun a ha =>
    (J.fractions a).mpr ⟨⟨a,ha⟩,1,by simp,by simp⟩
  letI:zZE C₀ J.ring :=(Subring.inclusion hchart).toAlgebra
  letI:zsf C₀ J.ring M:=zsL fun _=>rfl
  let U:Submonoid C₀ :=
    { carrier := {a | pointVal x (T.map a)=1}
      one_mem' := by simp
      mul_mem' := fun ha hc=> by
        change pointVal x (T.map (_ *_))=1
        rw [map_mul,map_mul,ha,hc,mul_one] }
  have hinv (a :C₀) (ha :a∈U) : (a :M)⁻¹∈J.ring :=
    (J.fractions _).mpr ⟨1,a,ha,by simp [one_div]⟩
  have hne (a :C₀) (ha :a∈U) : (a :M)≠0:= by
    intro hz
    change pointVal x (T.map a)=1 at ha
    rw [show a=0 from Subtype.ext hz,map_zero,map_zero] at ha
    exact zero_ne_one ha
  have hnon (a :C₀) (ha :a∈U) : ¬ IsIntegral C₀ ((a :M)*b) := by
    intro hi
    let s :J.ring :=⟨_,hinv a ha⟩
    have h:=(isIntegral_algebraMap (x :=s)).mul (hi.tower_top (A:=J.ring))
    change IsIntegral J.ring ((a :M)⁻¹*((a :M)*b)) at h
    rw [← mul_assoc,inv_mul_cancel₀ (hne a ha),one_mul] at h
    exact hb h
  let I:=(Ek (R:=N) b).comap (algebraMap C₀ N)
  have hI (a :C₀) :a∈I↔IsIntegral C₀ ((a :M)*b) := by
    change algebraMap C₀ N a∈Ek b↔_
    rw [bsA]
    exact ⟨fun ⟨c,hc⟩=>hc.symm ▸ c.property,fun hi=>⟨⟨_,hi⟩,rfl⟩⟩
  obtain ⟨m,hm,hIm,hmU⟩:=I.exists_le_prime_disjoint U
    (Set.disjoint_left.mpr fun a ha hU=>hnon a hU ((hI a).mp ha))
  have :m.IsPrime :=hm
  have :zjH R M:=IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance :zjH H M)
  obtain ⟨a,ha,hai⟩:=(Algebra.IsAlgebraic.isAlgebraic (R:=R) b).exists_integral_multiple
  have hRM:zq4 (algebraMap R M) :=
    (algebraMap H M).injective.comp (zxb R H)
  have hd:algebraMap C₀ M (algebraMap R C₀ a)≠0 :=
    fun h=>ha (hRM ((zG3 R C₀ M a).trans (h.trans (map_zero _).symm)))
  rw [Algebra.smul_def,zG3 R C₀ M] at hai
  obtain ⟨P,hP,hp,hPm,hbad⟩:=detect_normal m b
    (fun c hc hi=>hc (hIm ((hI c).mpr hi)))
    ⟨algebraMap R C₀ a,hd,hai.tower_top⟩
  have :P.IsPrime :=hP
  obtain ⟨v,hv,hcen,hreg,hval⟩:=localValuation (N :=N) (K:=M) P hp
  have hregC (a :C₀) :v (a :M)≤1 :=hreg (algebraMap C₀ N a)
  refine ⟨v,hv,?_,lt_of_not_ge fun h=>hbad ((hval b).mp h),?_⟩
  · intro a
    obtain ⟨c,d,hd,h⟩:=(J.fractions _).mp a.property
    have hunit :v (d:M)=1 :=le_antisymm (hregC d) (le_of_not_gt fun hlt =>
      (Set.disjoint_left.mp hmU) (hPm ((hcen _).mp hlt)) hd)
    change v (a :M)≤1
    rw [h,map_div₀,hunit,div_one]
    exact hregC c
  let P₀:=P.under R
  letI:P₀.IsPrime :=Ideal.comap_isPrime (algebraMap R N) P
  letI:FaithfulSMul R N :=(faithfulSMul_iff_algebraMap_injective ..).mpr
    (Function.Injective.of_comp (f :=algebraMap N M) (g:=algebraMap R N)
      (by rw [← RingHom.coe_comp,← IsScalarTower.algebraMap_eq R N M]
          exact hRM))
  letI:zVK R N :=zux R N
  refine classify T v hv P₀ ?_ hregC (fun g=>hcen (algebraMap R N g))
  intro I hIp hI₀ hIP
  letI:I.IsPrime :=hIp
  by_contra hn
  obtain ⟨Q,hQP,hQ,hQI⟩ :=
    Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt P (lt_of_le_of_ne hIP hn)
  letI:Q.IsPrime :=hQ
  have hne :Q≠P:= by
    intro hz
    exact hn (hQI.over.trans (congrArg (fun Q' : Ideal N=>Q'.under R) hz))
  have hQ₀:Q ≠ ⊥ := by
    intro hzb
    apply hI₀
    rw [hQI.over,hzb]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R N)
  have hheight:=(Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hQP hne))
  rw [hp] at hheight
  have hh:Q.height+1≤0+1 := by simpa only [zero_add] using hheight
  have hz :Q.height≤0:=(ENat.add_le_add_iff_right ENat.one_ne_top).mp hh
  exact hQ₀ (Ideal.height_eq_zero_iff_eq_bot.mp (le_antisymm hz zero_le))
end
end qydrhVa
end
section
set_option autoImplicit true
namespace qrqpbQa
theorem proof :qeBKasb.c2 :=
 qydrhVa.proof
end qrqpbQa
end
end
section
section
set_option autoImplicit true
namespace qkEA7Vd
theorem proof :qfzuawb.c3:=qJm9rWb.fiber
end qkEA7Vd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qi1t4Ta
open Polynomial Matrix
open scoped Matrix
private theorem coeff_shift {T:Type*} [za6 T] (g:T[X]) {d:ℕ}
   (hd:g.natDegree≤d) (i j:ℕ) :
   (g*z7y ^j).coeff i =
     if i∈Set.Icc j (j+d) then g.coeff (i - j) else 0:= by
 rw [coeff_mul_X_pow']
 by_cases h:j≤ i
 · by_cases h' : i≤j+d
   · simp [zs2,h,h']
   · simp [zs2,h,h',coeff_eq_zero_of_natDegree_lt (show g.natDegree< i - j by omega)]
 · simp [zs2,h]
private theorem cNb {T:Type*} [za6 T] (g:T[X]) (t:T)
  (hg:g.eval t=0) {d n:ℕ} (hd:g.natDegree≤d) (j:ℕ) (hj:d+j<n) :
  ∑ i:Fin n,t^(i:ℕ)*(g*z7y ^j).coeff i=0:= by
 have hdeg: (g*z7y ^j).natDegree<n :=
  natDegree_mul_le.trans_lt ((Nat.add_le_add hd (natDegree_X_pow_le j)).trans_lt hj)
 simp only [mul_comm (t^_)]
 calc
  _ = ∑ i∈Finset.range n,(g*z7y ^j).coeff i*t^i :=
    Fin.sum_univ_eq_sum_range (fun i:ℕ=>(g*z7y ^j).coeff i*t^i) n
  _=0:= by rw [← eval_eq_sum_range' hdeg,eval_mul,hg,zero_mul]
private theorem sylvester_eval {T:Type*} [za6 T] (f g:T[X]) (t:T)
   {m n:ℕ} (hf :f.natDegree≤ m) (hg:g.natDegree≤n)
   (hf0:f.eval t=0) (hg0:g.eval t=0) :
   (fun i:Fin (m+n)=>t^(i:ℕ)) ᵥ* sylvester f g m n=0:= by
 ext j
 cases j using Fin.addCases with
 | left j =>
   simp only [vecMul,dotProduct,sylvester,of_apply,Fin.addCases_left,Pi.zero_apply]
   simp_rw [← coeff_shift g hg]
   exact cNb g t hg0 hg j (by have :=j.isLt; omega)
 | right j =>
   simp only [vecMul,dotProduct,sylvester,of_apply,Fin.addCases_right,Pi.zero_apply]
   simp_rw [← coeff_shift f hf]
   exact cNb f t hf0 hf j (by have :=j.isLt; omega)
private theorem discr_vanish {R T:Type*} [za6 R] [zrb T]
   (a :R →+* T) (f :R[X]) (hd:2≤f.natDegree) (t:T)
   (hf :f.eval₂ a t=0) (hg:f.derivative.eval₂ a t=0) :a f.discr=0:= by
 classical
 let n:=f.natDegree
 let j:Fin (n - 1+n) :=⟨2*n - 2,by dsimp [n]; omega⟩
 let w:Fin (n - 1+n)→T:= fun i =>
   if i=j then a f.leadingCoeff*t^(i:ℕ) else t^(i:ℕ)
 have hS: (fun i:Fin (n - 1+n)=>t^(i:ℕ)) ᵥ*
     a.mapMatrix (sylvester f.derivative f (n-1) n)=0:= by
   rw [← sylvester_map_map]
   exact sylvester_eval _ _ t
     (natDegree_map_le.trans (natDegree_derivative_le _)) natDegree_map_le
     (by simpa only [eval_map] using hg) (by simpa only [eval_map] using hf)
 have hw:w ᵥ* a.mapMatrix f.sylvesterDeriv=0:= by
   rw [← hS,← sylvesterDeriv_updateRow f (by omega)]
   ext k
   simp only [vecMul,dotProduct]
   apply Finset.sum_congr rfl
   intro i _
   change w i*a (f.sylvesterDeriv i k) =
     t^(i:ℕ)*a ((f.sylvesterDeriv.updateRow j (f.leadingCoeff•f.sylvesterDeriv j)) i k)
   by_cases h:i=j
   · subst i
     simp only [w,ite_eq_left rfl,updateRow_self,Pi.smul_apply,smul_eq_mul,map_mul]
     ac_rfl
   · rw [updateRow_ne h,show w i=t^(i:ℕ) by simp only [w,ite_eq_right h]]
 have hn:w≠0:= by
   intro h
   let i:Fin (n-1+n) :=⟨0,by dsimp [n]; omega⟩
   have hij:i≠j:=Fin.ne_of_val_ne (by change 0≠2*n-2; dsimp [n]; omega)
   have hh:=congrFun h i
   simp only [w,ite_eq_right hij,Pi.zero_apply] at hh
   simp [i] at hh
 rw [Polynomial.discr,map_mul,RingHom.map_det,Matrix.exists_vecMul_eq_zero_iff.mp ⟨w,hn,hw⟩,zero_mul]
private theorem linear_impossible {E T:Type*} [zrb E] [zrb T]
   (a :E[X] →+* T) (f :E[X][X]) (hi:Irreducible f) (hd:f.natDegree=1) (t:T)
   (hf :f.eval₂ a t=0) (hg:f.derivative.eval₂ a t=0) :False := by
 have hprim:=hi.isPrimitive (by omega :f.natDegree≠0)
 let I:=RingHom.ker a
 let b:=Submodule.IsPrincipal.generator I
 have hI:Ideal.span {b} = I:=Ideal.span_singleton_generator I
 have hb:a b=0:= by
   apply RingHom.mem_ker.mp
   change b∈I
   rw [← hI]
   exact Ideal.mem_span_singleton_self b
 have hbu : ¬ IsUnit b:= fun h=>(h.map a).ne_zero hb
 apply hbu (hprim b ?_)
 rw [C_dvd_iff_dvd_coeff]
 suffices hall : ∀ i,a (f.coeff i)=0 by
   intro i
   apply Ideal.mem_span_singleton.mp
   rw [hI]
   exact RingHom.mem_ker.mpr (hall i)
 have he :=eq_X_add_C_of_natDegree_le_one hd.le
 have h1 :a (f.coeff 1)=0:= by
   conv at hg=>lhs; rw [he]
   simpa using hg
 have h0:a (f.coeff 0)=0:= by
   conv at hf=>lhs; rw [he]
   simpa [eval₂_add,eval₂_mul,h1] using hf
 intro i
 rcases i with _ | _ | i
 · exact h0
 · exact h1
 · rw [coeff_eq_zero_of_natDegree_lt (by omega),map_zero]
theorem discr_of_common_root {E T:Type*} [zrb E] [zrb T]
   (a :E[X] →+* T) (f :E[X][X]) (hi:Irreducible f) (hd:0<f.natDegree) (t:T)
   (hf :f.eval₂ a t=0) (hg:f.derivative.eval₂ a t=0) :a f.discr=0:= by
 by_cases h:2≤f.natDegree
 · exact discr_vanish a f h t hf hg
 · exact (linear_impossible a f hi (by omega) t hf hg).elim
end qi1t4Ta
end
section
namespace qJm9rWb
def c1 :Prop :=qfzuawb.c1
def c2 :Prop :=qfzuawb.c2
theorem of_children (h1 :c1) (h2 :c2) :q0mTRkc.c5 :=
 qfzuawb.of_children h1 h2 fiber
end qJm9rWb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qOHrlse
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX j9)
open P5_7_7 (phys)
open qqi5QRb (pointVal)
open qb0hmCe (CurveModel)

open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb (Pencil Chart seedRing markJet linear coords)
open qZn79Eb (MarkLocal shift slope)
open private polyVal_le polyVal_eq from ProximityPrize.SubmissionLower.ZOcoJLa
private structure Fractions {M:Type} [zrb M] (R:Subring M)
  (s :R →+* FX) (x :L) where
 ring :Subring M
 mem_iff : ∀ a :M,a∈ring ↔ ∃ b c:R,
  pointVal x (s c)=1∧a=(b:M)/(c:M)
 map :ring →+* FX
 map_div : ∀ (b c:R) (_hc:pointVal x (s c)=1)
  (a :ring),(a :M)=(b:M)/(c:M)→map a=s b/s c
private def localize {M:Type} [zrb M] (R:Subring M) (s :R →+* FX)
    (x :L) :Fractions R s x := by
  let W:Submonoid R :=
    { carrier := {c | pointVal x (s c)=1}
      one_mem' := by simp
      mul_mem' := by
        intro b c hb hc
        show pointVal x (s (b*c))=1
        rw [map_mul,map_mul,show pointVal x (s b)=1 from hb,
          show pointVal x (s c)=1 from hc,one_mul] }
  have hsn (c:W) :s c≠0:= by
    intro h
    have hc:pointVal x (s c)=1 :=c.property
    rw [h,map_zero] at hc
    exact zero_ne_one hc
  have hrn (c:W) : ((c:R) :M)≠0:= by
    intro h
    have hc: (c:R)=0:=Subtype.ext h
    exact hsn c (hc ▸ s.map_zero)
  let i:Localization W →+* M :=
    zvq (g:=R.subtype) fun c:W=>isUnit_iff_ne_zero.mpr (hrn c)
  let j:Localization W →+* FX :=
    zvq (g:=s) fun c:W=>isUnit_iff_ne_zero.mpr (hsn c)
  have hi:zq4 i:=(IsLocalization.lift_injective_iff _).2 fun a b =>
    ⟨fun h=> by simpa only [i,IsLocalization.lift_eq] using congrArg i h,
     fun h=>congrArg (algebraMap R (Localization W)) (Subtype.val_injective h)⟩
  let e :Localization W ≃+* i.range :=
    RingEquiv.ofLeftInverse (Function.leftInverse_invFun hi)
  have he (a :Localization W) : (e a :M)=i a :=rfl
  have hfrac {N :Type} [zrb N] (g:R →+* N) (u : ∀ c:W,IsUnit (g c))
      (b:R) (c:W) :
      (zvq u:Localization W →+* N) (zzm (Localization W) b c) =
        g b/g c:= by
    apply (eq_div_iff (u c).ne_zero).2
    have h:=congrArg (zvq u:Localization W →+* N)
      (IsLocalization.mk'_spec (Localization W) b c)
    simpa only [map_mul,IsLocalization.lift_eq] using h
  refine ⟨i.range,?_,j.comp e.symm.toRingHom,?_⟩
  · intro a
    constructor
    · rintro ⟨b,rfl⟩
      obtain ⟨c,d,rfl⟩:=IsLocalization.exists_mk'_eq W b
      exact ⟨c,d,d.property,hfrac R.subtype _ c d⟩
    · rintro ⟨b,c,hc,rfl⟩
      exact ⟨zzm (Localization W) b ⟨c,hc⟩,hfrac R.subtype _ b ⟨c,hc⟩⟩
  · intro b c hc a ha
    let d:W:=⟨c,hc⟩
    let v :=zzm (Localization W) b d
    have h:e v=a :=Subtype.ext ((he v).trans ((hfrac R.subtype _ b d).trans ha.symm))
    rw [← h,zQb]
    change j (e.symm (e v))= _
    rw [RingEquiv.symm_apply_apply]
    exact hfrac s _ b d
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S} {A:Pencil F} {γ:K} {hγ:γ∈F.marks} {B:L[X]}
private theorem c7Q (T:Chart A γ hγ B) (x :L) (hx :B.eval x=0)
    (a :A.bY γ) :pointVal x (T.map a)≤1 := by
  obtain ⟨b,hb⟩:=a
  induction hb using Subring.closure_induction with
  | mem b hb =>
    rcases hb with (⟨c,rfl⟩ | ⟨i,rfl⟩)
    · rw [show (⟨A.pO γ c,_⟩:A.bY γ)=A.inChart γ c from rfl,T.seed]
      exact polyVal_le _ _
    · rw [show (⟨A.ratio i,_⟩:A.bY γ)=A.chartRatio γ i from rfl,T.F8,
        map_div₀,polyVal_eq x (T.avoids x hx),div_one]
      exact polyVal_le _ _
  | zero =>
    change pointVal x (T.map 0)≤1
    simp
  | one =>
    change pointVal x (T.map 1)≤1
    simp
  | add b c hb hc ihb ihc =>
    change pointVal x (T.map (⟨b,hb⟩ + ⟨c,hc⟩))≤1
    rw [map_add]
    exact ((pointVal x).map_add _ _).trans (max_le ihb ihc)
  | neg b hb ih =>
    change pointVal x (T.map (-⟨b,hb⟩))≤1
    rwa [map_neg,(pointVal x).map_neg]
  | mul b c hb hc ihb ihc =>
    change pointVal x (T.map (⟨b,hb⟩*⟨c,hc⟩))≤1
    rw [map_mul,map_mul]
    exact mul_le_one' ihb ihc
private def seedConst (r :L) :seedRing F γ :=
 ⟨algebraMap L Cq.E r,by
   by_cases hr :r=0
   · simp [hr]
   · exact ((F.place γ).on_constants r hr).le⟩
private theorem seedConst_map (T:Chart A γ hγ B) (r :L) :
  T.map (A.inChart γ (seedConst (F:=F) r))=phys (C r) := by
 rw [T.seed]
 congr 2
 change ((F.atPlace γ hγ) (algebraMap L Cq.E r)).coeff 0=r
 rw [AlgHom.commutes,LaurentSeries.algebraMap_apply,HahnSeries.C_apply]
 exact HahnSeries.coeff_single_same _ _
structure MarkData (T:Chart A γ hγ B) (x :L) where
 loc:MarkLocal T x
 seed :seedRing F γ →+* loc.ring
 seed_coe : ∀ c,(seed c:A.M)=algebraMap Cq.E A.M (c:Cq.E)
 seed_map : ∀ c,loc.map (seed c)=phys (C ((F.atPlace γ hγ (c:Cq.E)).coeff 0))
 x_map :loc.map ⟨A.x,loc.x_mem⟩=phys z7y
 y_map :loc.map ⟨A.y,loc.y_mem⟩=phys (j9 (S γ))
def build (T:Chart A γ hγ B) (x :L) (hx :B.eval x=0) :MarkData T x := by
  let J:=localize (A.bY γ) T.map x
  let a :=A.chartRatio γ 0
  let G:=linear (C:L →+* L[X]) A.a (markJet S γ)
  have hg:pointVal x (phys G)=1 :=polyVal_eq x (T.avoids x hx)
  have ha :pointVal x (T.map a)=1 := by
    rw [T.F8,show markJet S γ 0=1 from rfl,map_one,map_div₀,map_one,hg,div_one]
  let inc:A.bY γ →+* J.ring :=
    (A.bY γ).subtype.codRestrict J.ring fun b =>
      (J.mem_iff _).2 ⟨b,1,by simp,by simp⟩
  have hinc (b:A.bY γ) :J.map (inc b)=T.map b:= by
    simpa only [map_one,div_one] using J.map_div b 1 (by simp) (inc b) (by simp [inc])
  have hcoordinate (i:Fin 4) (u:A.M) (s :L[X])
      (hu:coords F.f A.x A.y i=u*A.polar) (hs :markJet S γ i=s) :
      ∃ h:u∈J.ring,J.map ⟨u,h⟩=phys s := by
    have he :u=(A.chartRatio γ i:A.M)/(a :A.M) := by
      change u=A.ratio i/A.ratio 0
      rw [Pencil.ratio,Pencil.ratio,div_div_div_cancel_right₀ A.gauge_ne,hu,
        show coords F.f A.x A.y 0=A.polar from rfl,mul_div_cancel_right₀ _ A.polar_ne]
    refine ⟨(J.mem_iff u).2 ⟨_,_,ha,he⟩,(J.map_div _ _ ha _ he).trans ?_⟩
    have hg' : phys G≠0:= by
      intro h
      rw [h,map_zero] at hg
      exact zero_ne_one hg
    rw [T.F8,T.F8,hs,show markJet S γ 0=1 from rfl,map_one,
      div_div_div_cancel_right₀ hg',div_one]
  have hX:=hcoordinate 1 A.x z7y rfl rfl
  have hY:=hcoordinate 2 A.y (j9 (S γ)) rfl rfl
  have hJ:=hcoordinate 3 (slope A) (j9 (S γ)).derivative
    (by change _=(-_/_)*_; rw [div_mul_cancel₀ _ A.polar_ne]; rfl) rfl
  have hxMap:=hX.choose_spec
  have hyMap:=hY.choose_spec
  let hxJ:=hX.choose
  let hyJ:=hY.choose
  let xc:J.ring :=⟨A.x,hxJ⟩
  let sc (r :L) :=A.inChart γ (seedConst (F:=F) r)
  let t (r :L) :J.ring :=xc - inc (sc r)
  have ht (r :L) :J.map (t r)=phys (z7y - C r) := by
    change J.map (xc - inc (sc r))= _
    rw [map_sub,show J.map xc= _ from hxMap,hinc]
    change phys z7y - T.map (A.inChart γ (seedConst (F:=F) r))= _
    rw [seedConst_map,map_sub]
  have htc (r :L) : (t r :A.M)=shift A r :=rfl
  let loc:MarkLocal T x :=
    { ring :=J.ring
      fractions :=J.mem_iff
      map :=J.map
      regular := fun b=> by
        obtain ⟨c,d,hd,he⟩:=(J.mem_iff b).mp b.property
        rw [J.map_div c d hd b he,map_div₀,hd,div_one]
        exact c7Q T x hx c
      ic:=t
      gqx :=htc
      shifted_map :=ht
      shifted_inv := fun r hr=> by
        obtain ⟨b,c,hc,he⟩:=(J.mem_iff _).mp (t r).property
        have hv :pointVal x (T.map b)=1 := by
          have hv :=polyVal_eq x (f :=z7y - C r) (by
            simpa only [eval_sub,eval_X,eval_C,sub_ne_zero] using Ne.symm hr)
          rw [← ht r,J.map_div b c hc (t r) he,map_div₀,hc,div_one] at hv
          exact hv
        exact (J.mem_iff _).2 ⟨c,b,hv,by rw [← htc,he,inv_div]⟩
      x_mem:=hxJ
      y_mem:=hyJ
      slope_mem:=hJ.choose }
  exact ⟨loc,inc.comp (A.inChart γ),fun _=>rfl,fun c=>(hinc _).trans (T.seed c),
    hxMap,hyMap⟩
end
end qOHrlse
end
section
set_option backward.isDefEq.respectTransparency false
namespace qOHrlse
noncomputable section
open Polynomial
open P5 (K)
open cu (L j9)
open P5_7_7 (phys)
open qb0hmCe (CurveModel cLN)
open q1kuFjb (expansion_coeff integralSeries mapTwice residue fWQ)
open qNu3xvc (seedDerivative)
open qoCymac (LocalDerivation)
open qhFwyvc (nC)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation atPolynomial)
open qLXroAb (Pencil Chart seedRing evalXY)
open qZn79Eb (LocalFormula numerator)
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
private def m8 {R T:Type} [za6 R] [za6 T] (f :R →+* T)
  (x y :T) :R[X][X] →+* T :=
 eval₂RingHom (eval₂RingHom f x) y
private theorem eval_comp {R T U:Type} [za6 R] [za6 T] [za6 U]
  (f :R →+* T) (k :T →+* U) (x y :T) (g:R[X][X]) :
  k (m8 f x y g)=m8 (k.comp f) (k x) (k y) g:= by
 change k (g.eval₂ (eval₂RingHom f x) y)=g.eval₂ (eval₂RingHom (k.comp f) (k x)) (k y)
 rw [hom_eval₂]
 congr 1
 apply zz4
 intro h
 change k (h.eval₂ f x)=h.eval₂ (k.comp f) (k x)
 rw [hom_eval₂]
private theorem eval_coeff_map {R T U:Type} [za6 R] [za6 T] [za6 U]
  (f :R →+* T) (k :T →+* U) (x y :U) (g:R[X][X]) :
  m8 k x y (mapTwice f g)=m8 (k.comp f) x y g:= by
 change (g.map (mapRingHom f)).eval₂ (eval₂RingHom k x) y =
  g.eval₂ (eval₂RingHom (k.comp f) x) y
 rw [eval₂_map]
 congr 1
 exact zz4 fun h=>eval₂_map f k x
private theorem physical_eval :
   eval₂RingHom (phys.comp (C:L →+* L[X])) (phys z7y)=phys := by
 apply Polynomial.ringHom_ext
 · intro c
   simp only [coe_eval₂RingHom,eval₂_C,zQb]
 · exact eval₂_X _ _
private theorem coeff_map₂ {R T:Type} [za6 R] [za6 T] (f :R →+* T)
  (g:R[X][X]) (i j:ℕ) : ((mapTwice f g).coeff i).coeff j=f ((g.coeff i).coeff j) := by
 simp only [mapTwice,coe_mapRingHom,coeff_map]
private theorem coeff_seedDeriv {E :Type} [zrb E] [zZE L E]
  (D:Derivation L E E) (g:E[X][X]) (i j:ℕ) :
  (((seedDerivative D g).coeff i).coeff j)=D ((g.coeff i).coeff j) := by
 rw [seedDerivative,sum_coeff _ (by simp [Polynomial.sum_def]),sum_coeff _ (by simp)]
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S} {A:Pencil F} {γ:K} {V:Variation F} {hγ:γ∈V.marks}
 {T:Chart A γ (V.Bp hγ) (V.den γ)} {x :L}
private theorem formula (J:MarkData T x) (D:Derivation L Cq.E Cq.E)
   (hD:LocalDerivation (F.atPlace γ (V.Bp hγ)) (F.place γ) D) :
   Nonempty (LocalFormula J.loc D (V.num γ)) := by
 let w:=F.place γ
 let a :=F.atPlace γ (V.Bp hγ)
 let ι:=w.value.valuationSubring.subtype
 let ρ:seedRing F γ →+* L :=
   residue.comp ((a.toRingHom.comp ι).codRestrict _ fun c =>
     (integralSeries (a c) ((F.value γ (V.Bp hγ) c).symm.trans_le c.property)).property)
 have hρ (c:seedRing F γ) :ρ c=(a (c:Cq.E)).coeff 0:=fWQ _
 obtain ⟨g,hg⟩:=qhFwyvc.j9 w F.f (F.integral γ (V.Bp hγ))
 obtain ⟨n,hn⟩:=qhFwyvc.j9 w (seedDerivative D F.f) (fun i j=> by
   rw [coeff_seedDeriv]
   exact (hD _ (F.integral γ (V.Bp hγ) i j)).1)
 have hg:mapTwice ι g=F.f :=hg
 have hn:mapTwice ι n=seedDerivative D F.f :=hn
 have hred (b:nC w) :mapTwice ρ b=cLN a 0 (mapTwice ι b) := by
   apply zXJ
   intro i
   apply zXJ
   intro j
   rw [coeff_map₂,expansion_coeff,coeff_map₂,hρ]
   rfl
 have hnred:mapTwice ρ n=cLN a 1 F.f := by
   apply zXJ
   intro i
   apply zXJ
   intro j
   rw [coeff_map₂,hρ,expansion_coeff]
   have he :=congrArg (fun b:Cq.E[X][X]=>(b.coeff i).coeff j) hn
   rw [coeff_map₂,coeff_seedDeriv] at he
   change (a (ι ((n.coeff i).coeff j))).coeff 0= _
   rw [he]
   exact (hD _ (F.integral γ (V.Bp hγ) i j)).2
 have hder {R U:Type} [za6 R] [za6 U] (f :R →+* U) (b:R[X][X]) :
     mapTwice f b.derivative=(mapTwice f b).derivative :=
   (derivative_map b (mapRingHom f)).symm
 let xc:J.loc.ring :=⟨A.x,J.loc.x_mem⟩
 let yc:J.loc.ring :=⟨A.y,J.loc.y_mem⟩
 let test :=m8 J.seed xc yc
 have hgen (b:nC w) : (test b:A.M)=evalXY (mapTwice ι b) A.x A.y := by
   have hc:J.loc.ring.subtype.comp J.seed=(algebraMap Cq.E A.M).comp ι :=
     zz4 J.seed_coe
   change J.loc.ring.subtype (m8 J.seed xc yc b)= _
   rw [eval_comp,hc,← eval_coeff_map]
   rfl
 have hspec (b:nC w) :J.loc.map (test b)=atPolynomial (mapTwice ρ b) (S γ) := by
   have hc:J.loc.map.comp J.seed=(phys.comp C).comp ρ :=
     zz4 fun c=>(J.seed_map c).trans (congrArg (fun l=>phys (C l)) (hρ c).symm)
   change J.loc.map (m8 J.seed xc yc b)= _
   rw [eval_comp,hc,show J.loc.map xc= _ from J.x_map,show J.loc.map yc= _ from J.y_map,
     ← eval_coeff_map]
   simp only [m8,physical_eval,atPolynomial,coe_eval₂RingHom]
 refine ⟨{
   num := -(test n)
   sep:=test g.derivative
   num_eq := ?_
   sep_eq := by rw [hgen,hder,hg]
   simple := by rw [hspec,hder,hred,hg]; exact V.simple γ hγ
   formula := ?_ }⟩
 · rw [Subring.coe_neg,hgen,hn,numerator]
 · rw [map_neg,hspec,hspec,hnred,hder,hred,hg,neg_div]
   exact (V.formula γ hγ).symm
theorem proof :qZn79Eb.c1 := by
 intro q Cq z S F A V γ hγ T x D hx hD
 let J:=build T x hx
 exact ⟨J.loc,formula (hγ:=hγ) J D hD⟩
end
end qOHrlse
end
section
set_option autoImplicit true
namespace q6kkC0d
theorem proof :qeBKasb.c1 :=
 qOHrlse.proof
end q6kkC0d
end
end
