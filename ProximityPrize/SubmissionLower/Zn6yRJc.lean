import ProximityPrize.SubmissionLower.ZUihISc
import ProximityPrize.SubmissionLower.ZvIWsYa
import ProximityPrize.SubmissionLower.ZTOnaha
set_option Elab.async false
open _root_ renaming Finset.filter_subset → zT0, Finset.prod_congr → zX3, Finset.prod_filter_mul_prod_filter_not → zeW, Finset.range → z4x, Finset.sum_eq_zero → zYF, Finsupp.add_apply → zSs, Fintype.linearCombination_apply → zGl, LinearIndependent → z14, LinearMap.finrank_range_add_finrank_ker → z7i, Module.finrank → zsE, MvPolynomial.X → z9v, MvPolynomial.weightedTotalDegree_piSingle → z5e, Nat.pos_of_ne_zero → zOl
section
set_option autoImplicit true
namespace qajFMeb
noncomputable section
open aR (ao)
open xE (Flag)
open akL (MI Jp BU Oq eAc azA)
open qnnEPee
open MvPolynomial
private def point (e :Jp) :Fin 4→ao :=
  ![1,(coordU e :ao),(coordV e :ao),(coordW e :ao)]
private def cU (i:Fin 4) (s k :ℕ) :MI :=
  ∏ j∈z4x k,(z9v i - C ((s+j:ℕ) :ao))
private theorem fall_at (n s k :ℕ) (hs :s≤n) :
    (∏ j∈z4x k,((n:ao)-((s+j:ℕ) :ao))) =
      (k.factorial:ao)*((n - s).choose k :ao) := by
  by_cases h:k≤n - s
  · rw [← Nat.cast_mul,← Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_prod_range,Nat.cast_prod]
    apply zX3 rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.cast_sub (show j≤n - s by omega),Nat.cast_sub hs,Nat.cast_add,sub_sub]
  · have hlt:n - s<k := by omega
    rw [Nat.choose_eq_zero_of_lt hlt,Nat.cast_zero,mul_zero]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hlt) (by
      rw [show s+(n - s)=n by omega,sub_self])
private theorem bFo (x :Fin 4→ao) (i:Fin 4) (n s k :ℕ)
    (hx :x i=(n:ao)) (hs :s≤n) :
    eval x (cU i s k)=(k.factorial:ao)*((n - s).choose k :ao) := by
  simpa only [cU,map_prod,map_sub,eval_X,eval_C,hx] using fall_at n s k hs
private theorem fall_bound (i:Fin 4) (s k :ℕ) :
    cU i s k∈restrictWeightedDegree Oq (k*Oq i) := by
  induction k with
  | zero=>simpa [cU] using C_mem_restrictWeightedDegree Oq 0 (1 :ao)
  | succ k ih =>
    have hf :z9v i - C ((s+k :ℕ) :ao) ∈
        restrictWeightedDegree Oq (Oq i) :=
      (restrictWeightedDegree (R:=ao) Oq (Oq i)).sub_mem
        (X_mem_restrictWeightedDegree (R:=ao) Oq _ i le_rfl)
        (C_mem_restrictWeightedDegree Oq _ ((s+k :ℕ) :ao))
    simpa only [cU,Finset.prod_range_succ,Nat.succ_mul,one_mul] using
      mul_mem_restrictWeightedDegree ih hf
private def row (a :Jp) :MI :=
  C ((-1 :ao)^(a 1+a 3))*cU 1 (a 3+a 2) (a 1) *
    cU 2 (a 3) (a 2)*cU 3 0 (a 3)
private def scale (a :Jp) :ao :=
  ((a 1).factorial:ao)*((a 2).factorial:ao)*((a 3).factorial:ao)
private theorem fZo (a :Jp) :row a∈restrictWeightedDegree Oq (a.weight Oq) := by
  rw [exp_weight]
  have h:=mul_mem_restrictWeightedDegree (mul_mem_restrictWeightedDegree (mul_mem_restrictWeightedDegree
      (C_mem_restrictWeightedDegree Oq 0 ((-1 :ao)^(a 1+a 3)))
      (fall_bound 1 (a 3+a 2) (a 1))) (fall_bound 2 (a 3) (a 2))) (fall_bound 3 0 (a 3))
  change row a∈restrictWeightedDegree Oq (0+a 1*1+a 2*2+a 3*3) at h
  simpa only [zero_add,mul_one] using h
private theorem row_eval (a e :Jp) (hg:a.weight BU=e.weight BU) :
    eval (point e) (row a)=scale a*(tailMonomial e).coeff a := by
  rw [tail_coeff e a hg]
  simp only [row,map_mul,eval_C,bFo (point e) 3 (coordW e) 0 (a 3) rfl (Nat.zero_le _),Nat.sub_zero]
  by_cases h3:a 3≤ coordW e
  · have hv :a 3≤ coordV e := by unfold coordV; simpa [coordW] using h3.trans (Nat.le_add_left _ _)
    rw [bFo (point e) 2 (coordV e) (a 3) (a 2) rfl hv]
    by_cases h2 :a 2≤ coordV e-a 3
    · have hu:a 3+a 2≤ coordU e := by unfold coordV at hv h2; unfold coordU; omega
      rw [bFo (point e) 1 (coordU e) (a 3+a 2) (a 1) rfl hu,← Nat.sub_sub,scale]
      ac_rfl
    · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h2)]
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h3)]
private theorem factorial_ne_zero {n:ℕ} (hn:n≤1710) : (n.factorial:ao)≠0:= by
  have :CharP ao 2130706433 :=
    charP_of_injective_algebraMap (R:=K1.K) (A:=ao) aR.embed.injective 2130706433
  induction n with
  | zero=>simp
  | succ n ih =>
    rw [Nat.factorial_succ,Nat.cast_mul]
    refine mul_ne_zero ?_ (ih (by omega))
    intro h
    have hd:=(CharP.cast_eq_zero_iff ao 2130706433 (n+1)).mp h
    have :=Nat.le_of_dvd (Nat.succ_pos n) hd
    omega
private def pad (L:ℕ) (a :Jp) :Jp :=
  a.erase 0+Finsupp.single 0 (L-(a 1+a 2+a 3))
private theorem pad_zero (L:ℕ) (a :Jp) :pad L a 0=L-(a 1+a 2+a 3) := by
  simp [pad,zSs]
private theorem pad_ne (L:ℕ) (a :Jp) {i:Fin 4} (hi:i≠0) :pad L a i=a i:= by
  simp [pad,zSs,Finsupp.erase_ne hi,Finsupp.single_eq_of_ne hi]
private theorem pad_mem (F:Flag) (a :Jp) (ha :a.weight Oq<F.lower.toNat) :
    pad (F.lower - 1).toNat a∈momentColumns F:= by
  rw [momentColumns,azA]
  change ((pad _ a).weight BU:ℤ)=F.lower - 1 ∧
    ((pad _ a).weight Oq:ℤ)≤F.lower - 1
  rw [exp_weight] at ha
  rw [exp_grade,exp_weight]
  simp only [pad_zero,pad_ne _ _ (show (1 :Fin 4)≠0 by decide),
    pad_ne _ _ (show (2 :Fin 4)≠0 by decide),pad_ne _ _ (show (3:Fin 4)≠0 by decide)]
  omega
private theorem eval_moment (L:ℕ) (a e :Jp) (r :ao) :
    eval (point e) (monomial a r)=r*momentValue (pad L a) e := by
  rw [eval_monomial,Finsupp.prod_fintype _ _ (fun _=>pow_zero _),Fin.prod_univ_four]
  simp [point,momentValue,pad_ne,mul_assoc]
private theorem moment_sum_eq_zero (F:Flag) (v :Tail F→ao)
    (hv :momentMap F (momentColumns F) v=0) (p:MI)
    (hp : ∀ a∈p.support,a.weight Oq<F.lower.toNat) :
    ∑ e :Tail F,v e*eval (point e.val) p=0:= by
  let L:MI →ₗ[ao] ao := ∑ e :Tail F,v e•(aeval (point e.val)).toLinearMap
  have hL (q:MI) :L q = ∑ e :Tail F,v e*eval (point e.val) q:= by
    simp only [L,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
      AlgHom.toLinearMap_apply,aeval_eq_eval]
  rw [← hL]
  rw [p.as_sum,map_sum]
  apply zYF
  intro a ha
  let b : ↥(momentColumns F) :=⟨pad (F.lower - 1).toNat a,pad_mem F a (hp a ha)⟩
  have hb:=congrFun hv b
  simp only [momentMap,zGl,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Pi.zero_apply] at hb
  rw [hL]
  simp only [eval_moment (F.lower - 1).toNat]
  calc
    _=p.coeff a * ∑ e :Tail F,v e*momentValue b.val e.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ac_rfl
    _=0:= by rw [hb,mul_zero]
theorem proof :qnnEPee.c1 := by
  intro F _ hsmall v hv
  apply LinearMap.mem_ker.mpr
  apply MvPolynomial.ext
  intro a
  change (weightedTruncation Oq F.lower.toNat (tailMap F v)).coeff a=0
  rw [coeff_weightedTruncation]
  by_cases ha :a.weight Oq<F.lower.toNat
  · rw [ite_eq_left ha,tailMap,zGl,coeff_sum]
    simp only [coeff_smul,smul_eq_mul]
    by_cases hg: (a.weight BU:ℤ)=F.degree
    · have hsum:=moment_sum_eq_zero F v (LinearMap.mem_ker.mp hv) (row a) fun b hb =>
        lt_of_le_of_lt (mem_restrictWeightedDegree.mp (fZo a) b hb) ha
      have hm : ∑ e :Tail F,v e*eval (point e.val) (row a) =
          scale a * ∑ e :Tail F,v e*(tailMonomial e.val).coeff a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        have he : (e.val.weight BU:ℤ)=F.degree :=
          (eAc.mp (Finset.mem_filter.mp e.property).1).1
        rw [row_eval a e.val (by omega)]
        ac_rfl
      rw [hm] at hsum
      rw [exp_weight] at ha
      exact (mul_eq_zero.mp hsum).resolve_left <| mul_ne_zero
        (mul_ne_zero (factorial_ne_zero (by omega)) (factorial_ne_zero (by omega)))
        (factorial_ne_zero (by omega))
    · apply zYF
      intro e _
      have hz : (tailMonomial e.val).coeff a=0:= by
        by_contra hn
        exact hg ((tailMonomial_support F e).1 (mem_support_iff.mpr hn)).1
      rw [hz,mul_zero]
  · rw [ite_eq_right ha]
end
end qajFMeb
end
section
set_option autoImplicit true
namespace qP9LnAa
noncomputable section
open Polynomial K1 aR
open jA (kH jK iP mA gY bC)
open acZ (Bu cfL)
open axa (Exponent weight arX)
open P6_6_4 (Ga Source E3 RF)

open bAl (bxL)
open scoped BigOperators
open private aV b8T bqa boundary bVx cU3 from ProximityPrize.SubmissionLower.S
open private Ly from ProximityPrize.SubmissionLower.A2
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
private def akn {Γ s} (w:I→K) (P:jF Γ s) (L:kH P) (t:ℕ) :
    Submodule ao jK :=
  aV w P L t ⊓
    ((MvPolynomial.restrictWeightedDegree (R:=iP)
      (Pi.single (none :mA) 1) 40000).restrictScalars ao).comap Bu
private theorem bsC {Γ s} (w:I→K) (P:jF Γ s) (L:kH P)
    (t:ℕ) (F:jK) :F∈akn w P L t↔Source w P L Ga t F:= by
  classical
  simp only [akn,Submodule.mem_inf,b8T,Submodule.mem_comap,
    Submodule.restrictScalars_mem,cfL,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    z5e,Source]
  change jA.Source w P L Ga t F∧gY (bC F)≤40000 ↔
    jA.Source w P L Ga t F∧gY F≤40000
  rw [bxL]
private instance {Γ s} (w:I→K) (P:jF Γ s) (L:kH P) (t:ℕ) :
    Module.Finite ao (akn w P L t) := by
  have :FiniteDimensional ao ↥(aV w P L t) :=bqa w P L t
  have h:akn w P L t≤aV w P L t:=inf_le_left
  exact FiniteDimensional.of_injective (K:=ao) (V := ↥(akn w P L t))
    (V₂ := ↥(aV w P L t)) (Submodule.inclusion h) (Submodule.inclusion_injective h)
private def aff {Γ s} (w:I→K) (P:jF Γ s) (L:kH P) (t:ℕ) :
    akn w P L t →ₗ[ao] (Exponent→ao) :=
  (boundary P.H.natDegree t).comp (akn w P L t).subtype
private theorem brp {Γ s} (w:I→K) (P:jF Γ s) (L:kH P) (t:ℕ) :
    zsE ao (aff w P L (t+1)).ker ≤
      zsE ao (akn w P L t) := by
  let f :=(akn w P L (t+1)).subtype.comp (aff w P L (t+1)).ker.subtype
  have hm (F: (aff w P L (t+1)).ker) :f F∈akn w P L t:= by
    obtain ⟨⟨hc,hcut,hphys,hpole⟩,hseed⟩:=(bsC w P L _ _).mp F.val.property
    have hz :boundary P.H.natDegree (t+1) F.val.val=0:=LinearMap.mem_ker.mp F.property
    apply (bsC w P L _ _).mpr
    refine ⟨⟨hc,fun m hm => ?_,hphys,hpole⟩,hseed⟩
    have h:=bVx hcut hz m hm
    change ((F.val.val).coeff m).natDegree+weight P.H.natDegree m≤t+arX*P.H.natDegree
    omega
  apply LinearMap.finrank_le_finrank_of_injective (f :=f.codRestrict _ hm)
  intro F G he
  have heq :=congrArg (fun Q:akn w P L t=>Q.val) he
  exact Subtype.ext (Subtype.ext heq)
theorem proof :qIkXmGe.c1 := by
  classical
  intro w Γ s P L hr
  let r (t:ℕ) :=zsE ao (aff w P L t).range
  refine ⟨r,?_,fun t _ => ?_⟩
  · have hzero : (aff w P L 0).ker = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro F hz
      have hsrc :=(bsC w P L _ _).mp F.property
      refine Subtype.ext (Ly Γ s P L F.val
        (fun m hm => ?_) hsrc.1.2.2.2)
      simpa only [Nat.zero_add] using bVx hsrc.1.2.1 hz m hm
    have hsum (t:ℕ) :zsE ao (akn w P L t) ≤
        ∑ v∈z4x (t+1),r v := by
      induction t with
      | zero =>
        have h:=z7i
          (K:=ao) (V:=akn w P L 0) (V₂:=Exponent→ao) (aff w P L 0)
        rw [hzero,finrank_bot,Nat.add_zero] at h
        simpa only [Nat.zero_add,Finset.sum_range_one] using h.ge
      | succ t ih =>
        have h:=z7i
          (K:=ao) (V:=akn w P L (t+1)) (V₂:=Exponent→ao) (aff w P L (t+1))
        rw [Finset.sum_range_succ,← h,add_comm]
        exact Nat.add_le_add (le_trans (brp w P L t) ih) le_rfl
    obtain ⟨e,he,hmem⟩:=hr
    have hi:z14 ao
        (fun i=>(⟨e i,(bsC w P L _ _).mpr (hmem i)⟩:akn w P L E3)) :=
      LinearIndependent.of_comp (akn w P L E3).subtype he
    exact (by simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank :
      RF≤Module.finrank ao (akn w P L E3)).trans (hsum E3)
  · let b:=Module.finBasis ao (aff w P L t).range
    choose e he using fun i:Fin (r t)=>LinearMap.mem_range.mp (b i).property
    have hsrc (i:Fin (r t)) :Source w P L Ga t (e i).val :=
      (bsC w P L _ _).mp (e i).property
    refine ⟨fun i=>bC (e i).val,
      cU3 (fun i=>(e i).val) (fun i=>(hsrc i).1.2.1) ?_,
      fun i=>Submodule.subset_span ⟨(e i).val,hsrc i,rfl⟩⟩
    have h:z14 ao (fun i=>(b i).val) :=
      b.linearIndependent.map' (aff w P L t).range.subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i=>boundary P.H.natDegree t (e i).val)=fun i=>(b i).val :=funext he
    rwa [heq]
end
end qP9LnAa
end
section
set_option autoImplicit true
namespace qlhCp6d
noncomputable section
open aR (Shape)
open jA hiding ahD Ga awY
open acZ (asW)
open P6_6_4 (ahD awY)

open scoped Polynomial BigOperators
open private a7b c5R c5S cEa from ProximityPrize.SubmissionLower.S
private theorem c54 {a :Shape} {u:ℕ} {F Q:ko} (hF:F≠0)
    (hc:Jn a F) (hs :gY F≤u) (hd:Q∣F) :
    vC Q≤a.b∧lP Q≤a.j∧gY Q≤u:= by
  classical
  have hcap:=cEa hF hc hd
  have hseed :gY Q≤gY F:= by
    simpa only [z5e,gY] using
      MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none :mA) 1) hd hF
  exact ⟨hcap.1,hcap.2.1,hseed.trans hs⟩
theorem proof :qIkXmGe.c2 := by
  intro F G hF hG hFCap hFSeed hGCap hfixed hmoving
  classical
  let _:StrongNormalizationMonoid ko :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let _:GCDMonoid ko:=UniqueFactorizationMonoid.toGCDMonoid ko
  let g:=gcd F G
  have hg:g≠0:=gcd_ne_zero_of_left hF
  let N :=UniqueFactorizationMonoid.normalizedFactors g
  let A:=N.toFinset
  let pureFactors :=A.filter (fun f=>vC f=0)
  let jetFactors :=A.filter (fun f => ¬ vC f=0)
  let fixed:=jetFactors.filter (fun f=>gY f=0)
  let moving:=jetFactors.filter (fun f => ¬ gY f=0)
  let powCount:ko→ℕ:=N.count
  let pure :iP[X] := ∏ f∈pureFactors,(a7b f)^powCount f
  have hpure :YB pure = ∏ f∈pureFactors,f^powCount f := by
    let φ:iP[X] →+* ko :=
      Polynomial.eval₂RingHom MvPolynomial.C (z9v none)
    change φ (∏ f∈pureFactors,(a7b f)^powCount f)= _
    rw [map_prod]
    refine zX3 rfl fun f hf => ?_
    rw [map_pow]
    exact congrArg (fun R=>R^powCount f)
      (c5R (Finset.mem_filter.mp hf).2)
  let D:=YB pure*(∏ f∈fixed,f^powCount f)*(∏ f∈moving,f^powCount f)
  have hD:Associated D g:= by
    suffices D =N.prod by
      rw [this]
      exact UniqueFactorizationMonoid.prod_normalizedFactors hg
    change YB pure*(∏ f∈fixed,f^powCount f) *
      (∏ f∈moving,f^powCount f)= _
    rw [hpure,mul_assoc]
    unfold fixed moving
    rw [zeW]
    unfold pureFactors jetFactors
    rw [zeW]
    exact (Finset.prod_multiset_count N).symm
  have hDne :D ≠0:=ne_zero_of_dvd_ne_zero hg hD.dvd
  have hDF:D ∣F:=hD.dvd.trans (gcd_dvd_left F G)
  have hDG:D ∣G:=hD.dvd.trans (gcd_dvd_right F G)
  obtain ⟨F',hF'⟩:=hDF
  obtain ⟨G',hG'⟩:=hDG
  have hl:F' ≠ 0:=right_ne_zero_of_mul (hF' ▸ hF)
  have hr :G' ≠ 0:=right_ne_zero_of_mul (hG' ▸ hG)
  have hrel :IsRelPrime F' G' := by
    intro d hdF hdG
    have hdF' : D *d∣F:=hF' ▸ mul_dvd_mul_left D hdF
    have hdG' : D *d∣G:=hG' ▸ mul_dvd_mul_left D hdG
    have hd:=(dvd_gcd hdF' hdG').trans hD.symm.dvd
    apply isUnit_of_dvd_one
    exact (mul_dvd_mul_iff_left hDne).mp (by simpa only [mul_one] using hd)
  have hcommon (f :ko) (hf :f∈A) :f∣F∧f∣G:= by
    have hfg:f∣g:=UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hf)
    exact ⟨hfg.trans (gcd_dvd_left F G),hfg.trans (gcd_dvd_right F G)⟩
  have hmake (b:Bool) (B:Finset ko) (hBA:B⊆A)
      (hj : ∀ f∈B,0<vC f)
      (hs : ∀ f∈B,if b then 0<gY f else gY f=0) :
      asW b B:= by
    refine ⟨?_,?_,hj,hs⟩
    · intro f hf q hq hne hassoc
      exact hne (UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
        (Multiset.mem_toFinset.mp (hBA hf)) (Multiset.mem_toFinset.mp (hBA hq)) hassoc)
    · intro f hf
      exact UniqueFactorizationMonoid.irreducible_of_normalized_factor _
        (Multiset.mem_toFinset.mp (hBA hf))
  have hfixedA:fixed⊆A:=(zT0 _ _).trans (zT0 _ _)
  have hmovingA:moving⊆A:=(zT0 _ _).trans (zT0 _ _)
  have hfix :=hmake false fixed hfixedA
    (fun _ hf=>zOl (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf=>(Finset.mem_filter.mp hf).2)
  have hmov :=hmake true moving hmovingA
    (fun _ hf=>zOl (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf=>zOl (Finset.mem_filter.mp hf).2)
  obtain ⟨hft,hfi⟩:=hfixed fixed hfix (fun f hf=>hcommon f (hfixedA hf))
  obtain ⟨hmt,hmi,hms,hlow⟩:=hmoving moving hmov (fun f hf=>hcommon f (hmovingA hf))
  have hpureF:YB pure∣F :=
    (show YB pure∣D by
      exact ⟨_,mul_assoc _ _ _⟩).trans ⟨F',hF'⟩
  have hpure_ne :pure≠0:= by
    intro hz
    apply hDne
    simp [D,hz,YB]
  refine ⟨{
    fixed:=fixed
    moving:=moving
    pure :=pure
    exponent:=powCount
    left:=F'
    right:=G'
    pure_ne :=hpure_ne
    pure_degree :=(c5S hF hpureF).trans (hFSeed.trans (by decide))
    fixed_kind := fun f hf=>⟨hfix.irreducible f hf,hfix.Bo f hf,hfix.seed f hf⟩
    moving_kind := fun f hf=>⟨hmov.irreducible f hf,hmov.Bo f hf,hmov.seed f hf,hlow f hf⟩
    fixed_total:=hft
    fixed_index :=hfi
    moving_total:=hmt
    moving_index :=hmi
    moving_seed :=hms
    azo:=hF'
    az7:=hG'
    left_ne :=hl
    right_ne :=hr
    proper :=hrel
    left_caps :=c54 hF hFCap hFSeed ⟨D,hF'.trans (mul_comm _ _)⟩
    right_caps :=c54 hG hGCap.1 hGCap.2 ⟨D,hG'.trans (mul_comm _ _)⟩
  }⟩
end
end qlhCp6d
end
