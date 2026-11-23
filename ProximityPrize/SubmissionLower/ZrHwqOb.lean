import ProximityPrize.SubmissionLower.Z3wMysc
import ProximityPrize.SubmissionLower.ZFO2WXb
import ProximityPrize.SubmissionLower.P5_7_1_3_1Proof
import ProximityPrize.SubmissionLower.ZjZXRjd
import ProximityPrize.SubmissionLower.Z7znM4a
import ProximityPrize.SubmissionLower.Z1LucWb
set_option Elab.async false
open _root_ renaming Finset.range → z4x, Finsupp.mapDomain → z8D, LinearIndependent → z14, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.C → znf, MvPolynomial.coeff_C_mul → z06, MvPolynomial.le_degreeOf_of_mem_support → zTo, MvPolynomial.le_weightedTotalDegree → z6P, Nat.le_div_iff_mul_le → z1g, Nat.mul_le_mul_left → zBI, Nat.sub_add_cancel → zxt, Polynomial.map_add → zS4, Polynomial.map_mul → zNl, Submodule.mem_iInf → zxR
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q0Nj7Rb
noncomputable section
open Polynomial
open P6 (p)
open P6_7_3 (Input emz)
open qlc9qed (Bank mem_ambient bsz powerAt)
open aR (ao)
open jA Rk
open aA0 (cEb c4E)
open private trueCut_shift from ProximityPrize.SubmissionLower.ZTFKldb
open private a8W dxN from ProximityPrize.SubmissionLower.S
open private line b7T cYc ct4 c40 from ProximityPrize.SubmissionLower.A3
theorem shift {x :Input} (P:OnePole x) (b:Bank) {t F}
    (hF:F∈aV P b t) (i:ℕ) :
    Yd P.data.H i F∈aV P b (t+(3*x.h)*i) := by
  obtain ⟨hA,hC,hP⟩:=Submodule.mem_inf.mp hF
  obtain ⟨hc,hs,hw⟩:=mem_ambient.mp hA
  refine Submodule.mem_inf.mpr ⟨mem_ambient.mpr ⟨cEb P.data.H i F b.box hc,?_,?_⟩,?_,?_⟩
  · rw [gY,MvPolynomial.degreeOf_le_iff]
    intro a ha
    exact (Nat.le_add_left ..).trans
      ((zTo none (a8W ha)).trans hs)
  · rw [← P.height] at hw ⊢
    simpa only [Nat.add_right_comm] using trueCut_shift P.data.H i _ F hw
  · apply (zxR _).mpr
    intro j
    have hj:=(bsz _ _ _ _).mp ((zxR _).mp hC j)
    apply (bsz _ _ _ _).mpr
    intro a
    exact dxN P.data.H i b.m _ _ F hj a
  · exact (NR.aVU _ _ _ _ _).mpr
      (c4E P.data P.bY _ i F ((NR.aVU _ _ _ _ _).mp hP))
theorem bank_mono {x :Input} (P:OnePole x) (b:Bank) {s t:ℕ} (hst:s≤t) :
    aV P b s≤aV P b t:= by
  rintro F ⟨hA,hC⟩
  obtain ⟨hc,hs,hw⟩:=mem_ambient.mp hA
  exact ⟨mem_ambient.mpr ⟨hc,hs,fun a ha=>(hw a ha).trans (Nat.add_le_add_right hst _)⟩,hC⟩
theorem factor_power {x :Input} (P:OnePole x) {G:ko}
    (hi:Irreducible G) (hs :0<G.degreeOf none) (hsmall:G.degreeOf none<p)
    (hdiv : ∀ F∈aV P .strong Bank.strong.cut,G∣bC F) :
    ∀ t≤Bank.strong.cut,∀ F∈aV P .strong t,G^powerAt x.h t∣bC F:= by
  intro t ht F hF
  have hpos :0<3*x.h:= by
    have h:=(emz x).1
    change 2407≤x.h at h
    omega
  apply c40 (line none) (b7T none)
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi) (ct4 hs hsmall)
  intro i hi'
  have hle :i≤(Bank.strong.cut - t)/(3*x.h) := by
    unfold powerAt at hi'
    omega
  have hm: (3*x.h)*i≤Bank.strong.cut - t:= by
    simpa only [Nat.mul_comm] using (z1g hpos).mp hle
  have hcut:t+(3*x.h)*i≤Bank.strong.cut:= by omega
  have hd:=hdiv _ (bank_mono P .strong hcut (shift P .strong hF i))
  rw [cYc]
  have hn:qV (P.data.H^(3*i))≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ao[X] iP)).mpr
      (pow_ne_zero _ P.data.monic.ne_zero)
  have hunit :IsUnit (znf (qV (P.data.H^(3*i))) :ko) :=
    (IsUnit.mk0 _ hn).map znf
  apply hunit.dvd_mul_left.mp
  simpa only [Yd,bC,map_mul,MvPolynomial.map_C] using hd
end
end q0Nj7Rb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q0Nj7Rb
noncomputable section
open P6_7_3 (Input emz)
open qlc9qed (Bank mem_ambient Aw b4I powerAt)
open q6AUWfb (Exponent slots slots_sum bwH dQC)
open aR (ao)
open jA
open acZ (OV bI3 a88 agr bZx)
open axa (weight)
open private multiples mem_multiples from ProximityPrize.SubmissionLower.S
open private boundary bVx cU3 power_le_top seedSpace mem_seedSpace from ProximityPrize.SubmissionLower.ZjZXRjd
open private Lh column column_mem cGZ column_card finite_ambient from ProximityPrize.SubmissionLower.P5_7_1_3_1Proof
open scoped BigOperators
theorem ds9 (b:Bank) (h:ℕ) :
    zAa ao (Aw b h b.cut) ∧
      b.ambientCount h≤zsE ao (Aw b h b.cut) := by
  let V:=Aw b h b.cut
  let:zAa ao V:=finite_ambient b h
  let v (c:Lh b h) :V:=⟨column c,column_mem c⟩
  have hi:z14 ao v :=LinearIndependent.of_comp V.subtype (cGZ b h)
  exact ⟨inferInstance,column_card b h ▸ hi.fintype_card_le_finrank⟩
abbrev aMH :ℕ:=(3*2534)*(3038*665000)
private abbrev total (h t:ℕ) :=t+(Bank.strong.box.b+Bank.strong.box.j)*h
private theorem bank_bounds {x :Input} {P:OnePole x} {t F} (hF:F∈aV P .strong t) :
    Jn Bank.strong.box F∧gY F≤Bank.strong.U∧ahb x.h (total x.h t) F :=
  mem_ambient.mp (Submodule.mem_inf.mp hF).1
private theorem finite_bank {x :Input} (P:OnePole x) {t:ℕ}
    (ht:t≤Bank.strong.cut) :zAa ao (aV P .strong t) := by
  let:FiniteDimensional ao (Aw .strong x.h Bank.strong.cut) :=
    finite_ambient .strong x.h
  have hle :aV P .strong t≤Aw .strong x.h Bank.strong.cut :=
    (bank_mono P .strong ht).trans inf_le_left
  exact FiniteDimensional.of_injective (K:=ao) (V := ↥(aV P .strong t))
    (V₂ := ↥(Aw .strong x.h Bank.strong.cut))
    (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
private def aff {x :Input} (P:OnePole x) (t:ℕ) :
    aV P .strong t →ₗ[ao] (Exponent→ao) :=
  (boundary x.h (total x.h t)).comp (aV P .strong t).subtype
private theorem brp {x :Input} (P:OnePole x) (t:ℕ) (ht:t≤Bank.strong.cut) :
    zsE ao (aff P (t+1)).ker≤zsE ao (aV P .strong t) := by
  let f :=(aV P .strong (t+1)).subtype.comp (aff P (t+1)).ker.subtype
  have hm (F: (aff P (t+1)).ker) :f F∈aV P .strong t:= by
    obtain ⟨hc,hs,hw⟩:=bank_bounds F.val.property
    have hz :boundary x.h (total x.h (t+1)) F.val.val=0:=LinearMap.mem_ker.mp F.property
    refine ⟨mem_ambient.mpr ⟨hc,hs,fun m hmem => ?_⟩,F.val.property.2⟩
    have h:=bVx hw hz hmem
    change (F.val.val.coeff m).natDegree+weight x.h m≤total x.h t
    dsimp only [total] at h ⊢
    omega
  let:zAa ao (aV P .strong t) :=finite_bank P ht
  apply LinearMap.finrank_le_finrank_of_injective (f :=f.codRestrict _ hm)
  intro F G he
  exact Subtype.ext (Subtype.ext (congrArg (fun Q:aV P .strong t=>Q.val) he))
private theorem telescope {x :Input} (P:OnePole x) (h0:aV P .strong 0 = ⊥) (t:ℕ)
    (ht:t≤Bank.strong.cut) :
    zsE ao (aV P .strong t) ≤
      ∑ v∈z4x (t+1),zsE ao (aff P v).range := by
  induction t with
  | zero =>
    rw [h0,finrank_bot]
    exact Nat.zero_le _
  | succ t ih =>
    let:zAa ao (aV P .strong (t+1)) :=finite_bank P ht
    have h:=LinearMap.finrank_range_add_finrank_ker (K:=ao)
      (V:=aV P .strong (t+1)) (V₂:=Exponent→ao) (aff P (t+1))
    rw [Finset.sum_range_succ,← h,add_comm]
    have ht' := Nat.le_of_succ_le ht
    exact Nat.add_le_add ((brp P t ht').trans (ih ht')) le_rfl
private theorem layer_bound {x :Input} (P:OnePole x) (t n:ℕ) (ht:t≤Bank.strong.cut) {G:ko}
    (hg:0<G.degreeOf (some 2))
    (hdvd : ∀ F∈aV P .strong t,G^n∣bC F) :
    zsE ao (aff P t).range≤ slots n:= by
  classical
  let:zAa ao (aV P .strong t) :=finite_bank P ht
  let b:=Module.finBasis ao (aff P t).range
  choose e he using fun i=>LinearMap.mem_range.mp (b i).property
  have hi:z14 ao (fun i=>(b i).val) :=
    b.linearIndependent.map' (aff P t).range.subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have heq : (fun i=>boundary x.h (total x.h t) (e i).val)=fun i=>(b i).val :=funext he
  let V:=OV Bank.strong.box ⊓ seedSpace ⊓ multiples (G^n)
  have hspan:Submodule.span iP (Set.range fun i=>bC (e i).val)≤V:= by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    obtain ⟨hc,hs,_⟩:=bank_bounds (e i).property
    refine ⟨⟨bI3.mpr (a88 hc),mem_seedSpace.mpr ?_⟩,
      mem_multiples.mpr (hdvd _ (e i).property)⟩
    exact b4I.trans_le hs
  refine dQC n _ _ (cU3 (fun i=>(e i).val)
    (fun i=>(bank_bounds (e i).property).2.2) (by rw [heq]; exact hi)) ?_
  intro R hR
  have hm:R∈V:=hspan hR
  exact ⟨bI3.mp hm.1.1,mem_seedSpace.mp hm.1.2,
    fun hn=>power_le_top hg hn (mem_multiples.mp hm.2)⟩
theorem ceiling_bound {x :Input} (P:OnePole x) {G:ko}
    (hg:0<G.degreeOf (some 2))
    (hdvd : ∀ t≤Bank.strong.cut,∀ F∈aV P .strong t,G^powerAt x.h t∣bC F) :
    zsE ao (aV P .strong Bank.strong.cut)≤aMH := by
  obtain ⟨hl,hh⟩:=emz x
  change 2407≤x.h at hl
  change x.h≤2534 at hh
  have he :0<3*x.h:= by omega
  have h0:aV P .strong 0 = ⊥ := by
    apply (aV P .strong 0).eq_bot_iff.mpr
    intro F hF
    by_contra hn
    have hs :=(a88 (bank_bounds hF).1).2.2.1
    change (bC F).degreeOf (some 2)≤19 at hs
    have hd:=power_le_top hg (agr hn) (hdvd 0 (Nat.zero_le _) F hF)
    have hbig:19≤Bank.strong.cut/(3*x.h) := by
      apply (z1g he).mpr
      change 19*(3*x.h)≤21568799
      omega
    simp only [powerAt,Nat.sub_zero] at hd
    omega
  calc
    _ ≤ ∑ t∈z4x (Bank.strong.cut+1),zsE ao (aff P t).range :=
      telescope P h0 _ le_rfl
    _≤(3*x.h) * ∑ k∈z4x 19,slots (1+k) :=
      bZx he _ (fun k=>slots (1+k))
        (fun t ht=>layer_bound P t (powerAt x.h t) ht hg (hdvd t ht))
        (fun k hk=>bwH (by omega))
    _=(3*x.h)*(3038*665000) := by rw [slots_sum]
    _≤(3*2534)*(3038*665000) :=
      Nat.mul_le_mul_right _ (zBI 3 hh)
end
end q0Nj7Rb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace q0Nj7Rb
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open P6 (K)
open P6_7_3 (Input emz)
open P5_7_1 (TopCaps atTop)
open qlc9qed (Bank Aw toTop aD mem_ambient bsz duQ)
open aR (af jF embed extend cK jet)
open jA Rk
open private sum_coeffs from ProximityPrize.SubmissionLower.ZTFKldb
open private gt6 cfm weight_eq_sum aWN from ProximityPrize.SubmissionLower.C
open private d2J from ProximityPrize.SubmissionLower.S
open private eval_rename_top raw_eval_degree from ProximityPrize.SubmissionLower.Z7znM4a
private theorem poleData (x :Input) :
    ∃ P:jF x.Γ x.F.scalar,P.H=x.H∧P.H.natDegree=x.h ∧
      ∀ γ,P.z γ=embed (x.M.label γ) := by
  let M:=x.M
  let z := fun γ:K=>embed (M.label γ)
  obtain ⟨hm,hd,hdiv,_,_,_,_,hnode,_,_,_⟩:=x.bY
  have unit {P:K[X]} (hp:IsCoprime P M.E) :IsCoprime (extend P) x.H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ:K) :extend (M.wK γ)=extend M.A₀+C (z γ)*extend M.A₁:= by
    change (M.A₀+C (M.label γ)*M.A₁).map embed= _
    rw [zS4,zNl,Polynomial.map_C]
  refine ⟨⟨x.H,hm,?_,?_,?_,z,?_,extend M.factor,extend M.Q,extend M.A₀,
    extend M.A₁,unit M.coprime_factor.symm,unit M.offset_reduced,unit M.first_amplitude_unit,
    ?_,?_⟩,rfl,hd,fun _=>rfl⟩
  · rw [hd]
    have h:2407≤x.h∧x.h≤2534 :=emz x
    exact ⟨(by decide :1≤2407).trans h.1,h.2.trans (by decide)⟩
  · exact fun i=>(hnode i).1
  · intro γ hγ
    rw [hd]
    exact P6_7.aic x.F hγ
  · intro a b hab
    exact sub_left_inj.mp (embed.injective hab)
  · intro γ hγ
    rw [← amp]
    exact unit (x.F.mark γ hγ).pole_unit
  · intro γ hγ
    have eqn:=(x.F.mark γ hγ).identity
    have orig:M.factor*M.wK γ*x.F.scalar γ+C (M.label γ)*M.Q =
        M.E*M.decoder (x.F.mark γ hγ).bad:= by
      rw [← eqn]
      ring
    have mapped:=congrArg (Polynomial.map embed) orig
    simp only [zS4,zNl,Polynomial.map_C] at mapped
    rw [← amp]
    exact mapped ▸ hdiv.trans (dvd_mul_right _ _)
theorem onePole (x :Input) :Nonempty (OnePole x) := by
  obtain ⟨P,hH,hh,hz⟩:=poleData x
  obtain ⟨L⟩:=bRd.proof x.Γ x.F.scalar P
  exact ⟨⟨P,L,hH,hh,hz⟩⟩
theorem caps_at {h:ℕ} (b:Bank) {F}
    (hF:F∈Aw b h b.cut) :
    TopCaps h b.m b.box.b b.box.j b.box.t b.U (toTop F) := by
  classical
  obtain ⟨⟨hB,hJ,hC,_⟩,hU,hw⟩:=mem_ambient.mp hF
  intro a ha
  rw [toTop,MvPolynomial.support_rename_of_injective aD.injective] at ha
  obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp ha
  rw [toTop,MvPolynomial.coeff_rename_mapDomain _ aD.injective]
  have hB' := (z6P (fun i:mA=>i.elim 0 (fun _=>1)) he).trans hB
  have hJ' := (z6P (fun i:mA=>i.elim 0 Fin.val) he).trans hJ
  have hC' := (zTo (some 2) he).trans hC
  have hU' := (zTo none he).trans hU
  have hf :=hw e he
  simp only [Finsupp.weight_apply,smul_eq_mul] at hB' hJ'
  have hs (w:Fin 3→ℕ) :
      e.sum (fun i n=>n*i.elim 0 w) =
        w 0*e (some 0)+w 1*e (some 1)+w 2*e (some 2) := by
    rw [← sum_coeffs e w]
    congr 1
    funext i n
    cases i <;> simp [Nat.mul_comm]
  rw [hs] at hB' hJ'
  rw [sum_coeffs] at hf
  let d:=131071+h
  have h1 : (d-1)*e (some 1)+e (some 1)=d*e (some 1) := by
    calc
      _=(d-1)*e (some 1)+1*e (some 1) := by simp
      _ = _:= by rw [← Nat.add_mul,zxt (by dsimp [d]; omega)]
  have h2 : (d-2)*e (some 2)+2*e (some 2)=d*e (some 2) := by
    rw [← Nat.add_mul,zxt (by dsimp [d]; omega)]
  change (F.coeff e).natDegree+(d*e (some 0)+(d-1)*e (some 1) +
    (d-2)*e (some 2))≤b.cut+(b.box.b+b.box.j)*h at hf
  have he0: (z8D aD e) 0=e none := by
    simpa only [aD,finSuccEquiv_symm_none] using
      Finsupp.mapDomain_apply_of_injective aD.injective e none
  have he1 : (z8D aD e) 1=e (some 0) := by
    simpa only [aD,finSuccEquiv_symm_some,(by decide : ((0:Fin 3).succ)=1)] using
      Finsupp.mapDomain_apply_of_injective aD.injective e (some 0)
  have he2 : (z8D aD e) 2=e (some 1) := by
    simpa only [aD,finSuccEquiv_symm_some,(by decide : ((1 :Fin 3).succ)=2)] using
      Finsupp.mapDomain_apply_of_injective aD.injective e (some 1)
  have he3: (z8D aD e) 3=e (some 2) := by
    simpa only [aD,finSuccEquiv_symm_some,(by decide : ((2 :Fin 3).succ)=3)] using
      Finsupp.mapDomain_apply_of_injective aD.injective e (some 2)
  rw [he0,he1,he2,he3]
  refine ⟨by simpa using hB',by simpa using hJ',hC',hU',?_⟩
  change (F.coeff e).natDegree+d*(e (some 0)+e (some 1)+e (some 2)) ≤
    b.cut+(b.box.b+b.box.j)*h+e (some 1)+2*e (some 2)
  simp only [Nat.mul_add]
  omega
theorem source_zero {x :Input} (P:OnePole x) (b:Bank) {F}
    (hF:F∈aV P b b.cut) {γ:K} (hγ:γ∈x.Γ) :
    atTop (toTop F) (x.M.label γ) (x.F.scalar γ)=0:= by
  let L:=P.bY
  let H :=P.data.H
  let z :=P.data.z γ
  let res :=Tj L.numerator L.denominator z
  let r :=b.box.b+b.box.j
  obtain ⟨hA,hC,hP⟩:=Submodule.mem_inf.mp hF
  have hcut:=(mem_ambient.mp hA).2.2
  rw [← P.height] at hcut
  obtain ⟨Q,hQ⟩:=gt6 P.data L r F z (L.regular γ hγ)
    ((NR.aVU _ _ _ _ _).mp hP)
  have hres :res.natDegree≤H.natDegree :=
    (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans L.small.le)
  have hr :=cfm z hres hcut
  rw [hQ] at hr
  have hQcut:a04 b.cut Q:= by
    intro a ha
    have hn:=MvPolynomial.mem_support_iff.mp ha
    have hp:=pow_ne_zero r P.data.monic.ne_zero
    have hc: (znf (H^r)*Q).coeff a≠0:= by
      rw [z06]
      exact mul_ne_zero hp hn
    have hb:=MvPolynomial.mem_restrictJointDegree.mp hr a hc
    rw [z06,natDegree_mul hp hn,natDegree_pow] at hb
    simp only [weight_eq_sum,aWN] at hb
    change r*H.natDegree+_+_≤b.cut+r*H.natDegree at hb
    omega
  obtain ⟨T,hT,hST⟩:=L.quotient γ hγ
  have hcontact :=c6X b.m x.M.word H res z r F Q P.data.nodes
    (fun i=>(bsz _ _ _ _).mp ((zxR _).mp hC i)) hQ
  let B:=x.F.mark γ hγ
  have hz :cK Q T=0:= by
    apply wT.aHG B.bad.support (fun i=>embed (P6.node i))
      ((RingHom.injective embed).comp IRSProfile.domain.injective) b.m
    · intro i hi
      apply hcontact i T
      rw [← hST,extend,Polynomial.eval_map,Polynomial.eval₂_at_apply,B.scalar_hits i hi]
    · have hA:b.m*P5_7.midAgreement≤b.m*B.bad.support.card :=
        zBI _ ((by decide :P5_7.midAgreement≤P6.dw).trans B.bad.dw)
      have hpos :0<b.m*P5_7.midAgreement :=
        Nat.mul_pos (by cases b <;> decide) (by decide)
      have hdeg:=raw_eval_degree hT hQcut
      unfold Bank.cut at hdeg
      omega
  have h:=congrArg (fun R:af 3=>cK R T) hQ
  change cK (az5 H res (JX (C z) F)) T= _ at h
  rw [d2J,← hST] at h
  have h0:cK (znf (H^r)*Q) T=0:= by
    change MvPolynomial.eval (jet T) (_ *_)= _
    rw [map_mul,MvPolynomial.eval_C]
    change H^r*cK Q T=0
    rw [hz,mul_zero]
  rw [h0] at h
  rw [duQ,eval_rename_top,← P.Kw γ,h,map_zero]
end
end q0Nj7Rb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q0Nj7Rb
noncomputable section
open P6_7_3 (Input)
open qlc9qed (Bank Aw ays mem_ambient toTop toTop_injective choose_strong
  b4I topCommon cHJ)
open qzLARrc (oneDebit)
open aR (ao embed)
open jA
open NR (TT)
open acZ (agr)
open private bXt bCP cKM from ProximityPrize.SubmissionLower.DG
open private exists_row degree_dvd from ProximityPrize.SubmissionLower.Z7znM4a
open private separable_bound from ProximityPrize.SubmissionLower.ZrgYIVd
open private bDY from ProximityPrize.SubmissionLower.E2
def c1 :Prop :=qPQ4nYa.c1
def c2 :Prop :=qPQ4nYa.c2
def c3:Prop :=qPQ4nYa.c3
def c4 :Prop :=qzLARrc.c1
def c5:Prop :=qzLARrc.c2
def c6:Prop :=qzLARrc.c3
def c7:Prop :=qzLARrc.c4
private theorem c4y (h4 :c4) (h5:c5) (h6:c6) (h7:c7)
    {x :Input} (P:OnePole x) (b:Bank) (V:Submodule ao jK)
    [hV:zAa ao V] (hcap : ∀ F∈V,Jn b.box F∧gY F≤b.U) :
    TT V (pole P b)≤b.eMG x.h:= by
  have h:=bDY _ _ P.data P.bY b.box V (P.data.H.natDegree*oneDebit b) hV
    (fun P' L' _ hdeg hsep=>hdeg ▸ separable_bound h4 h5 h6 h7 b P' L' V hcap hsep)
  rw [P.height] at h
  exact h
private theorem debit_ok (b:Bank) (h:ℕ) (hh:h≤2534) :
    rank b+262144*((b.U+1)*b.contactRank)+b.eMG h≤b.ambientCount h:= by
  cases b <;> simp only [rank,Bank.rank,Bank.U,Bank.contactRank,Bank.eMG,
    Bank.ambientCount,Bank.az0,Bank.basePole,Bank.poleExcess,Nat.mul_add] <;> omega
private theorem rank_lower (hc:qlc9qed.c2) (hp :
    ∀ (x :Input) (P:OnePole x) (b:Bank) (V:Submodule ao jK),
      zAa ao V→(∀ F∈V,Jn b.box F∧gY F≤b.U) →
      TT V (pole P b)≤b.eMG x.h)
    {x :Input} (P:OnePole x) (b:Bank) :
    rank b≤zsE ao (aV P b b.cut) := by
  classical
  let V:=Aw b x.h b.cut
  obtain ⟨hV,hcol⟩:=ds9 b x.h
  let:zAa ao V:=hV
  have hcaps (F:jK) (hF:F∈V) :Jn b.box F∧gY F≤b.U :=
    ⟨(mem_ambient.mp hF).1,(mem_ambient.mp hF).2.1⟩
  let A (i:P6.I) :=ays b.m (embed (P6.node i)) (x.word i)
  have hcontacts :=bCP V (Finset.univ :Finset P6.I) A ((b.U+1)*b.contactRank)
    (fun _ _=>hc b _ _ V hV hcaps)
  have hcard: (Finset.univ :Finset P6.I).card = 262144 :=Fintype.card_fin (2^18)
  rw [Finset.inf_univ_eq_iInf,hcard] at hcontacts
  have hd:TT V (contacts x b ⊓ pole P b) ≤
      262144*((b.U+1)*b.contactRank)+b.eMG x.h :=
    (bXt V _ _).trans (Nat.add_le_add hcontacts (hp x P b V hV hcaps))
  exact cKM ((debit_ok b x.h (P6_7_3.emz x).2).trans hcol) hd
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) (h7:c7) :
    P6_7_3.c3:= by
  intro x
  obtain ⟨P⟩:=onePole x
  have bound:=rank_lower (qPQ4nYa.of_children h1 h2 h3)
    (fun _ P b V hV hc => @c4y h4 h5 h6 h7 _ P b V hV hc) (x :=x)
  have hcheap:=bound P .cheap
  have hstrong:=bound P .strong
  obtain ⟨F,hF,hnF⟩:=exists_row _ ((by decide :0< rank .cheap).trans_le hcheap)
  have hU:=(mem_ambient.mp (Submodule.mem_inf.mp hF).1).2.1
  obtain ⟨W,hW,hnW,havoid⟩:=choose_strong F hnF _
    (exists_row _ ((by decide :0< rank .strong).trans_le hstrong)) (by
      intro G hi hd ht hs
      by_contra! hall
      have hseed :=degree_dvd none (agr hnF) hd
      change gY G≤gY (bC F) at hseed
      rw [b4I] at hseed
      have hsmall:G.degreeOf none<P6.p:=hseed.trans_lt (hU.trans_lt (by decide))
      exact (not_le_of_gt (by decide :aMH< rank .strong))
        (hstrong.trans (ceiling_bound P ht (factor_power P hi hs hsmall hall))))
  refine ⟨⟨toTop F,toTop W,toTop_injective.ne hnF,toTop_injective.ne hnW,
    caps_at .cheap (Submodule.mem_inf.mp hF).1,caps_at .strong (Submodule.mem_inf.mp hW).1,
    topCommon havoid,?_⟩⟩
  intro γ hγ
  have hf :=source_zero P .cheap hF hγ
  have hw:=source_zero P .strong hW hγ
  have hs :=(x.F.mark γ hγ).scalar_fixed
  exact ⟨hf,hw,cHJ _ _ _ hs hf,cHJ _ _ _ hs hw⟩
end
end q0Nj7Rb
end
