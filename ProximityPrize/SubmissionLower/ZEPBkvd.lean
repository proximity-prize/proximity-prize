import ProximityPrize.SubmissionLower.ZjZXRjd
import ProximityPrize.SubmissionLower.ZKfhfIb
import ProximityPrize.SubmissionLower.ZbnhR9d
import ProximityPrize.SubmissionLower.P5_7_1_3_2Local
set_option Elab.async false
open private c6G aei aJZ multiples mem_multiples d2J AV Bg Ky aob normalize from ProximityPrize.SubmissionLower.S
open private boundary bVx cU3 power_le_top coordinate from ProximityPrize.SubmissionLower.ZjZXRjd
open private eval_rename_top raw_eval_degree exists_row degree_dvd from ProximityPrize.SubmissionLower.Z7znM4a
open _root_ renaming Fin.sum_univ_succ → zCS, Finset.Ico → zUb, Finset.card_range → ztd, Finset.exists_mem_eq_sup → zOU, Finset.mul_sum → zxw, Finset.range → z4x, Finset.sum_le_sum → zQk, Finsupp.sum_fintype → z9d, Finsupp.weight_apply → zDM, Fintype.sum_option → zy6, LinearIndependent → z14, LinearMap.finrank_range_add_finrank_ker → z7i, LinearMap.mulLeft → zzN, Module.Finite → zAa, Module.Finite.of_injective → zfv, Module.finrank → zsE, MvPolynomial.X_ne_zero → zch, MvPolynomial.coeff_C_mul → z06, MvPolynomial.degreeOf_eq_sup → zXi, MvPolynomial.le_degreeOf_of_mem_support → zTo, MvPolynomial.le_weightedTotalDegree → z6P, Nat.add_le_add_right → zlr, Nat.lt_succ_of_le → zB1, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.mul_pos → zah, Polynomial.map_add → zS4, Polynomial.map_mul → zNl, Set.range → zxp, Submodule.map_span → zYZ, Submodule.span → zLD
section
set_option autoImplicit true
namespace q84jfie
noncomputable section
open jA MvPolynomial
open qlc9qed (Bank)
open private value_choices from ProximityPrize.SubmissionLower.ZFO2WXb
open scoped BigOperators
private abbrev Exponent:=mA →₀ ℕ
private def tuples (a U:ℕ) :Finset (ℕ×ℕ×ℕ×ℕ) :=
  (zUb a 20).biUnion fun c =>
    (z4x (51 - 2*c)).biUnion fun j =>
      (z4x (165 - c - j)).biUnion fun i =>
        (z4x U).image fun z=>(c,j,i,z)
private def rU (a U:ℕ) :Finset Exponent:=(tuples a U).image aei
def slots (a U:ℕ) :ℕ:=U * ∑ c∈zUb a 20,(51 - 2*c)*140
private theorem b2w {R:Type*} [CommSemiring R] {a U:ℕ} {F:VP R}
    (hc:Jn Bank.strong.box F) (hz :gY F<U)
    {m:Exponent} (hm:m∈F.support) (ha :a≤ m (some 2)) :m∈rU a U:= by
  classical
  have htotal:=(z6P
    (fun i:mA=>i.elim 0 (fun _=>1)) hm).trans hc.1
  have hindex :=(z6P
    (fun i:mA=>i.elim 0 Fin.val) hm).trans hc.2.1
  have hseed :=(zTo (none :mA) hm).trans_lt hz
  have htop:=(zTo (some 2 :mA) hm).trans hc.2.2.1
  have hB:m (some 0)+m (some 1)+m (some 2)≤164 := by
    simpa [zDM,z9d,zy6,
      zCS,Bank.box,Nat.add_assoc] using htotal
  have hJ:m (some 1)+2*m (some 2)≤50:= by
    simpa [zDM,z9d,zy6,
      zCS,Bank.box,Nat.mul_comm] using hindex
  change m (some 2)≤19 at htop
  change m none<U at hseed
  refine Finset.mem_image.mpr ⟨(m (some 2),m (some 1),m (some 0),m none),?_,?_⟩
  · simp only [tuples,Finset.mem_biUnion,Finset.mem_Ico,Finset.mem_range,Finset.mem_image]
    exact ⟨m (some 2),⟨ha,by omega⟩,m (some 1),by omega,m (some 0),by omega,
      m none,by omega,rfl⟩
  · ext i
    cases i with
    | none=>simp [aei]
    | some i=>fin_cases i <;> simp [aei]
private theorem card_exponents (a U:ℕ) : (rU a U).card≤ slots a U :=
  Finset.card_image_le.trans (by
    unfold tuples
    calc
      _ ≤ ∑ c∈zUb a 20,∑ j∈z4x (51 - 2*c),
          ∑ _∈z4x (165 - c - j),U:= by
        refine Finset.card_biUnion_le.trans (zQk fun c _ => ?_)
        refine Finset.card_biUnion_le.trans (zQk fun j _ => ?_)
        refine Finset.card_biUnion_le.trans (zQk fun i _ => ?_)
        exact Finset.card_image_le.trans_eq (ztd _)
      _=slots a U:= by
        rw [slots,zxw]
        simp only [Finset.sum_const,ztd,Nat.nsmul_eq_mul]
        apply Finset.sum_congr rfl
        intro c hc
        rw [← Finset.sum_mul,value_choices (by have :=(Finset.mem_Ico.mp hc).2; omega),
          Nat.mul_comm])
theorem bwH {a U:ℕ} (ha :20≤a) :slots a U=0:= by
  rw [slots,Finset.Ico_eq_empty_of_le ha,Finset.sum_empty,Nat.mul_zero]
theorem slots_sum (U:ℕ) : (∑ k∈z4x 19,slots (1+k) U)=U*665000:= by
  have hp:=q6AUWfb.slots_sum
  simp only [q6AUWfb.slots,← zxw] at hp
  have he :=Nat.eq_of_mul_eq_mul_left (by decide :0<3038) hp
  simp only [slots,← zxw,he]
private abbrev topX:ko:=MvPolynomial.X (some 2)
private theorem moved_caps {G Q:ko} (hg:G≠0) (hq:Q≠0)
    (hT:0<G.degreeOf (some 2)) (hZ:0<G.degreeOf none) {a U:ℕ} (ha :0<a)
    (hc:Jn Bank.strong.box (G^a*Q)) (hs :gY (G^a*Q)≤U) :
    Jn Bank.strong.box (topX^a*Q)∧gY (topX^a*Q)<U ∧
      a≤(topX^a*Q).degreeOf (some 2) := by
  have hx :topX≠0:=zch _
  have hxdeg (v :mA→ℕ) :topX.weightedTotalDegree v=v (some 2) := by
    change (MvPolynomial.monomial (Finsupp.single (some 2 :mA) 1) (1 :iP)).weightedTotalDegree v= _
    rw [weightedTotalDegree_monomial _ _ _ one_ne_zero,Finsupp.weight_single]
    simp
  have hweight (v :mA→ℕ) :
      (topX^a*Q).weightedTotalDegree v≤(G^a*Q).weightedTotalDegree v := by
    have hG:v (some 2)≤G.weightedTotalDegree v := by
      obtain ⟨m,hm,he⟩:=zOU G.support
        (MvPolynomial.support_nonempty.mpr hg) (fun e=>e (some 2))
      rw [zXi,he] at hT
      exact (Nat.le_mul_of_pos_left _ hT).trans
        ((Finsupp.apply_smul_le_weight v m (some 2)).trans (le_weightedTotalDegree v hm))
    rw [weightedTotalDegree_mul v _ _ (pow_ne_zero _ hx) hq,
      weightedTotalDegree_mul v _ _ (pow_ne_zero _ hg) hq,
      aJZ v _ hx,aJZ v _ hg,hxdeg]
    exact zlr (zBI _ hG) _
  have ht: (topX^a*Q).degreeOf (some 2)=a+Q.degreeOf (some 2) := by
    rw [degreeOf_mul_eq (pow_ne_zero _ hx) hq]
    simp
  have hgT:a≤a*G.degreeOf (some 2) :=Nat.le_mul_of_pos_right _ hT
  have hgZ:0<a*G.degreeOf none :=zah ha hZ
  have hlim:=hc.2.2.1
  rw [degreeOf_mul_eq (pow_ne_zero _ hg) hq,degreeOf_pow_eq _ _ _ hg] at hlim
  unfold gY at hs ⊢
  rw [degreeOf_mul_eq (pow_ne_zero _ hg) hq,degreeOf_pow_eq _ _ _ hg] at hs
  have hz : (topX^a*Q).degreeOf none= Q.degreeOf none := by
    rw [degreeOf_mul_eq (pow_ne_zero _ hx) hq,degreeOf_pow_eq _ _ _ hx,
      degreeOf_X_of_ne (by decide : (none :mA)≠some 2),Nat.mul_zero,Nat.zero_add]
  have hz' : (topX^a*Q).degreeOf none≤(G^a*Q).degreeOf none := by
    rw [hz,degreeOf_mul_eq (pow_ne_zero _ hg) hq]
    exact Nat.le_add_left _ _
  exact ⟨⟨(hweight _).trans hc.1,(hweight _).trans hc.2.1,by omega,hz'.trans hc.2.2.2⟩,
    by omega,by omega⟩
theorem count_moving_symbols (a U r :ℕ) (ha :0<a) (e :Fin r→ko)
    (he :z14 iP e) {G:ko}
    (hT:0<G.degreeOf (some 2)) (hZ:0<G.degreeOf none)
    (h : ∀ F∈zLD iP (zxp e),
      Jn Bank.strong.box F∧gY F≤U∧G^a∣F) :
    r≤ slots a U:= by
  classical
  have hg:G≠0:= by rintro rfl; simp at hT
  choose q hq using fun i=>(h (e i) (Submodule.subset_span (Set.mem_range_self i))).2.2
  let f :=zzN iP (G^a)
  let g:=zzN iP (topX^a)
  have hf :f ∘ q=e :=funext fun i=>(hq i).symm
  have hli:=LinearIndependent.of_comp f (hf ▸ he :z14 iP (f ∘ q))
  have hgi:Function.Injective g:= fun x y hxy =>
    mul_left_cancel₀ (pow_ne_zero _ (zch _)) hxy
  have hgspan: (zLD iP (zxp q)).map g =
      zLD iP (zxp (g ∘ q)) := by rw [zYZ,Set.range_comp]
  have hfspan: (zLD iP (zxp q)).map f =
      zLD iP (zxp e) := by rw [zYZ,← Set.range_comp,hf]
  refine (c6G (rU a U) (g ∘ q)
    (hli.map' g (LinearMap.ker_eq_bot.mpr hgi)) ?_).trans (card_exponents a U)
  intro R hR hn
  rw [← hgspan] at hR
  obtain ⟨Q,hQ,rfl⟩:=hR
  have hQne :Q≠0:= fun hz=>hn (by rw [hz,map_zero])
  have hmem:f Q∈zLD iP (zxp e) :=hfspan ▸ Submodule.mem_map_of_mem hQ
  obtain ⟨hc,hs,hdeg⟩:=moved_caps hg hQne hT hZ ha (h (f Q) hmem).1 (h (f Q) hmem).2.1
  obtain ⟨m,hm,heq⟩:=zOU (g Q).support
    (MvPolynomial.support_nonempty.mpr hn) (fun u=>u (some 2))
  change a≤(g Q).degreeOf (some 2) at hdeg
  rw [zXi,heq] at hdeg
  exact ⟨m,b2w hc hs hm hdeg,MvPolynomial.mem_support_iff.mp hm⟩
end
end q84jfie
end
section
set_option autoImplicit true
namespace q84jfie
noncomputable section
open Polynomial
open P6 (I K)
open aR (ao jF)
open jA
open acZ (OV bI3 a88 agr bZx)
open axa (weight)
open qlc9qed (Bank b4I)
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
section
variable {Γ:Finset K} {s :K→K[X]} (w:I→K) (P:jF Γ s) (L:kH P) (U:ℕ)
private abbrev source (t:ℕ) :=aV w P L .strong U t
private abbrev total (h t:ℕ) :=t+(Bank.strong.box.b+Bank.strong.box.j)*h
private abbrev full:=Aw .strong P.H.natDegree U (cut .strong)
private theorem finiteSource (hfin:zAa ao (full P U)) {t:ℕ} (ht:t≤ cut .strong) :
    zAa ao (source w P L U t) := by
  let:zAa ao (full P U) :=hfin
  let:IsNoetherian ao (full P U) :=isNoetherian_of_isNoetherianRing_of_finite ao (full P U)
  have hle :source w P L U t≤full P U:= by
    intro F hF
    obtain ⟨hc,hs,ht'⟩:=mem_ambient.mp (Submodule.mem_inf.mp hF).1
    exact mem_ambient.mpr ⟨hc,hs,fun a ha=>(ht' a ha).trans (zlr ht _)⟩
  exact zfv (R:=ao) (N :=full P U)
    (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
private theorem bank_bounds {t F} (hF:F∈source w P L U t) :
    Jn Bank.strong.box F∧gY F≤U∧ahb P.H.natDegree (total P.H.natDegree t) F :=
  mem_ambient.mp (Submodule.mem_inf.mp hF).1
private def aff (t:ℕ) :source w P L U t →ₗ[ao] ((mA →₀ ℕ)→ao) :=
  (boundary P.H.natDegree (total P.H.natDegree t)).comp (source w P L U t).subtype
private theorem brp (t:ℕ) [zAa ao (source w P L U t)] :
    zsE ao (aff w P L U (t+1)).ker≤zsE ao (source w P L U t) := by
  let f :=(source w P L U (t+1)).subtype.comp (aff w P L U (t+1)).ker.subtype
  have hm (F: (aff w P L U (t+1)).ker) :f F∈source w P L U t:= by
    obtain ⟨hc,hs,hw⟩:=bank_bounds w P L U F.val.property
    have hz :boundary P.H.natDegree (total P.H.natDegree (t+1)) F.val.val=0 :=
      LinearMap.mem_ker.mp F.property
    refine ⟨mem_ambient.mpr ⟨hc,hs,fun m hmem => ?_⟩,F.val.property.2⟩
    have hh:=bVx hw hz hmem
    change (F.val.val.coeff m).natDegree+weight P.H.natDegree m≤total P.H.natDegree t
    dsimp only [total] at hh ⊢
    omega
  apply LinearMap.finrank_le_finrank_of_injective (f :=f.codRestrict _ hm)
  intro F G he
  exact Subtype.ext (Subtype.ext (congrArg (fun Q:source w P L U t=>Q.val) he))
private theorem telescope (hfin:zAa ao (full P U)) (h0:source w P L U 0 = ⊥)
    (t:ℕ) (ht:t≤ cut .strong) :zsE ao (source w P L U t) ≤
      ∑ v∈z4x (t+1),zsE ao (aff w P L U v).range := by
  induction t with
  | zero =>
    rw [h0,finrank_bot]
    exact Nat.zero_le _
  | succ t ih =>
    let:zAa ao (source w P L U _) :=finiteSource w P L U hfin ht
    have hlt:=(Nat.le_succ t).trans ht
    let:zAa ao (source w P L U t) :=finiteSource w P L U hfin hlt
    have h:=z7i (K:=ao)
      (V:=source w P L U (t+1)) (V₂:=(mA →₀ ℕ)→ao) (aff w P L U (t+1))
    rw [Finset.sum_range_succ,← h,add_comm]
    exact Nat.add_le_add ((brp w P L U t).trans (ih hlt)) le_rfl
private theorem layer_bound (t a :ℕ) [zAa ao (source w P L U t)] (ha :0<a)
    {G:ko} (hT:0<G.degreeOf (some 2)) (hZ:0<G.degreeOf none)
    (hdvd : ∀ F∈source w P L U t,G^a∣bC F) :
    zsE ao (aff w P L U t).range≤ slots a U:= by
  classical
  let b:=Module.finBasis ao (aff w P L U t).range
  choose e he using fun i=>LinearMap.mem_range.mp (b i).property
  have hi:z14 ao (fun i=>(b i).val) :=
    b.linearIndependent.map' (aff w P L U t).range.subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have heq : (fun i=>boundary P.H.natDegree (total P.H.natDegree t) (e i).val) =
      fun i=>(b i).val :=funext he
  let seedBox :Submodule iP ko:=MvPolynomial.restrictWeightedDegree (R:=iP) (Pi.single (none :mA) 1) U
  have hZmem (R:ko) :R∈seedBox↔gY R≤U:= by
    dsimp only [seedBox]
    rw [MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
      MvPolynomial.weightedTotalDegree_piSingle,gY]
  let V:=OV Bank.strong.box ⊓ seedBox ⊓ multiples (G^a)
  have hspan:zLD iP (zxp fun i=>bC (e i).val)≤V:= by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    obtain ⟨hc,hs,_⟩:=bank_bounds w P L U (e i).property
    exact ⟨⟨bI3.mpr (a88 hc),(hZmem _).mpr (b4I.trans_le hs)⟩,
      mem_multiples.mpr (hdvd _ (e i).property)⟩
  refine count_moving_symbols a U _ ha _ (cU3 (fun i=>(e i).val)
    (fun i=>(bank_bounds w P L U (e i).property).2.2) (heq ▸ hi)) hT hZ ?_
  intro R hR
  have hm:R∈V:=hspan hR
  exact ⟨bI3.mp hm.1.1,(hZmem _).mp hm.1.2,mem_multiples.mp hm.2⟩
theorem moving_ceiling (hfin:zAa ao (full P U)) {G:ko}
    (hT:0<G.degreeOf (some 2)) (hZ:0<G.degreeOf none)
    (hdvd : ∀ t≤ cut .strong,∀ F∈source w P L U t,G^powerAt P.H.natDegree t∣bC F) :
    zsE ao (source w P L U (cut .strong))≤aMH .strong P.H.natDegree U:= by
  let h:=P.H.natDegree
  have hh:=P.small.2
  have he :0<3*h:=zah (by decide) P.small.1
  have h0:source w P L U 0 = ⊥ := by
    apply (source w P L U 0).eq_bot_iff.mpr
    intro F hF
    by_contra hn
    have hs :=(a88 (bank_bounds w P L U hF).1).2.2.1
    change (bC F).degreeOf (some 2)≤19 at hs
    have hd:=power_le_top hT (agr hn) (hdvd 0 (Nat.zero_le _) F hF)
    have hb:19≤ cut .strong/(3*h) := by
      apply (Nat.le_div_iff_mul_le he).mpr
      change 19*(3*P.H.natDegree)≤21579239
      omega
    simp only [powerAt,Nat.sub_zero] at hd
    change 1+cut .strong/(3*h)≤_ at hd
    omega
  calc
    _ ≤ ∑ t∈z4x (cut .strong+1),zsE ao (aff w P L U t).range :=
      telescope w P L U hfin h0 _ le_rfl
    _≤(3*h) * ∑ k∈z4x 19,slots (1+k) U :=
      bZx he _ (fun k=>slots (1+k) U)
        (fun t ht=> by
          let:zAa ao (source w P L U _) :=finiteSource w P L U hfin ht
          exact layer_bound w P L U t (powerAt h t) (Nat.zero_lt_one.trans_le (Nat.le_add_right _ _)) hT hZ (hdvd t ht))
        (fun k hk=>bwH (by omega))
    _=aMH .strong h U:= by simp only [slots_sum,aMH,Nat.mul_assoc]
end
end
end q84jfie
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qacgeGb
noncomputable section
open Polynomial
open aR (ao)
open jA
open P6_7_1 (Input)
open qFAh60c (OnePole aV)
private theorem finite_ambient (h t:ℕ) :
    zAa ao (q84jfie.Aw .strong h 490 t) := by
  classical
  let V:=q84jfie.Aw .strong h 490 t
  let T:=t+(qlc9qed.Bank.strong.box.b+qlc9qed.Bank.strong.box.j)*h
  let E :=mA→Fin 491
  let A:=E×Fin (T+1)
  let f :V →ₗ[ao] (A→ao) :=LinearMap.pi fun u =>
    (coordinate (Finsupp.equivFunOnFinite.symm (fun i=>(u.1 i).val)) u.2.val).comp V.subtype
  have hzero (F:V) (hz :f F=0) :F=0:= by
    obtain ⟨hc,hs,hw⟩:=q84jfie.mem_ambient.mp F.property
    apply Subtype.ext
    apply MvPolynomial.ext
    intro m
    change F.val.coeff m=0
    by_contra hn
    have hm:=MvPolynomial.mem_support_iff.mpr hn
    have hd: (F.val.coeff m).natDegree≤T:=(Nat.le_add_right ..).trans (hw m hm)
    have he (i:mA) :m i<491 := by
      cases i with
      | none =>
        exact zB1 ((zTo none hm).trans hs)
      | some i =>
        have hdeg:F.val.degreeOf (some i)≤vC F.val :=
          MvPolynomial.degreeOf_le_weightedTotalDegree
            (fun j:mA=>j.elim 0 (fun _=>1)) (some i) Nat.one_pos F.val
        exact ((zTo (some i) hm).trans
          (hdeg.trans hc.1)).trans_lt (by decide)
    let u:E := fun i=>⟨m i,he i⟩
    let k :Fin (T+1) :=⟨_,zB1 hd⟩
    have hk :=congrArg (fun v :A→ao=>v (u,k)) hz
    change (F.val.coeff (Finsupp.equivFunOnFinite.symm (fun i=>(u i).val))).coeff
      (F.val.coeff m).natDegree=0 at hk
    rw [show Finsupp.equivFunOnFinite.symm (fun i=>(u i).val)=m from
      Finsupp.equivFunOnFinite.symm_apply_apply m] at hk
    exact (leadingCoeff_ne_zero.mpr hn) hk
  apply zfv f
  intro F G he
  exact sub_eq_zero.mp (hzero (F-G) ((f.map_sub F G).trans (sub_eq_zero.mpr he)))
private theorem bank_eq {x :Input} (P:OnePole x) (t:ℕ) :
    aV P .strong t=q84jfie.aV x.M.word P.data P.bY .strong 490 t:= by
  have ha :qFAh60c.Aw .strong x.h t =
      q84jfie.Aw .strong P.data.H.natDegree 490 t:= by
    ext F
    rw [qFAh60c.mem_ambient,q84jfie.mem_ambient,P.height]
    rfl
  unfold aV q84jfie.aV
  rw [ha]
  rfl
theorem proof :qFAh60c.c4 := by
  intro x P G hT hZ hdiv
  rw [bank_eq]
  have h:=q84jfie.moving_ceiling x.M.word P.data P.bY 490
    (finite_ambient _ _) hT hZ (by
      intro t ht F hF
      rw [P.height]
      exact hdiv t ht F ((bank_eq P t).symm ▸ hF))
  refine h.trans ?_
  change 3*P.data.H.natDegree*490*665000≤qFAh60c.topCeiling
  rw [P.height]
  exact (ztf 665000 (ztf 490
    (zBI 3 (qFAh60c.emz x).2))).trans (by decide)
end
end qacgeGb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace q84jfie
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open P6 (K dw)
open P6_7 (RectTail)
open P6_7_2 (Input Bs)
open P5_7_1 (atTop)
open qlc9qed (Bank toTop bsz duQ)
open aR (af jF embed extend cK jet)
open jA Rk
open private gt6 cfm weight_eq_sum aWN from ProximityPrize.SubmissionLower.C
theorem heights {r :RectTail} (x :Input r) :r.kA.lo≤x.h∧x.h≤(Bs r).hi:= by
  have hb:r.kA.hi≤(Bs r).hi:= by cases r <;> decide
  obtain ⟨h₁,h₂⟩:=x.kA
  change (r.kA.lo:ℤ)≤x.M.iF at h₁
  change x.M.iF≤(r.kA.hi:ℤ) at h₂
  change r.kA.lo≤x.M.iF.toNat∧x.M.iF.toNat≤(Bs r).hi
  omega
private theorem height_guards (r :RectTail) :1≤ r.kA.lo∧(Bs r).hi≤2600:= by
  cases r <;> decide
private theorem poleData {r :RectTail} (x :Input r) :
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
    have ⟨h₁,h₂⟩:=heights x
    exact ⟨(height_guards r).1.trans h₁,h₂.trans (height_guards r).2⟩
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
        M.E*M.decoder (x.F.mark γ hγ).bad:= by rw [← eqn]; ring
    have mapped:=congrArg (Polynomial.map embed) orig
    simp only [zS4,zNl,Polynomial.map_C] at mapped
    rw [← amp]
    exact mapped ▸ hdiv.trans (dvd_mul_right _ _)
theorem onePole {r :RectTail} (x :Input r) :Nonempty (OnePole x) := by
  obtain ⟨P,hH,hh,hz⟩:=poleData x
  obtain ⟨L⟩:=bRd.proof x.Γ x.F.scalar P
  exact ⟨⟨P,L,hH,hh,hz⟩⟩
theorem source_zero {r :RectTail} {x :Input r} (P:OnePole x) (b:Bank) {U F}
    (hF:F∈aV x.M.word P.data P.bY b U (cut b)) {γ:K} (hγ:γ∈x.Γ) :
    atTop (toTop F) (x.M.label γ) (x.F.scalar γ)=0:= by
  let L:=P.bY
  let H :=P.data.H
  let z :=P.data.z γ
  let res :=Tj L.numerator L.denominator z
  let r :=b.box.b+b.box.j
  obtain ⟨hA,hC,hP⟩:=Submodule.mem_inf.mp hF
  have hcut:=(mem_ambient.mp hA).2.2
  obtain ⟨Q,hQ⟩:=gt6 P.data L r F z (L.regular γ hγ)
    ((NR.aVU _ _ _ _ _).mp hP)
  have hres :res.natDegree≤H.natDegree :=
    (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans L.small.le)
  have hr :=cfm z hres hcut
  rw [hQ] at hr
  have hQcut:a04 (cut b) Q:= by
    intro a ha
    have hn:=MvPolynomial.mem_support_iff.mp ha
    have hp:=pow_ne_zero r P.data.monic.ne_zero
    have hc: (MvPolynomial.C (H^r)*Q).coeff a≠0:= by
      rw [z06]
      exact mul_ne_zero hp hn
    have hb:=MvPolynomial.mem_restrictJointDegree.mp hr a hc
    rw [z06,natDegree_mul hp hn,natDegree_pow] at hb
    simp only [weight_eq_sum,aWN] at hb
    change r*H.natDegree+_+_≤(cut b)+r*H.natDegree at hb
    omega
  obtain ⟨T,hT,hST⟩:=L.quotient γ hγ
  have hcontact :=c6X b.m x.M.word H res z r F Q P.data.nodes
    (fun i=>(bsz _ _ _ _).mp ((Submodule.mem_iInf _).mp hC i)) hQ
  let B:=x.F.mark γ hγ
  have hz :cK Q T=0:= by
    apply wT.aHG B.bad.support (fun i=>embed (P6.node i))
      ((RingHom.injective embed).comp IRSProfile.domain.injective) b.m
    · intro i hi
      apply hcontact i T
      rw [← hST,extend,Polynomial.eval_map,Polynomial.eval₂_at_apply,B.scalar_hits i hi]
    · have hA:b.m*dw≤b.m*B.bad.support.card :=
        zBI _ B.bad.dw
      have hpos :0<b.m*dw :=
        zah (by cases b <;> decide) (by decide)
      have hdeg:=raw_eval_degree hT hQcut
      unfold cut at hdeg
      omega
  have h:=congrArg (fun R:af 3=>cK R T) hQ
  change cK (az5 H res (JX (C z) F)) T= _ at h
  rw [d2J,← hST] at h
  have h0:cK (MvPolynomial.C (H^r)*Q) T=0:= by
    change MvPolynomial.eval (jet T) (_ *_)= _
    rw [map_mul,MvPolynomial.eval_C]
    change H^r*cK Q T=0
    rw [hz,mul_zero]
  rw [h0] at h
  rw [duQ,eval_rename_top,← P.Kw γ,h,map_zero]
end
end q84jfie
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q84jfie
noncomputable section
open P6 (I p)
open P6_7 (RectTail)
open P6_7_2 (Input Bs cheapWidth strongWidth)
open aR (ao jF embed)
open jA
open NR (TT)
open acZ (agr)
open qlc9qed (Bank ays toTop toTop_injective topCommon cHJ choose_strong b4I)
open qPQ4nYa (originRange apR origin)
open private bXt bCP cKM from ProximityPrize.SubmissionLower.DG
open private flat_capped normalize_capped contact_of_origin_zero from ProximityPrize.SubmissionLower.P5_7_1_3_2Local
def c1 :Prop :=
  ∀ (r :RectTail) (a :Bank) (h:ℕ),h≤(Bs r).hi →
    zAa ao (Aw a h (width r a) (cut a)) ∧
    ambientCount a h (width r a)≤zsE ao (Aw a h (width r a) (cut a))
def c2 :Prop := ∀ a :Bank,zsE ao (originRange a)≤a.contactRank
def c3:Prop :=
  ∀ (r :RectTail) (a :Bank) {Γ s} (P:jF Γ s) (L:kH P)
    (V:Submodule ao jK),zAa ao V →
    (∀ F∈V,Jn a.box F∧gY F≤width r a) →
    TT V (pole P L a)≤eMG a P.H.natDegree (width r a)
private theorem contactDebit (a :Bank) (U:ℕ) (x v :ao) (V:Submodule ao jK)
    [zAa ao V] (hcap : ∀ F∈V,Jn a.box F∧gY F≤U) :
    TT V (ays a.m x v)≤(U+1)*zsE ao (originRange a) := by
  let A:V →ₗ[ao] (Fin (U+1)→ originRange a) :=LinearMap.pi fun n =>
    ((origin a).domRestrict (apR a)).rangeRestrict ∘ₗ
      (((normalize x v).toLinearMap ∘ₗ aob n ∘ₗ V.subtype).codRestrict _
        (fun F=>normalize_capped (flat_capped (hcap F F.property).1 n) x v))
  have hle :A.ker.map V.subtype≤V ⊓ ays a.m x v := by
    rintro _ ⟨F,hF,rfl⟩
    refine ⟨F.property,contact_of_origin_zero a x v F.val ?_⟩
    intro n
    by_cases hn:n<U+1
    · exact congrArg (fun z :originRange a=>z.val)
        (congrFun (LinearMap.mem_ker.mp hF) ⟨n,hn⟩)
    · have hd: (AV F.val).natDegree≤U:= by
        simpa only [AV,MvPolynomial.natDegree_optionEquivLeft,gY] using
          (hcap F.val F.property).2
      have h₀:Bg n F.val=0:=Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))
      have h₁:aob n F.val=0:= by
        change Ky.symm (Bg n F.val)=0
        rw [h₀,map_zero]
      simp [h₁]
  have hk :=Submodule.finrank_mono hle
  rw [Submodule.finrank_map_subtype_eq] at hk
  have hr :=Submodule.finrank_le A.range
  rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hr
  have hnull:=z7i (K:=ao)
    (V := ↥V) (V₂:=Fin (U+1)→ originRange a) A
  have hc:TT V (ays a.m x v)≤zsE ao A.range := by
    unfold TT
    omega
  exact hc.trans (by simpa only [Nat.cast_id] using hr)
private theorem cfw (r :RectTail) (a :Bank) (h:ℕ) (hh:h≤(Bs r).hi) :
    let U:=width r a
    aMH a h U + 1+262144*((U+1)*a.contactRank)+eMG a h U≤ambientCount a h U:= by
  cases r <;> cases a <;>
    simp only [width,cheapWidth,strongWidth,aMH,Bs,Bank.contactRank,Bank.basePole,
      Bank.poleExcess,eMG,ambientCount,az0,Nat.mul_add] at * <;> omega
private theorem rank_lower (ha :c1) (hc:c2) (hp:c3)
    {r :RectTail} {x :Input r} (P:OnePole x) (a :Bank) :
    aMH a P.data.H.natDegree (width r a)+1 ≤
      zsE ao (aV x.M.word P.data P.bY a (width r a) (cut a)) := by
  let h:=P.data.H.natDegree
  let U:=width r a
  let V:=Aw a h U (cut a)
  have hh:h≤(Bs r).hi:= by
    change P.data.H.natDegree≤_
    rw [P.height]
    exact (heights x).2
  obtain ⟨hV,hcol⟩:=ha r a h hh
  let:zAa ao V:=hV
  have hcaps (F:jK) (hF:F∈V) :Jn a.box F∧gY F≤U :=
    ⟨(mem_ambient.mp hF).1,(mem_ambient.mp hF).2.1⟩
  let A (i:I) :=ays a.m (embed (P6.node i)) (embed (x.M.word i))
  have hn:=bCP V (Finset.univ :Finset I) A ((U+1)*a.contactRank)
    (fun _ _=>(contactDebit a U _ _ V hcaps).trans (zBI _ (hc a)))
  have hcard: (Finset.univ :Finset I).card = 262144 :=Fintype.card_fin (2^18)
  rw [Finset.inf_univ_eq_iInf,hcard] at hn
  have hd:TT V (contacts x.M.word a ⊓ pole P.data P.bY a) ≤
      262144*((U+1)*a.contactRank)+eMG a h U :=
    (bXt V _ _).trans (Nat.add_le_add hn (hp r a P.data P.bY V hV hcaps))
  exact cKM ((cfw r a h hh).trans hcol) hd
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P6_7_2.c2 := by
  intro r x
  obtain ⟨P⟩:=onePole x
  have hcheap:=rank_lower h1 h2 h3 P .cheap
  have hstrong:=rank_lower h1 h2 h3 P .strong
  have hh:P.data.H.natDegree≤(Bs r).hi:= by rw [P.height]; exact (heights x).2
  have hfin:=(h1 r .strong P.data.H.natDegree hh).1
  obtain ⟨F,hF,hnF⟩:=exists_row _ hcheap
  have hU:=(mem_ambient.mp (Submodule.mem_inf.mp hF).1).2.1
  have hpos :0<x.h :=
    (show 0< r.kA.lo by cases r <;> decide).trans_le (heights x).1
  obtain ⟨W,hW,hnW,havoid⟩:=choose_strong F hnF _
    (exists_row _ ((Nat.zero_lt_succ _).trans_le hstrong)) (by
      intro G hi hd ht hs
      by_contra! hall
      have hseed :=degree_dvd none (agr hnF) hd
      change gY G≤gY (bC F) at hseed
      rw [b4I] at hseed
      have hsmall:G.degreeOf none<p :=
        hseed.trans_lt (hU.trans_lt (show width r .cheap<p by cases r <;> decide))
      have hforced:=factor_power P hpos hi hs hsmall hall
      exact (Nat.not_succ_le_self _) (hstrong.trans (moving_ceiling x.M.word P.data P.bY (width r .strong) hfin ht hs hforced)))
  refine ⟨⟨toTop F,toTop W,toTop_injective.ne hnF,toTop_injective.ne hnW,
    topCaps P .cheap hF,topCaps P .strong hW,topCommon havoid,?_⟩⟩
  intro γ hγ
  have hf :=source_zero P .cheap hF hγ
  have hw:=source_zero P .strong hW hγ
  have hs :=(x.F.mark γ hγ).scalar_fixed
  exact ⟨hf,hw,cHJ _ _ _ hs hf,cHJ _ _ _ hs hw⟩
end
end q84jfie
end
