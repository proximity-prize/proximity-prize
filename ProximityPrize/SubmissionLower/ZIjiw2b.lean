import ProximityPrize.SubmissionLower.ZOGAUga
set_option Elab.async false
open _root_ renaming Fin.sum_univ_four → zmL, Fin.sum_univ_succ → zCS, Finset.filter_subset → zT0, Finset.range → z4x, Finset.sum_le_sum → zQk, Finset.sup_le → zf9, Finsupp.sum_fintype → z9d, LinearIndependent → z14, LinearMap.codRestrict → zTB, LinearMap.finrank_range_add_finrank_ker → z7i, LinearMap.ker → z83, LinearMap.mulLeft → zzN, LinearMap.range → zWl, Module.finrank → zsE, MvPolynomial.C → znf, MvPolynomial.coeff_C_mul → z06, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, MvPolynomial.le_degreeOf_of_mem_support → zTo, MvPolynomial.le_totalDegree → zY3, Nat.zero_le → zD0
section
set_option autoImplicit true
namespace qEtASgc
noncomputable section
open Polynomial
open P6 (I K node)
open P6_6 (Pq Contact aRG Dj tB gZ Wk aWx primaryM)
open aR (ao embed af aO shape qE cK)
open aiI (Symbol LY)
open private yZ ajI bpc dgt linearFactor br2 b7U b03 crW from ProximityPrize.SubmissionLower.AB
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent:=Fin 4 →₀ ℕ
private def kO (m:Exponent) :ℕ :=
  m.sum (fun i a=>(gZ - i.val)*a)
private theorem aaG {w:I→K} {T:ℕ} {P:af 4} :
    Pq w T P ↔
      (∀ m∈P.support,m.sum (fun _ a=>a)≤Wk.b ∧
        m.sum (fun i a=>i.val*a)≤Wk.j∧m 3≤Wk.t ∧
        m 1+m 2+m 3≤Dj (m.sum (fun _ a=>a)) ∧
        (P.coeff m).natDegree+kO m≤T)∧Contact w P:= by
  simp only [Pq,aO,shape,qE,MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff,Finset.sup_le_iff,aRG,tB]
  constructor
  · rintro ⟨⟨hb,hj,ht⟩,hp,hT,hc⟩
    exact ⟨fun m hm=>⟨hb m hm,hj m hm,ht m hm,hp m hm,hT m hm⟩,hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨⟨fun m hm=>(h m hm).1,fun m hm=>(h m hm).2.1,fun m hm=>(h m hm).2.2.1⟩,
      fun m hm=>(h m hm).2.2.2.1,fun m hm=>(h m hm).2.2.2.2,hc⟩
private def aV (w:I→K) (T:ℕ) :Submodule ao (af 4) where
  carrier := {P | Pq w T P}
  zero_mem' := by
    apply aaG.mpr
    simp [Contact,cK]
  add_mem' {P Q} hP hQ:= by
    obtain ⟨hP,hp⟩:=aaG.mp hP
    obtain ⟨hQ,hq⟩:=aaG.mp hQ
    apply aaG.mpr
    constructor
    · intro m hm
      have hor :=Finset.mem_union.mp (MvPolynomial.support_add hm)
      have Ca :
          m.sum (fun _ a=>a)≤Wk.b∧m.sum (fun i a=>i.val*a)≤Wk.j ∧
            m 3≤Wk.t∧m 1+m 2+m 3≤Dj (m.sum (fun _ a=>a)) ∧
            kO m≤T:= by
        rcases hor with h | h
        · obtain ⟨hb,hj,ht,hprofile,hw⟩:=hP m h
          exact ⟨hb,hj,ht,hprofile,by omega⟩
        · obtain ⟨hb,hj,ht,hprofile,hw⟩:=hQ m h
          exact ⟨hb,hj,ht,hprofile,by omega⟩
      obtain ⟨hb,hj,ht,hprofile,hw⟩:=Ca
      refine ⟨hb,hj,ht,hprofile,?_⟩
      have hsum: ((P+Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m)+(Q.coeff m)).natDegree≤_
        exact natDegree_add_le _ _
      have hdegree (R:af 4) (hR:m∈R.support→(R.coeff m).natDegree+kO m≤T) :
          (R.coeff m).natDegree≤T - kO m:= by
        by_cases h:m∈R.support
        · have :=hR h
          omega
        · have hz :R.coeff m=0:= by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz,natDegree_zero]
          exact zD0 _
      have hp' := hdegree P (fun h=>(hP m h).2.2.2.2)
      have hq' := hdegree Q (fun h=>(hQ m h).2.2.2.2)
      have :=hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← ajI,map_add,ajI,ajI]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP:= by
    obtain ⟨hP,hp⟩:=aaG.mp hP
    apply aaG.mpr
    constructor
    · intro m hm
      obtain ⟨hb,hj,ht,hprofile,hw⟩:=hP m (MvPolynomial.support_smul hm)
      refine ⟨hb,hj,ht,hprofile,?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h:yZ S (c•P)=c•yZ S P:=(yZ S).map_smul c P
      rw [ajI,ajI] at h
      rw [h]
      exact bpc _ _ c (hp i S hS)
private def bnp (T:ℕ) :
    af 4 →ₗ[ao] (((Fin 4→Fin (Wk.b+1))×Fin (T+1))→ao) :=
  LinearMap.pi fun u =>
    (Polynomial.lcoeff ao u.2.val).comp
      ((MvPolynomial.lcoeff ao[X] (Finsupp.equivFunOnFinite.symm (fun i=>(u.1 i).val))
        : af 4 →ₗ[ao[X]] ao[X]).restrictScalars ao)
private instance bqa (w:I→K) (T:ℕ) :Module.Finite ao (aV w T) := by
  classical
  let f :aV w T →ₗ[ao] (((Fin 4→Fin (Wk.b+1))×Fin (T+1))→ao) :=
    (bnp T).comp (aV w T).subtype
  have hzero (Q:aV w T) (hQ:f Q=0) :Q=0:= by
    obtain ⟨P,hP⟩:= Q
    change Pq w T P at hP
    apply Subtype.ext
    change P=0
    apply MvPolynomial.ext
    intro m
    change _=0
    by_contra hnz
    have hm:=MvPolynomial.mem_support_iff.mpr hnz
    have hT: (P.coeff m).natDegree≤T:=(Nat.le_add_right _ _).trans (hP.2.2.1 m hm)
    let u:Fin 4→Fin (Wk.b+1) := fun i=>⟨m i,Nat.lt_succ_of_le <|
      (zTo i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk :k<T+1
    · have hval :=congrFun hQ (u,⟨k,hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i=>(u i).val))).coeff k=0 at hval
      have heq :Finsupp.equivFunOnFinite.symm (fun i=>(u i).val)=m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz :=f.map_sub P Q
  rw [h,sub_self] at hz
  exact hzero (P-Q) hz
private def aff (w:I→K) (x :ao) (T:ℕ) :aV w T →ₗ[ao] Symbol :=
  (dgt x).comp (aV w T).subtype
private theorem c0X (w:I→K) (x :ao) (hx : ∀ i:I,x≠embed (node i))
    (T:ℕ) (P:af 4) :
    Pq w (T+1) (znf (linearFactor x)*P)↔Pq w T P:= by
  rw [aaG,aaG,crW]
  apply and_congr
  · refine forall_congr' fun m=>forall_congr' fun hm => ?_
    rw [z06,natDegree_mul (br2 x)
      (MvPolynomial.mem_support_iff.mp hm),b7U]
    omega
  · simp only [Contact,cK,map_mul,z9X]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro S
    apply forall_congr'
    intro hS
    generalize primaryM=m
    have hc:IsCoprime (Polynomial.X-Polynomial.C (embed (node i))) (linearFactor x) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx i).symm).isUnit
    exact (hc.pow_left (m:=m)).dvd_mul_left_iff
private theorem gNh (w:I→K) (x :ao) :
    z83 (aff w x 0) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  change LY x P.val=0 at hP
  obtain ⟨Q,hQ⟩:=b03 P.val x hP
  have hp:tB P.val 0:=P.property.2.2.1
  apply Subtype.ext
  change P.val=0
  rw [← hQ]
  suffices Q=0 by simp [this]
  apply MvPolynomial.ext
  intro m
  change _=0
  by_contra hnz
  have hm:m∈P.val.support := by
    rw [← hQ,crW]
    exact MvPolynomial.mem_support_iff.mpr hnz
  have h:=hp m hm
  rw [← hQ,z06,natDegree_mul (br2 x) hnz,
    b7U] at h
  omega
private theorem etP (w:I→K) (x :ao) (hx : ∀ i:I,x≠embed (node i))
    (T:ℕ) :zsE ao (z83 (aff w x (T+1))) =
      zsE ao (aV w T) := by
  let L:aV w T →ₗ[ao] (z83 (aff w x (T+1))) :=
    zTB _ (zTB (aV w (T+1))
      ((zzN ao (znf (linearFactor x))).comp (aV w T).subtype)
      (fun P=>(c0X w x hx T P.val).mpr P.property)) (fun P=> by
        rw [LinearMap.mem_ker]
        change LY x (znf (linearFactor x)*P.val)=0
        simp [LY,linearFactor])
  have hL:Function.Bijective L:= by
    have hnz : (znf (linearFactor x) :af 4)≠0:= by
      simpa only [ne_eq,MvPolynomial.C_eq_zero] using br2 x
    constructor
    · intro P Q h
      apply Subtype.ext
      have heq :=congrArg (fun V:z83 (aff w x (T+1))=>V.val.val) h
      change znf (linearFactor x)*P.val=znf (linearFactor x)*Q.val at heq
      exact mul_left_cancel₀ hnz heq
    · intro P
      have h:LY x P.val.val=0:=LinearMap.mem_ker.mp P.property
      obtain ⟨Q,hQ⟩:=b03 P.val.val x h
      have hmem:Pq w (T+1) (znf (linearFactor x)*Q) := by
        rw [hQ]
        exact P.val.property
      refine ⟨⟨Q,(c0X w x hx T Q).mp hmem⟩,Subtype.ext (Subtype.ext hQ)⟩
  exact (LinearEquiv.ofBijective L hL).finrank_eq.symm
theorem proof :P6_6_3.c1 := by
  classical
  intro w x hr hx
  let r (T:ℕ) :=zsE ao (zWl (aff w x T))
  refine ⟨r,?_,fun T _ => ?_⟩
  · have heq (T:ℕ) :zsE ao (aV w T) =
        ∑ V∈z4x (T+1),r V:= by
      induction T with
      | zero =>
        have h:=z7i
          (K:=ao) (V:=aV w 0) (V₂:=Symbol) (aff w x 0)
        rw [gNh,finrank_bot,Nat.add_zero] at h
        simpa only [Nat.zero_add,Finset.sum_range_one] using h.symm
      | succ T ih =>
        have h:=z7i
          (K:=ao) (V:=aV w (T+1)) (V₂:=Symbol) (aff w x (T+1))
        rw [etP w x hx,ih,Nat.add_comm] at h
        rw [Finset.sum_range_succ]
        exact h.symm
    obtain ⟨e,he,hmem⟩:=hr
    have hi:z14 ao (fun i=>(⟨e i,hmem i⟩:aV w aWx)) :=
      LinearIndependent.of_comp (aV w aWx).subtype he
    rw [← heq]
    simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank
  · let basis :=Module.finBasis ao (zWl (aff w x T))
    choose e he using fun i:Fin (r T)=>LinearMap.mem_range.mp (basis i).property
    refine ⟨fun i=>(e i).val,fun i=>(e i).property,?_⟩
    have h:z14 ao (fun i=>(basis i).val) :=
      basis.linearIndependent.map' (zWl (aff w x T)).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i=>LY x (e i).val)=fun i=>(basis i).val :=funext he
    rwa [heq]
end
end qEtASgc
end
section
set_option autoImplicit true
namespace qEc1Pne
noncomputable section
open aR (ao aO)
open aiI (Symbol acO)
open P6_6 (Wk Dj Gq)
open P6_6_3 (SymbolInProfile)
open gW (V7)
open anm (akp)
open MvPolynomial
open private arA from ProximityPrize.SubmissionLower.L
open scoped BigOperators
private abbrev Exp:=Fin 4 →₀ ℕ
private abbrev cV (m:Exp) :=m.sum (fun _ a=>a)
private abbrev index (m:Exp) :=m.sum (fun i a=>i.val*a)
private abbrev ayF (m:Exp) :=m 1+m 2+m 3
private theorem ay9 (m:Exp) :cV m=m 0+ayF m:= by
  simp [cV,ayF,z9d,zCS,Nat.add_assoc]
private theorem en9 (m:Exp) :index m=m 1+2*m 2 + 3*m 3:= by
  simp [index,z9d,zCS]; omega
private def ary (u d j t:ℕ) :Finset Exp :=
  (z4x (min d (min t (j/3))+1)).biUnion (fun z =>
    (z4x (min (d - z) ((j-3*z)/2)+1)).biUnion (fun y =>
      (z4x (min (d - z - y) (j-3*z - 2*y)+1)).image (fun x =>
        Finsupp.equivFunOnFinite.symm ![u - z - y - x,x,y,z])))
private theorem eiH (u d j t:ℕ) : (ary u d j t).card≤V7 d j t:= by
  unfold ary V7
  refine Finset.card_biUnion_le.trans (zQk fun z _ => ?_)
  refine Finset.card_biUnion_le.trans (zQk fun y _ => ?_)
  exact Finset.card_image_le.trans_eq (Finset.card_range _)
private theorem ez3 {u d j t:ℕ} {m:Exp} (hu:cV m=u)
    (hd:ayF m≤d) (hj:index m≤j) (ht:m 3≤t) :
    m∈ary u d j t:= by
  classical
  rw [ay9] at hu
  simp only [ayF] at hd hu
  rw [en9] at hj
  simp only [ary,Finset.mem_biUnion,Finset.mem_range,Finset.mem_image]
  refine ⟨m 3,by omega,m 2,by omega,m 1,by omega,?_⟩
  have hv :u - m 3 - m 2 - m 1=m 0:= by omega
  rw [hv]
  ext i
  fin_cases i <;> simp
private def slots (B j t f :ℕ) :Finset Exp :=
  (z4x (B+1)).biUnion (fun u=>ary u (min u (Dj (u+f))) j t)
private theorem cp6 (B j t f :ℕ) :
    (slots B j t f).card ≤ ∑ u∈z4x (B+1),
      V7 (min u (Dj (u+f))) j t :=
  Finset.card_biUnion_le.trans (zQk fun u _=>eiH u _ _ _)
private def aS2 :Submodule ao Symbol :=
  restrictSupport ao {m:Exp |
    cV m≤Wk.b∧index m≤Wk.j∧m 3≤Wk.t∧ayF m≤Dj (cV m)}
private theorem cDs {P:Symbol} (h:P∈aS2) :
    aO (akp P) Wk := by
  refine ⟨zf9 fun m hm=>(h hm).1,zf9 fun m hm=>(h hm).2.1,?_⟩
  change P.degreeOf 3≤Wk.t
  exact degreeOf_le_iff.mpr fun m hm=>(h hm).2.2.1
private theorem ezX {P:Symbol} (h:aO (akp P) Wk)
    (hp:SymbolInProfile P) :P∈aS2 := by
  intro m hm
  exact ⟨(le_totalDegree hm).trans h.1,
    (Finset.le_sup (f :=index) hm).trans h.2.1,
    (le_degreeOf_of_mem_support 3 hm).trans h.2.2,hp m hm⟩
private theorem c5t {F Q:Symbol} (hF:F≠0) (hQ:Q≠0)
    (hp:F*Q∈aS2) :
    F.totalDegree+Q.totalDegree≤Wk.b ∧
      acO F+acO Q≤Wk.j∧F.degreeOf 3+Q.degreeOf 3≤Wk.t:= by
  obtain ⟨hb,hj,ht⟩:=cDs hp
  change (F*Q).totalDegree≤_ at hb
  change acO (F*Q)≤_ at hj
  change (F*Q).degreeOf 3≤_ at ht
  rw [totalDegree_mul_of_isDomain hF hQ] at hb
  rw [arA,weightedTotalDegree_mul _ _ _ hF hQ,
    ← arA,← arA] at hj
  rw [degreeOf_mul_eq hF hQ] at ht
  exact ⟨hb,hj,ht⟩
private theorem dhE (P:Symbol) (hP:P≠0) :
    ∃ m∈P.support,cV m=P.totalDegree := by
  obtain ⟨m,hm,hg⟩:=Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hP) cV
  exact ⟨m,hm,hg.symm⟩
private theorem VB (M:ℕ) (m:Exp) :
    Finsupp.weight (![M,M+1,M+1,M + 1] :Fin 4→ℕ) m =
      M*cV m+ayF m:= by
  rw [ay9]
  simp [ayF,Finsupp.weight_apply,z9d,zCS,smul_eq_mul]; ring
private theorem eu7 {F Q:Symbol} (hF:F≠0)
    (hQ:Q≠0) (hp:F*Q∈aS2) {m:Exp} (hm:m∈Q.support)
    (hu:cV m= Q.totalDegree) :
    ayF m≤Dj (Q.totalDegree+F.totalDegree) := by
  let M:=Wk.b+1
  let w:Fin 4→ℕ := ![M,M+1,M+1,M + 1]
  have hw (a :Exp) :Finsupp.weight w a=M*cV a+ayF a :=VB M a
  have hb: (F*Q).totalDegree≤Wk.b:=(cDs hp).1
  have hupper :weightedTotalDegree w (F*Q) ≤
      M*(F*Q).totalDegree+Dj ((F*Q).totalDegree) := by
    apply zf9
    intro a ha
    rw [hw]
    have hale :cV a≤(F*Q).totalDegree :=le_totalDegree ha
    by_cases htop:cV a=(F*Q).totalDegree
    · rw [htop]
      exact Nat.add_le_add_left (htop ▸ (hp ha).2.2.2) _
    · have hnext:M*(cV a+1)≤M*(F*Q).totalDegree :=
        Nat.mul_le_mul_left M (by omega)
      have hder :ayF a≤M :=
        Nat.le_succ_of_le ((by rw [ay9]; omega :ayF a≤ cV a).trans
          (hale.trans hb))
      rw [Nat.mul_succ] at hnext
      omega
  obtain ⟨a,ha,hg⟩:=dhE F hF
  have hleft:=le_weightedTotalDegree w ha
  have hright:=le_weightedTotalDegree w hm
  rw [hw,hg] at hleft
  rw [hw,hu] at hright
  rw [weightedTotalDegree_mul w F Q hF hQ,totalDegree_mul_of_isDomain hF hQ,
    Nat.mul_add] at hupper
  rw [Nat.add_comm Q.totalDegree F.totalDegree]
  omega
private theorem eu9 {F Q:Symbol} (hF:F≠0)
    (hQ:Q≠0) (hp:F*Q∈aS2) {m:Exp} (hm:m∈Q.support)
    (hu:cV m= Q.totalDegree) :
    m∈slots (Wk.b-F.totalDegree) (Wk.j-acO F)
      (Wk.t - F.degreeOf 3) F.totalDegree := by
  obtain ⟨hb,hj,ht⟩:=c5t hF hQ hp
  have hi:index m≤acO Q:=Finset.le_sup (f :=index) hm
  have hz :=le_degreeOf_of_mem_support 3 hm
  apply Finset.mem_biUnion.mpr
  refine ⟨Q.totalDegree,Finset.mem_range.mpr (by omega),ez3 hu ?_ ?_ ?_⟩
  · apply le_min
    · have hg:=ay9 m
      omega
    · exact eu7 hF hQ hp hm hu
  · omega
  · omega
theorem proof :P6_6_3.c2 := by
  classical
  intro F hF r e hli he
  by_cases hr :r=0
  · rw [hr]
    exact zD0 _
  choose Q hQ using fun i=>(he i).2.2
  have he_mem (i:Fin r) :e i∈aS2 :=
    ezX (he i).1 (he i).2.1
  let i₀:Fin r :=⟨0,Nat.pos_of_ne_zero hr⟩
  have hQ₀:Q i₀≠0:= fun h=>hli.ne_zero i₀ (by rw [hQ i₀,h,mul_zero])
  have hp₀:F*Q i₀∈aS2 :=hQ i₀ ▸ he_mem i₀
  obtain ⟨hb,hj,ht⟩:=c5t hF hQ₀ hp₀
  have hfit : (akp F).b≤Wk.b∧(akp F).j≤Wk.j ∧
      (akp F).t≤Wk.t:= by
    change F.totalDegree≤Wk.b∧acO F≤Wk.j∧F.degreeOf 3≤Wk.t
    exact ⟨by omega,by omega,by omega⟩
  let A:=slots (Wk.b-F.totalDegree) (Wk.j-acO F)
    (Wk.t - F.degreeOf 3) F.totalDegree
  let coord:Symbol →ₗ[ao] (↥A→ao) :=LinearMap.pi fun m=>lcoeff ao m.val
  let mulF:Symbol →ₗ[ao] Symbol:=zzN ao F
  have hind:z14 ao (fun i=>coord (Q i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    let q:Symbol := ∑ i,a i•Q i
    have hzero :coord q=0:= by
      dsimp only [q]
      rw [map_sum]
      simpa only [map_smul] using ha
    have hmul :F*q = ∑ i,a i•e i:= by
      change mulF q= _
      dsimp only [q]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _=> by rw [map_smul,hQ i]; rfl
    have hp:F*q∈aS2 := by
      rw [hmul]
      exact Submodule.sum_mem _ fun i _=>Submodule.smul_mem _ _ (he_mem i)
    have hq:q=0:= by
      by_contra hn
      obtain ⟨m,hm,hu⟩:=dhE q hn
      have hmA:m∈A:=eu9 hF hn hp hm hu
      have hc:q.coeff m=0:=congrFun hzero ⟨m,hmA⟩
      exact (mem_support_iff.mp hm) hc
    exact Fintype.linearIndependent_iff.mp hli a (by rw [← hmul,hq,mul_zero])
  have hdim:r≤A.card:= by
    simpa only [Fintype.card_fin,Module.finrank_fintype_fun_eq_card,Fintype.card_coe]
      using hind.fintype_card_le_finrank
  simp only [Gq,hfit.1,hfit.2.1,hfit.2.2,and_self,ite_true]
  exact hdim.trans (cp6 _ _ _ _)
end
end qEc1Pne
end
section
set_option autoImplicit true
namespace qrpOkAa
noncomputable section
open Polynomial
open MvPolynomial UniqueFactorizationMonoid
open P6_6
open aR (ao af Shape aO shape Z8 jet cK wU extend)
open anm (bNR aXI)
open private IM from ProximityPrize.SubmissionLower.AB
open private cpo from ProximityPrize.SubmissionLower.E1
open private aDq from ProximityPrize.SubmissionLower.BF
open private prod_shape cwR from ProximityPrize.SubmissionLower.ZOGAUga
open scoped BigOperators
private def series (S:ao[X]) :af 4 →+* MvPowerSeries (Fin 4) ao[X] :=
  MvPolynomial.coeToMvPowerSeries.ringHom.comp (IM S)
private theorem le_series_order {S:ao[X]} {R:af 4} {d:ℕ} :
    (d:ℕ∞)≤(series S R).order↔wU R S d:= by
  constructor
  · intro h m hm
    have hn:MvPowerSeries.coeff m (series S R)≠0:=MvPolynomial.mem_support_iff.mp hm
    exact ENat.natCast_le_natCast.mp (h.trans (MvPowerSeries.order_le hn))
  · intro h
    apply MvPowerSeries.nat_le_order
    intro m hm
    change (Z8 R S).coeff m=0
    by_contra hn
    exact (not_lt_of_ge (h m (MvPolynomial.mem_support_iff.mpr hn))) hm
private theorem asl (S:ao[X]) (R:af 4) :
    (Z8 R S).totalDegree≤R.totalDegree := by
  rw [← weightedTotalDegree_one,← weightedTotalDegree_one]
  change (bind₁ (fun i=>MvPolynomial.X i+MvPolynomial.C (jet S i)) R).weightedTotalDegree 1≤_
  apply weightedTotalDegree_bind₁_le_of_le (1 :Fin 4→ℕ) 1
  intro i
  exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    (Submodule.add_mem _ (X_mem_restrictWeightedDegree _ _ _ le_rfl)
      (C_mem_restrictWeightedDegree _ _ _))
private theorem series_order {S:ao[X]} {R:af 4} (hR:R≠0) :
    (series S R).order=(ambientOrder R S:ℕ∞) := by
  classical
  have hne :series S R≠0:= by
    intro h
    have hs :IM S R=0:=MvPolynomial.coe_eq_zero_iff.mp h
    apply hR
    exact bao.gqg (jet S) (hs.trans (map_zero (IM S)).symm)
  let d:=(series S R).order.toNat
  have hd: (series S R).order=(d:ℕ∞) :=
    (MvPowerSeries.ne_zero_iff_order_finite.mp hne).symm
  obtain ⟨m,hm,hdeg⟩:=(MvPowerSeries.order_eq_nat.mp hd).1
  have hs :m∈(Z8 R S).support :=MvPolynomial.mem_support_iff.mpr hm
  have hb:d≤(shape R).b:=hdeg ▸ (zY3 hs).trans (asl S R)
  have ho:wU R S d:=le_series_order.mp hd.ge
  have hz :wU R S 0:= fun _ _=>zD0 _
  have hg:wU R S (ambientOrder R S) :=
    Nat.findGreatest_spec (zD0 (shape R).b) hz
  have hgd:=le_series_order.mpr hg
  rw [hd] at hgd
  have hda :d≤ambientOrder R S:=Nat.le_findGreatest hb ho
  exact hd.trans (congrArg (fun k :ℕ=>(k :ℕ∞))
    (le_antisymm hda (ENat.natCast_le_natCast.mp hgd)))
private theorem order_zero_of_eval {S:ao[X]} {R:af 4} (h:cK R S≠0) :
    (series S R).order=0:= by
  have hc:MvPowerSeries.coeff 0 (series S R)≠0:= by
    change (IM S R).coeff 0≠0
    rwa [← MvPolynomial.constantCoeff_eq,cpo]
  exact le_antisymm (by simpa only [map_zero,Nat.cast_zero] using MvPowerSeries.order_le hc) bot_le
private theorem order_pow (S:ao[X]) {R:af 4} (hR:R≠0) (a :ℕ) :
    (series S (R^a)).order=((a*ambientOrder R S:ℕ) :ℕ∞) := by
  induction a with
  | zero =>
    rw [pow_zero,map_one,zero_mul,Nat.cast_zero]
    exact MvPowerSeries.weightedOrder_one (fun _:Fin 4=>1)
  | succ a ih =>
    rw [pow_succ,map_mul,MvPowerSeries.order_mul,ih,series_order hR,Nat.succ_mul,Nat.cast_add]
private theorem jet_shape (R:af 4) (h:0<(shape R).b) :JetShape (shape R) := by
  classical
  refine ⟨h,(aDq R).1,?_⟩
  apply zf9
  intro m hm
  have hd:m.degree=m 0+m 1+m 2+m 3:= by rw [Finsupp.degree_eq_sum,zmL]
  have hb:m.degree≤R.totalDegree :=zY3 hm
  rw [hd] at hb
  have ht:=zTo (3:Fin 4) hm
  rw [z9d _ _ (fun _=>Nat.mul_zero _),zmL]
  change 0*m 0+1*m 1+2*m 2 + 3*m 3≤2*R.totalDegree+R.degreeOf 3
  omega
private theorem eval_ne_of_degree_zero {R:af 4} {S:ao[X]}
    (hn:R≠0) (hd: (shape R).b=0) :cK R S≠0:= by
  have he :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (show R.totalDegree=0 from hd)
  have hc:R.coeff 0≠0:= fun hz=>hn (he.trans (hz ▸ map_zero znf))
  have hv :cK R S=R.coeff 0 :=
    (congrArg (fun r=>cK r S) he).trans (z9X _)
  rwa [hv]
private theorem cEa {Q R:af 4} {b:Shape} (hQ:Q≠0) (h:R∣Q)
    (hb:aO (shape Q) b) :aO (shape R) b:= by
  obtain ⟨h₁,h₂,h₃⟩:=bNR hQ h
  exact ⟨h₁.trans hb.1,h₂.trans hb.2.1,h₃.trans hb.2.2⟩
theorem proof :P6_6_3.c3:= by
  classical
  intro Δ s P Q l hQ hbox hw hp ho
  let _:StrongNormalizationMonoid (af 4) :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let A:=normalizedFactors Q
  let T:=A.toFinset
  let F:=T.filter fun r=>0<(shape r).b ∧ ¬ r∣P
  let a (r :af 4) :=A.count r
  let n:=Fintype.card ↥F
  let j:Fin n ≃ ↥F:=(Fintype.equivFin ↥F).symm
  let R:Fin n→af 4 := fun i=>(j i).val
  let e :Fin n→ℕ:= fun i=>a (R i)
  have hmem (i:Fin n) :R i∈T∧0<(shape (R i)).b ∧ ¬ R i∣P :=
    Finset.mem_filter.mp (j i).property
  have hirr (r :af 4) (hr :r∈T) :Irreducible r :=
    irreducible_of_normalized_factor _ (Multiset.mem_toFinset.mp hr)
  have hgrp:A.prod = ∏ r∈T,r^a r :=Finset.prod_multiset_count A
  have hassoc:Associated A.prod Q:=prod_normalizedFactors hQ
  have hd (i:Fin n) :R i∣Q :=
    dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (hmem i).1)
  have hprod: (∏ i,R i^e i)∣Q:= by
    rw [show (∏ i,R i^e i) = ∏ r : ↥F,r.val^a r.val from j.prod_comp (fun r=>r.val^a r.val),
      Finset.prod_coe_sort F (fun r=>r^a r)]
    exact (Finset.prod_dvd_prod_of_subset F T _ (zT0 _ _)).trans
      (hgrp ▸ hassoc.dvd)
  refine ⟨n,R,e,⟨?_,?_,fun i=>(hmem i).2.2,fun i=>cEa hQ (hd i) hbox,?_,?_⟩,?_⟩
  · intro i
    exact ⟨hirr _ (hmem i).1,jet_shape _ (hmem i).2.1,cwR hQ (hd i) hw⟩
  · intro i
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp (hmem i).1)
  · have h:=cEa hQ hprod hbox
    change aO (shape (factorProd (fun i=>R i^e i) Finset.univ)) _ at h
    rw [prod_shape _ _ (fun i=>pow_ne_zero _ (hirr _ (hmem i).1).ne_zero)] at h
    have he : (shape ∘ fun i=>R i^e i)=fun i=>(shape (R i)).scale (e i) :=
      funext fun i=>aXI (R i) (hirr _ (hmem i).1).ne_zero (e i)
    rwa [he] at h
  · intro γ hγ
    let S:=extend (s γ)
    have hout (r :af 4) (hr :r∈T) (hf :r∉F) :cK r S≠0:= by
      by_cases hdiv :r∣P
      · intro hz
        apply hp γ hγ
        have he :cK r S∣cK P S:=map_dvd (zY9 (jet S)) hdiv
        rwa [hz,zero_dvd_iff] at he
      · exact eval_ne_of_degree_zero (hirr r hr).ne_zero
          (Nat.eq_zero_of_not_pos fun hpos=>hf (Finset.mem_filter.mpr ⟨hr,hpos,hdiv⟩))
    obtain ⟨u,hu⟩:=hassoc
    have hu0:cK (u:af 4) S≠0 :=
      (u.isUnit.map (zY9 (jet S))).ne_zero
    apply ENat.natCast_le_natCast.mp
    calc
      (l:ℕ∞)≤(series S Q).order :=le_series_order.mpr (ho γ hγ)
      _=(series S A.prod).order := by
        rw [← hu,map_mul,MvPowerSeries.order_mul,order_zero_of_eval hu0,add_zero]
      _ = ∑ r∈T,(series S (r^a r)).order := by rw [hgrp,map_prod,MvPowerSeries.order_prod]
      _ = ∑ r∈F,(series S (r^a r)).order := by
        symm
        apply Finset.sum_subset (zT0 _ _)
        intro r hr hf
        apply order_zero_of_eval
        change zY9 (jet S) (r^a r)≠0
        rw [map_pow]
        exact pow_ne_zero _ (hout r hr hf)
      _ = ∑ i,(series S (R i^e i)).order := by
        rw [show (∑ i,(series S (R i^e i)).order) =
          ∑ r : ↥F,(series S (r.val^a r.val)).order from
          j.sum_comp (fun r=>(series S (r.val^a r.val)).order)]
        exact (Finset.sum_coe_sort F _).symm
      _=((∑ i,e i*ambientOrder (R i) S:ℕ) :ℕ∞) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun i _=>order_pow S (hirr _ (hmem i).1).ne_zero _
  · intro i
    have hA:R i∈normalizedFactors Q:=Multiset.mem_toFinset.mp (hmem i).1
    have hpow (k :ℕ) :R i^k∣Q↔k≤e i:= by
      rw [pow_dvd_iff_le_emultiplicity,emultiplicity_eq_count_normalizedFactors (hirr _ (hmem i).1) hQ,
        normalize_normalized_factor _ hA,ENat.natCast_le_natCast]
    exact ⟨(hpow _).mpr le_rfl,fun h=>Nat.not_succ_le_self _ ((hpow _).mp h)⟩
end
end qrpOkAa
end
