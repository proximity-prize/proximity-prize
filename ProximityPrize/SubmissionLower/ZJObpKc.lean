import ProximityPrize.SubmissionLower.ZXxMpWa
set_option Elab.async false
section
set_option autoImplicit true
namespace qeu0RUc
noncomputable section
open aR (af)
open oR (separant)
open we (cH eT Yk fW D7 JZ)
open yz (F3 bpH)
open P6_6_5 (Fb)
open qSCPCwb (Dm BW Ji aap Lx avD
  Vk Gf)
open MvPolynomial
open scoped BigOperators
open private bHC from ProximityPrize.SubmissionLower.BG
open private cUa from ProximityPrize.SubmissionLower.BG
open private cTL from ProximityPrize.SubmissionLower.A2
theorem avw {f :af 3} {P:Ideal (eT 3)} :
    P∈yD f ↔ ¬ Fb f ∧
      P∈(BW f).retainedMinimalPrimes (fW (separant f)) := by
  classical
  by_cases hf :Fb f <;> simp [yD,hf]
theorem ePv {n:ℕ} (f :Fin n→af 3) :
    Ji f=Finset.univ.biUnion fun i =>
      (yD (f i)).image (fun P=>(i,P)) := by
  classical
  unfold Ji
  congr 1
  funext i
  by_cases hf :Fb (f i) <;> simp [yD,hf]
theorem azC {n:ℕ} {f :Fin n→af 3} {a :aap n} :
    a∈Ji f↔a.2∈yD (f a.1) := by
  classical
  rcases a with ⟨i,P⟩
  exact qSCPCwb.azC.trans avw.symm
theorem gw3 {n:ℕ} (f :Fin n→af 3) (v :aap n→ℕ) :
    (∑ a∈Ji f,v a) =
      ∑ i,∑ P∈yD (f i),v (i,P) := by
  classical
  rw [ePv,Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_image (fun _ _ _ _ h=>(Prod.mk.inj h).2)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨P,_,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨Q,_,he⟩:=Finset.mem_image.mp hb
    exact hij (Prod.mk.inj he).1.symm
theorem cHs {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) :
    0<Lx f P∧Lx f P < ⊤ := by
  classical
  have hm:=(Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2).1
  let:P.IsPrime :=hm.isPrime
  rw [Lx,dite_eq_left hm.isPrime]
  exact ⟨aY1.exy P hm.le,yz.bsa hm⟩
theorem cHt {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) :
    ((Lx f P).toNat :ℕ∞)=Lx f P :=
  ENat.natCast_toNat (cHs hP).2.ne
theorem dOv {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) :0<(Lx f P).toNat := by
  have h:=(cHs hP).1
  rw [← cHt hP] at h
  exact_mod_cast h
theorem cfr {f :af 3} (hf :Irreducible f)
    {P:Ideal (eT 3)} (hP:P∈yD f) :
    (affineHilbertPolynomial P).natDegree=1 := by
  obtain ⟨hw,hret⟩:=avw.mp hP
  have hmin:=(Ideal.mem_retainedMinimalPrimes.mp hret).1
  let:=hmin.isPrime
  let H :Ideal (eT 3) :=Ideal.span {fW f}
  let g:=fW (Dm f)
  have heq :BW f=H ⊔ Ideal.span {g} := by
    rw [← Ideal.span_union]
    rfl
  have hHP:H≤P:=le_sup_left.trans (heq ▸ hmin.le)
  obtain ⟨Q,hQ,hQP⟩:=Ideal.exists_minimalPrimes_le hHP
  let:=hQ.isPrime
  have hgQ:g∉Q:= by
    intro hg
    obtain ⟨a,ha,hga⟩:=Ideal.exists_mul_mem_of_mem_minimalPrimes hQ hg
    exact ha (Ideal.mem_span_singleton.mpr
      (cTL hf hw a (Ideal.mem_span_singleton.mp hga)))
  have hP' : P∈(Q ⊔ Ideal.span {g}).minimalPrimes := by
    have hle :H ⊔ Ideal.span {g} ≤ Q ⊔ Ideal.span {g} := sup_le_sup_right hQ.le _
    refine ⟨⟨hmin.isPrime,sup_le hQP (le_sup_right.trans (heq ▸ hmin.le))⟩,?_⟩
    intro J hJ hJP
    exact hmin.2 ⟨hJ.1,heq.trans_le (hle.trans hJ.2)⟩ hJP
  have hF:fW f≠0 :=
    fun h=>hf.ne_zero (map_injective _ Yk (h.trans (map_zero _).symm))
  have hdQ:=natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hQ
  have hdP:=principalCut_natDegree_affineHilbertPolynomial_add_one hgQ hP'
  rw [Nat.card_fin] at hdQ
  omega
theorem gnI {v :ℕ} {f :af 3} (hf :Irreducible f)
    {P:Ideal (eT 3)} (hP:P∈yD f) :aFK v f P:= by
  have hm:=Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2
  let:=hm.1.isPrime
  obtain ⟨hprime,hdim⟩:=bHC f P hm.2
  refine ⟨hprime.comap (afR v),?_⟩
  unfold i9
  rw [natDegree_affineHilbertPolynomial_comap_of_surjective (afR v)
      (monomialMap_surjective (aIn v)),hdim,cfr hf hP]
private theorem cMX {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) {x :Fin 3→cH} (hx :x∈D7 f P) :
    eval x (fW f)=0 :=
  hx.1 _ ((Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2).1.le
    (Ideal.subset_span (by simp)))
private theorem eEM {v :ℕ} {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) (T:Gf v f) (hnext:fW (Vk f)∉P) :
    T.next∉F3 f P:= by
  intro hn
  have hm:=Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2
  let:=hm.1.isPrime
  have hvanish:fW (separant f)*fW (Vk f) ∈
      vanishingIdeal cH (zeroLocus cH P) := by
    intro x hx
    change eval x (_ *_)=0
    rw [map_mul]
    by_cases hs :eval x (fW (separant f))=0
    · rw [hs,zero_mul]
    · have hr :x∈D7 f P:=⟨hx,hs⟩
      have he :eval (JZ f x) T.next=0:=hn _ ⟨x,hr,rfl⟩
      rw [(bpH T.next_represents (cMX hP hr) hs).mp he,
        mul_zero]
  rw [IsPrime.vanishingIdeal_zeroLocus P] at hvanish
  exact (hm.1.isPrime.mem_or_mem hvanish).elim hm.2 hnext
theorem eMx {v :ℕ} {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) (hcurve :aFK v f P) (T:Gf v f)
    (hnext:fW (Vk f)∉P) :
    (avD f P).Finite∧((avD f P).ncard:ℚ)≤pN v f P:= by
  let h:T.next∈restrictSupport cH (Wa v) :=T.next_box
  let l:=monomialLift T.next h
  have hmap :afR v l=T.next:=monomialMap_monomialLift _ _
  have hl:l∉i9 v f P:= by
    intro hm
    change afR v l∈F3 f P at hm
    rw [hmap] at hm
    exact eEM hP T hnext hm
  let J:=i9 v f P ⊔ Ideal.span {l}
  obtain ⟨hdim,hbound⟩:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hcurve.1 hl (totalDegree_monomialLift_le_one _ _)
  change (affineHilbertPolynomial J).natDegree≤_ at hdim
  rw [hcurve.2] at hdim hbound
  have hzero : (affineHilbertPolynomial J).natDegree=0:=Nat.eq_zero_of_le_zero hdim
  have hdeg:affineDegree J≤pN v f P:= by
    rw [pN,affineDegree_of_natDegree_eq_zero hzero,affineDegree,hcurve.2]
    simpa [J] using hbound
  obtain ⟨hfinite,hcard⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K:=cH) J hzero
  let m:= fun x=>monomialPoint (Wa v) (JZ f x)
  have hinj:Function.Injective m :=
    (monomialPoint_injective (aIn v)).comp (cUa f)
  have hsubset :m '' avD f P⊆zeroLocus cH J:= by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    apply sup_le
    · apply mem_zeroLocus_iff_le_ker_aeval.mp
      apply (monomialPoint_mem_zeroLocus_comap_iff (aIn v) _ _).mpr
      exact zeroLocus_vanishingIdeal_le _ ⟨x,hx.1,rfl⟩
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker,aeval_monomialPoint,hmap]
      exact (bpH T.next_represents
        (cMX hP hx.1) hx.1.2).mpr hx.2
  refine ⟨(hfinite.subset hsubset).of_finite_image hinj.injOn,?_⟩
  rw [← Set.ncard_image_of_injective _ hinj]
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard hsubset hfinite)).trans (hcard.trans hdeg)
end
end qeu0RUc
end
section
set_option autoImplicit true
namespace qeu0RUc
noncomputable section
open aR (af qE)
open oR (separant)
open we (DO cH eT fW vY JZ D7)
open yz (S3 oe ahz)
open P6_6 (bf mW)
open P6_6_5 (Zl)
open qSCPCwb (Gf Uj Bk)
open MvPolynomial
open scoped BigOperators Pointwise
open private bK6 bmt from ProximityPrize.SubmissionLower.BG
open private bvn from ProximityPrize.SubmissionLower.BG
private theorem gpO {v n:ℕ} {f :Fin n→af 3} (hf :Zl v f)
    (i:Fin n) :DO (vY (fW (separant (f i)))) (mW v) 0:= by
  let g:=f i
  have hF:DO (vY (fW g)) (mW v) 0 :=
    bmt
      ((Finset.single_le_sum (fun j _=>Nat.zero_le ((f j).totalDegree))
        (Finset.mem_univ i)).trans hf.total)
      ((Finset.single_le_sum (fun j _=>Nat.zero_le (qE (f j)))
        (Finset.mem_univ i)).trans hf.index)
      ((Finset.single_le_sum (fun j _=>Nat.zero_le ((f j).degreeOf 2))
        (Finset.mem_univ i)).trans hf.top) le_rfl (bvn g)
  have hderiv :vY (fW (separant g))=pderiv (2 :Fin 4) (vY (fW g)) := by
    unfold vY fW separant
    rw [show (2 :Fin 4)=(2 :Fin 3).castSucc from rfl,
      pderiv_rename (Fin.castSucc_injective 3),pderiv_map]
  change DO (vY (fW (separant g))) (mW v) 0
  rw [hderiv]
  intro a ha
  rw [MvPolynomial.mem_support_iff,coeff_pderiv] at ha
  have h:=hF _ (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul ha))
  simp only [Finsupp.add_apply,Finsupp.single_apply,ite_true] at h
  rcases h with ⟨hb,hj,ht,hh⟩
  exact ⟨by omega,by omega,by omega,hh⟩
private theorem eNn {v n:ℕ} {f :Fin n→af 3} (hf :Zl v f)
    (i:Fin n) (r :ℕ) :
    DO (vY (fW (separant (f i)))^r)
      ⟨r*(mW v).b,r*(mW v).j,r*(mW v).t⟩ 0:= by
  classical
  induction r with
  | zero =>
      simp only [pow_zero,DO,support_one,Finset.mem_singleton]
      rintro a rfl
      simp
  | succ r ih =>
      intro a ha
      rw [pow_succ] at ha
      obtain ⟨b,hb,c,hc,rfl⟩:=Finset.mem_add.mp (support_mul _ _ ha)
      have ⟨hb₀,hb₁,hb₂,hb₃⟩:=ih b hb
      have ⟨hc₀,hc₁,hc₂,hc₃⟩:=gpO hf i c hc
      simp only [Finsupp.add_apply,Nat.succ_mul] at *
      exact ⟨by omega,by omega,by omega,by omega⟩
theorem dM0 {v n:ℕ} {f :Fin n→af 3} (hf :Zl v f)
    (i:Fin n) (P:Ideal (eT 3)) (T:Gf v (f i))
    (hcurve :aFK v (f i) P) (hone :1≤pN v (f i) P) :
    ∃ Q:Bk,Q.IsPrime∧(affineHilbertPolynomial Q).natDegree≤1 ∧
      affineDegree Q≤pN v (f i) P ∧
      ∀ y∈D7 (f i) P,Uj (f i) T.numerator y∈zeroLocus cH Q:= by
  let A:=monomialPoint (Wa v) '' S3 (f i) P
  have hA:i9 v (f i) P=vanishingIdeal cH A:= by
    ext p
    constructor
    · intro hp
      rintro _ ⟨z,hz,rfl⟩
      rw [aeval_monomialPoint]
      exact hp z hz
    · intro hp z hz
      have he :=hp _ ⟨z,hz,rfl⟩
      rwa [aeval_monomialPoint] at he
  obtain ⟨D,hD_eq⟩ : ∃ D:eT 4,
      D =vY (fW (separant (f i)))^(bf-4) :=⟨_,rfl⟩
  have hD:D∈restrictSupport cH (Wa v) := by
    change DO D (RY v) bf
    rw [hD_eq]
    exact b0q v (eNn hf i (bf-4))
  have hN (j:Fin aR.bf) :
      T.numerator j∈restrictSupport cH (Wa v) := by
    change DO (T.numerator j) (RY v) bf
    exact dMX v (T.coefficient_box j)
  let d:=monomialLift D hD
  let ν (j:Fin aR.bf) :=monomialLift (T.numerator j) (hN j)
  have hdeval (z :oe) :eval (monomialPoint (Wa v) z) d=eval z D:= by
    have hmap :afR v d=D:=monomialMap_monomialLift D hD
    simpa only [aeval_eq_eval,hmap] using aeval_monomialPoint z d
  have hνeval (z :oe) (j:Fin aR.bf) :
      eval (monomialPoint (Wa v) z) (ν j)=eval z (T.numerator j) := by
    have hmap :afR v (ν j)=T.numerator j:=monomialMap_monomialLift _ _
    simpa only [aeval_eq_eval,hmap] using aeval_monomialPoint z (ν j)
  have hden (z) (hz :z∈A) :eval z d≠0:= by
    obtain ⟨_,⟨x,hx,rfl⟩,rfl⟩:=hz
    rw [hdeval,hD_eq,map_pow,ahz]
    exact pow_ne_zero _ hx.2
  obtain ⟨Q,hp,hd,hb,hz⟩:=bK6 A _ hA hcurve.1 hcurve.2 hone d ν
    (totalDegree_monomialLift_le_one _ _) (fun j=>totalDegree_monomialLift_le_one _ _) hden
  refine ⟨Q,hp,hd,hb,fun x hx => ?_⟩
  have hz' := hz (monomialPoint (Wa v) (JZ (f i) x)) ⟨_,⟨x,hx,rfl⟩,rfl⟩
  unfold Uj
  simpa only [hνeval,hdeval,hD_eq,map_pow,ahz] using hz'
end
end qeu0RUc
end
section
set_option autoImplicit true
namespace qeu0RUc
noncomputable section
open P6_6_5 (tC)
open we (DO eT)
open yz (oe ay3 oF Ny alT nD)
open zP (Exponent a9X ke a3z auv a5J aIA
  LK cWU bIk)
open P6_6 (bf mW LN)
open MvPolynomial
open scoped BigOperators Pointwise
open private c0v cK8 bCe bQd from ProximityPrize.SubmissionLower.BG
private theorem bDY:zP.c1 :=
  abG.of_children cxS.proof cxT.proof
private theorem efN :zP.c2 :=
  aaq.of_children cxU.proof cxV.proof
    (as3.of_children bRi.proof aY0.proof)
theorem bOc {v :ℕ}
    (F G E L:eT 4) (hF:F≠0) (hG:DO G (tC (mW v)) 1)
    (hE :DO E (LN (bf+1) (mW v)) (bf - 1))
    (hL:DO L (RY v) bf) (points :Finset oe)
    (hpoints : ∀ y∈points,oF y∈(ay3 F G E L).minimalPrimes) :
    (↑(∑ y∈points,(Ny (ay3 F G E L) y).toNat) :ℝ) ≤
      T7 v (alT F) := by
  classical
  let A:Fin 4→Finset Exponent :=
    ![a3z F,auv (tC (mW v)) 1,
      auv (LN (bf+1) (mW v)) (bf - 1),
      auv (RY v) bf]
  let f :Fin 4→eT 4 := ![F,G,E,L]
  have hz : ∀ i,0∈A i:= by
    intro i
    fin_cases i
    · obtain ⟨e,he⟩:=support_nonempty.mpr hF
      exact a5J.mpr ⟨e,he,fun _=>Nat.zero_le _⟩
    · exact bQd _ _
    · exact bQd _ _
    · exact bQd _ _
  have hd : ∀ i,a9X (A i) := by
    intro i
    fin_cases i
    · exact cK8 F
    · exact bCe _ _
    · exact bCe _ _
    · exact bCe _ _
  have hv (j:Fin 4) : ∃ i,Finsupp.single j 1∈A i:= by
    exact ⟨3,aIA.mpr (aIn v j)⟩
  have hsup : ∀ i,(f i).support⊆A i:= by
    intro i
    fin_cases i
    · exact fun a ha=>a5J.mpr ⟨a,ha,le_rfl⟩
    · exact fun a ha=>aIA.mpr (hG a ha)
    · exact fun a ha=>aIA.mpr (hE a ha)
    · exact fun a ha=>aIA.mpr (hL a ha)
  have hJ:ke f=ay3 F G E L:= by
    unfold ke ay3
    apply congrArg Ideal.span
    ext p
    simp [f,or_left_comm,or_comm]
  obtain ⟨hfinite,hmv⟩:=c0v efN bak.proof A hz hd hv
  have hbound:=bDY A hz hfinite f hsup points (by simpa only [hJ] using hpoints)
  have hbodies : (fun i=>LK (A i)) =
      ![alT F,nD (tC (mW v)) 1,
        nD (LN (bf+1) (mW v)) (bf - 1),nD (RY v) bf] := by
    funext i
    fin_cases i
    · exact cWU F
    · exact bIk _ _ (F4 v).1 (F4 v).2
    · have h:=bfa v (bf+1) (by decide)
      exact bIk _ _ h.1 h.2
    · have h:=bfa v (bf+2) (by decide)
      exact bIk _ _ h.1 h.2
  simpa only [hJ,hmv,hbodies,T7] using (Nat.cast_le (α:=ℝ)).mpr hbound
end
end qeu0RUc
end
