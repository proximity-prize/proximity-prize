import ProximityPrize.SubmissionLower.V
import ProximityPrize.SubmissionLower.BI
set_option Elab.async false
open _root_ renaming Algebra→ oy,Algebra.TensorProduct.algebraMap_apply→yJ,Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap→vi,Algebra.TensorProduct.includeRight→yB,Algebra.TensorProduct.ringHom_ext→vw,Algebra.algebraMap→c9,CommRing→lV,Continuous→t6,DFunLike.congr_fun→yQ,ENNReal.ofReal→pU,Fin.castSucc→ oY,Fin.last→ oK,Fin.snoc_castSucc→v9,Fin.snoc_last→u8,Fin.sum_univ_four→yL,Finset.sum_eq_zero→xL,Finsupp.weight_eq_sum→vl,Function.Injective→u5,Function.Surjective→y5,HasDerivAt→uJ,Ideal→aU,Ideal.Quotient.lift→xm,Ideal.Quotient.mk→ ox,Ideal.Quotient.ringHom_ext→x7,Ideal.isCoprime_iff_sup_eq→wA,Ideal.map_le_iff_le_comap→yU,Ideal.mem_map_of_mem→vH,Ideal.mem_sup_left→wR,Ideal.mem_sup_right→u9,Ideal.span→qM,Ideal.span_singleton_le_iff_mem→t7,Ideal.span_singleton_one→wY,Ideal.subset_span→v8,IsClosed.measurableSet→uh,MeasurableSet→p9,MeasureTheory.MeasureSpace.volume→nq,Module.Finite→ oz,Module.finrank→n5,Module.finrank_zero_of_subsingleton→zd,MvPolynomial→lJ,MvPolynomial.X→nI,MvPolynomial.affineHilbertPolynomial→ ov,MvPolynomial.eval₂Hom_C→pz,MvPolynomial.eval₂Hom_X'→pL,MvPolynomial.map→ oq,MvPolynomial.ringHom_ext→qy,Nat.mul_le_mul_left→sH,Polynomial.C→p6
open _root_ renaming Polynomial.X→p7,Polynomial.aeval→t9,Polynomial.aeval_C→vZ,Polynomial.aeval_X→ze,RatFunc.C→lz,RatFunc.X→pQ,RatFunc.algebraMap_C→zf,RatFunc.algebraMap_X→xW,RatFunc.algebraMap_eq_C→vG,RingEquiv.symm_apply_apply→qU,RingHom.comap_ker→wB,RingHom.comp_apply→xu,RingHom.congr_fun→sS,RingHom.ext→t8,Set.indicator_of_mem→vk,Set.indicator_of_notMem→vj,Set.mem_ofPred_eq→zc,Submodule.factor_surjective→xI,WithBot→qx,aR.Shape→mD,acY.Compact.Chunk→lI,bzT.coefficients→qm,congrArg→p5,continuous_apply→ oj,continuous_const→pC,dN.GeoJets→nX,gT.Ambient→cy,hasDerivAt_id'→th,intervalIntegral.integral_eq_sub_of_hasDerivAt→uW,isClosed_le→ oZ,le_sup_left→uz,le_total→t4,map_add→ oD,map_mul→pG,map_one→qz,map_sub→qG,measurableSet_Icc→yo,min_eq_left→t3,min_eq_right→t5,min_le_left→yl,min_le_right→sI,ringKrullDim→qJ,smul_eq_mul→vh
set_option autoImplicit true
section
set_option maxHeartbeats 1200000
namespace axe
noncomputable section
open WI (Vp aPy a7c)
section Quotients
variable {k R:Type} [Field k] [lV R] [oy k R]
abbrev cut (I:aU R) (q:R) :aU R:=I ⊔ qM {q}
theorem dSW (I:aU R) (q:R) {m n:ℕ} (hle :m≤n) :
  cut I (q^n)≤ cut I (q^m) :=
 sup_le_sup_left
  ((t7 _).mpr
    (Ideal.mem_span_singleton.mpr (pow_dvd_pow q hle))) _
private theorem dSI (I:aU R) (q:R) (hI:I.IsPrime) (hq:q∉I) (n:ℕ) :
   (cut I (q^(n+1))).colon {q} = cut I (q^n) := by
 ext x
 rw [Submodule.mem_colon_singleton,vh]
 change x*q∈I ⊔ qM {q^(n+1)} ↔ x∈I ⊔ qM {q^n}
 constructor
 · intro hx
   obtain ⟨r,hr,s,hs,heq⟩:=Submodule.mem_sup.mp hx
   obtain ⟨y,rfl⟩:=Ideal.mem_span_singleton.mp hs
   have hprod: (x - q^n*y)*q∈I:= by
     rw [sub_mul,mul_right_comm (q^n) y q,← pow_succ,← heq,add_sub_cancel_right]
     exact hr
   exact Submodule.mem_sup.mpr ⟨x - q^n*y,(hI.mem_or_mem hprod).resolve_right hq,
     q^n*y,Ideal.mem_span_singleton.mpr ⟨y,rfl⟩,sub_add_cancel _ _⟩
 · intro hx
   obtain ⟨r,hr,s,hs,rfl⟩:=Submodule.mem_sup.mp hx
   obtain ⟨y,rfl⟩:=Ideal.mem_span_singleton.mp hs
   refine Submodule.mem_sup.mpr ⟨r*q,I.mul_mem_right _ hr,
     q^(n+1)*y,Ideal.mem_span_singleton.mpr ⟨y,rfl⟩,?_⟩
   rw [add_mul,pow_succ]
   ring
private theorem gxt (I:aU R) (q:R) (n:ℕ) :
   cut (cut I (q^(n+1))) q=cut I q:= by
 refine le_antisymm (sup_le ?_ le_sup_right) ?_
 · simpa only [pow_one] using dSW I q (m:=1) (Nat.succ_le_succ (Nat.zero_le n))
 · exact sup_le (le_sup_left.trans uz) le_sup_right
theorem ea9 (I:aU R) (q:R) (hI:I.IsPrime) (hq:q∉I)
   (hfinite : ∀ n:ℕ,oz k (R ⧸ cut I (q^n))) (n:ℕ) :
   n5 k (R ⧸ cut I (q^n))=n*n5 k (R ⧸ cut I q) := by
 induction n with
 | zero =>
   have htop:cut I (q^0) = ⊤ := by simp [wY]
   rw [htop,Nat.zero_mul]
   exact zd
 | succ n ih =>
   let J:=cut I (q^(n+1))
   let f :=(Vp J q).restrictScalars k
   let g:=(Submodule.factor (uz :J≤ cut J q)).restrictScalars k
   have hf :u5 f :=aPy J q
   have hg:y5 g :=
     xI (uz :J≤ cut J q)
   have hex :Function.Exact f g:=a7c J q
   have :oz k (R ⧸ J) :=hfinite (n+1)
   have h:=g.finrank_range_add_finrank_ker
   rw [LinearMap.range_eq_top.mpr hg,finrank_top,LinearMap.exact_iff.mp hex,
     LinearMap.finrank_range_of_inj hf] at h
   change n5 k (R ⧸ cut J q) +
     n5 k (R ⧸ J.colon {q})=n5 k (R ⧸ J) at h
   dsimp only [J] at h
   rw [gxt,dSI I q hI hq n,ih] at h
   rw [← h,Nat.succ_mul,Nat.add_comm]
theorem gwK {ι:Type*} [Fintype ι] (J:aU R)
  (I:ι→ aU R) (hle : ∀ i,J≤I i)
  (hcop:Pairwise (fun i j=>IsCoprime (I i) (I j))) [oz k (R ⧸ J)] :
  (∑ i,n5 k (R ⧸ I i))≤n5 k (R ⧸ J) := by
 let f (i:ι) : (R ⧸ J) →ₗ[k] (R ⧸ I i) :=
  (Submodule.factor (hle i)).restrictScalars k
 have hsurj:y5 (LinearMap.pi f) := by
  intro y
  obtain ⟨r,hr⟩:=Ideal.pi_quotient_surjective hcop y
  exact ⟨ox J r,funext hr⟩
 have (i:ι) :oz k (R ⧸ I i) :=
  Module.Finite.of_surjective (f i) (xI (hle i))
 rw [← Module.finrank_pi_fintype]
 exact LinearMap.finrank_le_finrank_of_surjective hsurj
end Quotients
end
end axe
end
section
set_option maxHeartbeats 1200000
namespace axe
noncomputable section
open aR dN BO GJ lB
open MvPolynomial
open scoped BigOperators
def c1 :Prop :=
  ∀ (J:aU nX) (h:mD),
    J.IsPrime→vE h →
    (ov (To J h)).natDegree ≤
      (ov J).natDegree - 1 ∧
    (To J h = ⊤ ∨
      (To J h).IsPrime∧(To J h).comap (aeg h)=J)
def c2 :Prop :=
  ∀ (k :Type) [Field k] (I:aU (lJ (Fin 4) k))
    (Q:lJ (Fin 4) k) (a :mD),
    I.IsPrime→(ov I).natDegree≤1 →
    vE a→Q∉I→bQW Q a →
    n5 k (lJ (Fin 4) k ⧸ (I ⊔ qM {Q})) ≤
      bHl I a
private theorem b68 {k R:Type*} [Field k]
   [lV R] [IsDomain R] {d:ℕ} [oy (lJ (Fin d) k) R]
   [FaithfulSMul (lJ (Fin d) k) R] [oz (lJ (Fin d) k) R] :
   qJ R=(d:qx ℕ∞) := by
 let B:=lJ (Fin d) k
 have hB:qJ B=(d:qx ℕ∞) := by
   rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,ringKrullDim_eq_zero_of_field]
   simp
 rw [← hB]
 apply le_antisymm
 · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (c9 B R))
   intro x y hxy
   exact Ideal.IsIntegral.under_lt_under (show x.asIdeal<y.asIdeal from hxy)
 · obtain ⟨b,hb,hd⟩:=Ideal.exists_isPrime_le_height (n:=d) hB.ge
   obtain ⟨z,hz⟩ :=
     Algebra.IsIntegral.comap_surjective B R (⟨b,hb⟩:PrimeSpectrum B)
   have hz' : z.asIdeal.under B=b:=p5 PrimeSpectrum.asIdeal hz
   have hle :=Ideal.height_under_le_height (R:=B) z.asIdeal
   rw [hz'] at hle
   calc
     qJ B=(d:qx ℕ∞) :=hB
     _≤(z.asIdeal.height:qx ℕ∞) :=WithBot.coe_le_coe.mpr (hd.trans hle)
     _≤ qJ R:=Ideal.height_le_ringKrullDim_of_isPrime
private theorem b67 {k R:Type*} [Field k] [lV R] [IsDomain R]
  {d:ℕ} (g:lJ (Fin d) k →+* R) (hg:u5 g)
  (hgfin:g.Finite) :qJ R=(d:qx ℕ∞) := by
 let algebra :=g.toAlgebra
 let:=algebra
 let faithful:FaithfulSMul (lJ (Fin d) k) R :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
 let finite :oz (lJ (Fin d) k) R:=hgfin
 exact @b68 k R _ _ _ d algebra faithful finite
private theorem dXa {k σ:Type*} [Field k] [Finite σ]
   (I:aU (lJ σ k)) [I.IsPrime] :
   qJ (lJ σ k ⧸ I) =
     ((ov I).natDegree :qx ℕ∞) := by
 obtain ⟨d,g,hg,hgfin⟩:=exists_finite_inj_algHom_of_fg k (lJ σ k ⧸ I)
 have hH :=natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hgfin hg
 rw [Nat.card_fin] at hH
 rw [hH]
 exact b67 g.toRingHom hg hgfin
private theorem bhn (h:mD) {J K:aU nX} (hle :J≤K) :
  To J h≤To K h :=
 sup_le_sup_right (Ideal.map_mono hle) _
private theorem gmu {P:nX} {a h:mD} (hfit :yy P a) :
  bQW ((aeg h P)^6) (a.scale 6) := by
 have hs :=support_map_of_injective P (c9 GeoField (dV h)).injective
 obtain ⟨hb,hj,ht⟩:=hfit
 change (aeg h P).support=P.support at hs
 have hb' : (aeg h P).totalDegree≤a.b:= by
  rwa [totalDegree,hs,← totalDegree]
 have hj' : (aeg h P).weightedTotalDegree Fin.val≤a.j:= by
  rwa [weightedTotalDegree,hs,← weightedTotalDegree]
 have ht' : (aeg h P).degreeOf 3≤a.t:= by
  rwa [degreeOf_eq_sup,hs,← degreeOf_eq_sup]
 exact ⟨(totalDegree_pow _ _).trans (sH 6 hb'),
  (weightedTotalDegree_pow_le _ _ _).trans (sH 6 hj'),
  (degreeOf_pow_le _ _ _).trans (sH 6 ht')⟩
private theorem gsh (hslice :c1) {aI:aU nX}
    {P:nX} (hs :aI.IsPrime) (hdim: (ov aI).natDegree=2)
    (hP:P∉aI) {h:mD} (hh:vE h) :
    Pairwise (fun C D: (cut aI P).minimalPrimesFinset =>
      IsCoprime (To C h) (To D h)) := by
  have :=hs
  have data (C: (cut aI P).minimalPrimesFinset) :
      To C h = ⊤ ∨ ((To C h).IsMaximal ∧
        (To C h).comap (aeg h)=(C:aU nX)) := by
    have hC:=Ideal.mem_minimalPrimesFinset.mp C.2
    have hd:=principalCut_natDegree_affineHilbertPolynomial_add_one hP hC
    rw [hdim] at hd
    have hdimC: (ov (C:aU nX)).natDegree=1 := by omega
    obtain ⟨hbound,hprime⟩:=hslice C h hC.isPrime hh
    have hf :oz (dV h) (adi h ⧸ To C h) :=
      natDegree_affineHilbertPolynomial_eq_zero_iff.mp (by omega)
    refine hprime.imp_right ?_
    rintro ⟨hp,hcomap⟩
    have :=hp
    have :=hf
    have hfield :=IsField.of_isDomain_of_finite (dV h)
      (adi h ⧸ To C h)
    exact ⟨Ideal.Quotient.maximal_of_isField _ hfield,hcomap⟩
  intro C D hCD
  obtain hC | ⟨hmC,hcC⟩:=data C
  · simp [wA,hC]
  obtain hD | ⟨hmD,hcD⟩:=data D
  · simp [wA,hD]
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply hmC.coprime_of_ne hmD
  intro heq
  exact hCD (Subtype.ext (hcC.symm.trans (heq ▸ hcD)))
private theorem gxc (hslice :c1) {aI:aU nX} {P:nX}
   (hs :aI.IsPrime) (hdim: (ov aI).natDegree=2)
   (hP:P∉aI) {h:mD} (hh:vE h)
   [oz (dV h) (adi h ⧸ cut (To aI h) (aeg h P))] :
   (∑ C∈(cut aI P).minimalPrimesFinset,pN C h) ≤
     n5 (dV h) (adi h ⧸ cut (To aI h) (aeg h P)) := by
 classical
 let T:=(cut aI P).minimalPrimesFinset
 have heq :To (cut aI P) h=cut (To aI h) (aeg h P) := by
   simp only [To,cut,Ideal.map_sup,Ideal.map_span,Set.image_singleton]
   exact sup_right_comm _ _ _
 have hle (C:T) :cut (To aI h) (aeg h P)≤To C h :=
   heq ▸ bhn h (Ideal.mem_minimalPrimesFinset.mp C.2).le
 dsimp only [pN]
 rw [← Finset.sum_coe_sort]
 exact gwK _ (fun C:T=>To C h) hle
   (gsh hslice hs hdim hP hh)
theorem of_children (h1 :c1) (h2 :c2) :GJ.c1 := by
  classical
  intro aI P a h hs hdim ha hh hP hfit
  let h' := h.scale 6
  let a' := a.scale 6
  let I:=To aI h'
  let q:=aeg h' P
  have full_scale6 (b:mD) (hb:vE b) :vE (b.scale 6) := by
    obtain ⟨⟨hb₁,hb₂⟩,hb₃⟩:=hb
    change (6*b.j≤6*b.b∧3*(6*b.t)≤6*b.j)∧0<6*b.t
    omega
  have :=hs
  have hd: (ov aI).natDegree=2 := by
    exact_mod_cast (dXa aI).symm.trans hdim
  obtain ⟨hdrop,hcase⟩:=h1 aI h' hs (full_scale6 h hh)
  have hIdeg: (ov I).natDegree≤1 := by
    simpa [I,hd] using hdrop
  obtain htop | ⟨hprime,hcontract⟩:=hcase
  · have hzero (C:aU nX) (hC:C∈(cut aI P).minimalPrimesFinset) :
        pN C h' = 0:= by
      have hle :aI≤C:=le_sup_left.trans (Ideal.mem_minimalPrimesFinset.mp hC).le
      have heq :To C h' = ⊤ :=
        top_le_iff.mp (htop.symm.trans_le (bhn h' hle))
      change n5 (dV h') (adi h' ⧸ To C h')=0
      rw [heq]
      exact zd
    change 6*(∑ C∈(cut aI P).minimalPrimesFinset,pN C h')≤_
    rw [xL hzero,mul_zero]
    exact Nat.zero_le _
  have hq:q∉I:= by
    intro hm
    apply hP
    rw [← hcontract]
    exact hm
  have hpow (n:ℕ) (hn:0<n) :q^n∉I :=
    fun hm=>hq ((hprime.pow_mem_iff_mem n hn).mp hm)
  have bqb (u:adi h') (hu:u∉I) :
      oz (dV h') (adi h' ⧸ cut I u) := by
    apply natDegree_affineHilbertPolynomial_eq_zero_iff.mp
    have hf : (ov (cut I u)).natDegree ≤
        (ov I).natDegree - 1 :=
      (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
        hprime hu le_rfl).1
    exact Nat.eq_zero_of_le_zero (hf.trans (Nat.sub_eq_zero_of_le hIdeg).le)
  have hfin (n:ℕ) :oz (dV h') (adi h' ⧸ cut I (q^n)) := by
    cases n with
    | zero =>
      apply natDegree_affineHilbertPolynomial_eq_zero_iff.mp
      simp [cut,wY ,affineHilbertPolynomial_top]
    | succ n=>exact bqb _ (hpow (n+1) (Nat.succ_pos n))
  have :=bqb q hq
  have hsum:=gxc h1 hs hd hP (full_scale6 h hh)
  change 6*(∑ C∈(cut aI P).minimalPrimesFinset,pN C h') ≤
    Ux aI a' h'
  calc
    _≤6*n5 (dV h') (adi h' ⧸ cut I q) :=
      sH 6 hsum
    _=n5 (dV h') (adi h' ⧸ cut I (q^6)) :=
      (ea9 I q hprime hq hfin 6).symm
    _≤bHl I a' :=
      h2 (dV h') I (q^6) a' hprime hIdeg (full_scale6 a ha)
        (hpow 6 (by decide)) (gmu hfit)
    _ = _:=efu aI a' h'
end
end axe
end
section
namespace bao
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
def shift {R τ:Type} [lV R] (c:τ→R) :
    lJ τ R →+* lJ τ R :=
  eval₂Hom C (fun i=>nI i+C (c i))
@[simp] theorem ddR {R τ:Type} [lV R] (c:τ→R) (a :R) :
   shift c (C a)=C a := by simp [shift]
@[simp] theorem gqb {R τ:Type} [lV R] (c:τ→R) (i:τ) :
   shift c (nI i)=nI i+C (c i) := by simp [shift]
theorem gqg {R τ:Type} [lV R] (c:τ→R) :
  u5 (shift c) := by
 have h: (shift (fun i => -c i)).comp (shift c)=RingHom.id _:= by
  apply qy
  · intro r
    simp
  · intro i
    simp [oD,add_assoc]
 have hinv :Function.LeftInverse (shift (fun i => -c i)) (shift c) :=
  fun p=>yQ h p
 exact hinv.injective
theorem gqh {R S τ:Type} [lV R] [lV S] (f :R →+* S)
  (c:τ→R) (p:lJ τ R) :
  shift (fun i=>f (c i)) (oq f p)=oq f (shift c p) := by
 have h: (shift (fun i=>f (c i))).comp (oq f) =
    (oq f).comp (shift c) := by
  apply qy <;> intro i <;> simp
 exact yQ h p
theorem bX4 {k R B ι τ:Type} [Field k] [lV R] [IsDomain R]
    [lV B] [oy k R] [oy k B] [Fintype ι]
    (q:R →ₐ[k] B) {Q:R} (hQ:Q≠0) (hq:q Q=0) {v :ι→R}
    (hv :LinearIndependent k (fun i=>q (v i))) (s :Finset τ) (w:τ→R)
    (a :ι→lJ τ k) (H :lJ τ R)
    (he : ∑ i,oq (c9 k R) (a i)*C (v i) =
      (C Q + ∑ j∈s,C (w j)*nI j)*H) :
    ∀ i,a i=0:= by
  classical
  have hvanish (d:τ →₀ ℕ) :H.coeff d=0 ∧ ∀ i,(a i).coeff d=0:= by
    induction d using (measure (fun d:τ →₀ ℕ=>d.degree)).wf.induction with
    | h d ih =>
      have hlower : (∑ j∈s,C (w j)*nI j*H).coeff d=0:= by
        rw [coeff_sum]
        apply xL
        intro j _
        rw [mul_assoc,coeff_C_mul,coeff_X_mul']
        split_ifs with hj
        · have hjle :Finsupp.single j 1≤d:= by
            rw [Finsupp.single_le_iff]
            exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
          have hd:=p5 Finsupp.degree (tsub_add_cancel_of_le hjle)
          rw [oD,Finsupp.degree_single] at hd
          rw [(ih (d-Finsupp.single j 1) (show (d-Finsupp.single j 1).degree<d.degree
            by omega)).1,mul_zero]
        · rw [mul_zero]
      have h:=p5 (fun p:lJ τ R=>p.coeff d) he
      rw [add_mul,Finset.sum_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hlower,add_zero,coeff_C_mul,coeff_sum] at h
      simp only [mul_comm (oq _ _) (C _),coeff_C_mul,coeff_map,
        mul_comm (v _) (c9 k R _)] at h
      have hh : ∑ i,(a i).coeff d•q (v i)=0:= by
        have h' := p5 q h
        simpa only [map_sum,pG,AlgHom.commutes,hq,zero_mul,
          Algebra.smul_def] using h'
      have ha :=Fintype.linearIndependent_iff.mp hv _ hh
      have hz :Q*H.coeff d=0:= by
        rw [← h]
        simp [ha]
      exact ⟨(mul_eq_zero.mp hz).resolve_left hQ,ha⟩
  exact fun i=>MvPolynomial.eq_zero_iff.mpr fun d=>(hvanish d).2 i
end
end bao
end
section
set_option maxHeartbeats 0
set_option maxRecDepth 50000
namespace acY
open acY.Compact
private def p44 :lI 3258 3 563176701 :=
 cert _ _ _ 0x3f1f05043e1e3d1d3c1c1b3b1a193a18031716391502141338120111000b0d5c2c062f070e0f64330836090a0c6d371c322fc040f60a790d2a2dfd5290f2c3e59dddf04648f93d2c71c526a2552a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c1011344663780c99b5dcf042edfd5290f46a867cb3bbbe08c91f27a58e96a283f9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a121418202268c48bf0103d829e434a8b4f54a60cb0a193e2657e08c91f27a58e96a293e (by decide +kernel) (by decide +kernel)
end acY
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace bzT
open cu gT pI OH aiM MvPolynomial
open scoped Polynomial RatFunc TensorProduct
noncomputable section
attribute [local instance] Polynomial.algebra
private abbrev e7:=RatFunc aQ
private abbrev agF:=RatFunc e7
private local instance (priority :=high) yZ (I:aU cy) :oy e7[X] (aaz I) :=
 (t9 (KT I) :_ →ₐ[e7] aaz I).toRingHom.toAlgebra
private local instance (priority :=high) jetModule (I:aU cy) :
   Module e7[X] (aaz I) :=
 (yZ I).toModule
private abbrev B6 (I:aU cy) :=
 letI:oy e7[X] (aaz I) :=yZ I
 agF ⊗[e7[X]] aaz I
private abbrev azD (I:aU cy) :aU PI :=
 I.map AU ⊔ qM {JN,Z6}
private def Yu (I:aU cy) :PI →+* Ik I :=
 ox (azD I)
private theorem eAI (I:aU cy) :Yu I JN=0 :=
 Ideal.Quotient.eq_zero_iff_mem.mpr
  (u9 (v8 (by simp)))
private theorem eAH (I:aU cy) :Yu I Z6=0 :=
 Ideal.Quotient.eq_zero_iff_mem.mpr
  (u9 (v8 (by simp)))
private abbrev aed (I:aU cy) :agF →+* Ik I :=
 (c9 dV (Ik I)).comp coefficients.toRingHom
private theorem glU (I:aU cy) (a :FX) :
   aed I (lz (lz (c9 FX aQ a))) =
     Yu I (C (c9 FX dV a)) := by
 change Yu I (C (qm (lz (lz (c9 FX aQ a)))))= _
 rw [cGI]
private theorem db9 (I:aU cy) (i:Fin 2) :
   aed I (lz (lz (ek i))) =
     Yu I (C (kz (![0,2] i))) := by
 change Yu I (C (qm (lz (lz (ek i)))))= _
 rw [cGK]
private theorem glW (I:aU cy) :
  aed I (lz pQ)=Yu I (C (kz 1)) := by
 change Yu I (C (qm (lz pQ)))= _
 rw [cGL]
private theorem glV (I:aU cy) :
  aed I pQ=Yu I (C (kz 3)) := by
 change Yu I (C (qm pQ))= _
 rw [cGJ]
private def aEN (I:aU cy) :N8 →+* Ik I :=
 eval₂Hom ((aed I).comp (RatFunc.C.comp lz)) (fun i=>Yu I (nI i))
private theorem gn7 (I:aU cy) :
   (aEN I).comp Q6=(Yu I).comp AU:= by
 apply qy
 · intro a
   simpa only [xu,Q6,AU,map_C,aEN,pz]
     using glU I a
 · intro i
   simp [aEN,Q6,AU]
private def bwe (I:aU cy) :rM I →+* Ik I :=
  xm (Cr I) (aEN I) <| by
    change Cr I≤RingHom.ker (aEN I)
    apply sup_le
    · rw [yU,wB,gn7]
      intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (wR (vH AU hp))
    · rw [t7,RingHom.mem_ker]
      simp only [B4,qG,oD,pG,aEN,pz ,pL]
      change Yu I (nI 0) +
        aed I (lz (lz (ek 0)))*Yu I (nI 1) -
        aed I (lz (lz (ek 1)))=0
      rw [db9 I 0,db9 I 1]
      change Yu I (nI 0)+Yu I (C (kz 0)) *
        Yu I (nI 1)-Yu I (C (kz 2))=0
      simpa only [JN,qG,oD,pG] using eAI I
private theorem bNF (I:aU cy) (p:N8) :
  bwe I (ox (Cr I) p)=aEN I p :=
 rfl
private def tensorLift {R A B T:Type} [lV R] [lV A] [lV B]
  [lV T] [oy R A] [oy R B]
  (f :A →+* T) (g:B →+* T)
  (h:f.comp (c9 R A)=g.comp (c9 R B)) :A ⊗[R] B →+* T:= by
 letI:oy R T:=(f.comp (c9 R A)).toAlgebra
 let f' : A →ₐ[R] T := { f with commutes' := fun _=>rfl }
 let g' : B →ₐ[R] T := { g with commutes' := fun r=>(sS h r).symm }
 exact (Algebra.TensorProduct.lift (S:=R) f' g' (fun _ _=>Commute.all _ _)).toRingHom
private theorem tensorLift_tmul {R A B T:Type} [lV R] [lV A] [lV B]
  [lV T] [oy R A] [oy R B]
  (f :A →+* T) (g:B →+* T) (h:f.comp (c9 R A)=g.comp (c9 R B))
  (a :A) (b:B) :tensorLift f g h (a ⊗ₜ[R] b)=f a*g b :=
 rfl
private def awy (I:aU cy) :aaz I →+* Ik I :=
 tensorLift ((aed I).comp lz) (bwe I) <| by
  apply t8
  intro a
  change aed I (lz (c9 aQ e7 a)) =
   bwe I (ox (Cr I) (C a))
  rw [bNF,aEN,pz ,vG]
  rfl
private theorem gsz (I:aU cy) :
  awy I (KT I)=aed I RatFunc.X:= by
 apply sub_eq_zero.mp
 simp only [aWL,oD,awy,tensorLift_tmul,qz ,one_mul,
  zL,bNF,aEN,pL]
 change Yu I (nI 2) +
  aed I (lz pQ)*Yu I (nI 3) -
  aed I pQ=0
 rw [glW,glV]
 simpa only [Z6,qG,oD,pG] using eAH I
private def akr (I:aU cy) :B6 I →+* Ik I :=
  tensorLift (R:=e7[X]) (aed I) (awy I) <| by
    apply Polynomial.ringHom_ext
    · intro a
      change aed I (c9 e7[X] agF (p6 a)) =
        awy I (t9 (KT I) (p6 a))
      rw [zf ,vZ,yJ]
      simp only [awy,tensorLift_tmul,qz ,mul_one]
      rfl
    · change aed I (c9 e7[X] agF p7) =
        awy I (t9 (KT I) p7)
      rw [xW,ze,gsz]
private abbrev acd (I:aU cy) :agF →+* B6 I :=
 c9 agF (B6 I)
private abbrev aNO (I:aU cy) :aaz I →+* B6 I :=
 Algebra.TensorProduct.includeRight.toRingHom
private abbrev bwD (I:aU cy) :rM I →+* aaz I :=
 Algebra.TensorProduct.includeRight.toRingHom
private abbrev It (I:aU cy) :rM I →+* B6 I :=
 (aNO I).comp (bwD I)
private theorem b22 (I:aU cy) (a :e7) :
   aNO I (c9 e7 (aaz I) a) =
     acd I (lz a) := by
 have h:acd I (c9 e7[X] agF (p6 a)) =
     aNO I (c9 e7[X] (aaz I) (p6 a)) :=
   sS (vi
     (R:=e7[X]) (A:=agF) (B:=aaz I)) (p6 a)
 rw [zf ,
   show c9 e7[X] (aaz I) (p6 a) =
     c9 e7 (aaz I) a from vZ _ _] at h
 exact h.symm
private theorem b21 (I:aU cy) (a :aQ) :
    It I (ox (Cr I) (C a)) =
      acd I (lz (lz a)) := by
  have h:=sS
    (vi (R:=aQ)
      (A:=e7) (B:=rM I)) a
  change aNO I (yB (c9 aQ (rM I) a))= _
  rw [← show Algebra.TensorProduct.includeLeftRingHom (c9 aQ e7 a) =
      (yB (B:=rM I) (A:=e7))
        (c9 aQ (rM I) a) from h]
  exact (b22 I _).trans (by rw [vG])
private theorem d99 (I:aU cy) :
   aNO I (KT I)=acd I RatFunc.X:= by
 have h:acd I (c9 e7[X] agF p7) =
     aNO I (c9 e7[X] (aaz I) p7) :=
   sS (vi
     (R:=e7[X]) (A:=agF) (B:=aaz I)) p7
 rw [xW,
   show c9 e7[X] (aaz I) p7 =
     KT I from ze _] at h
 exact h.symm
private abbrev bgZ (I:aU cy) :dV →+* B6 I :=
 (acd I).comp coefficients.symm.toRingHom
private def asg (I:aU cy) :PI →+* B6 I :=
 eval₂Hom (bgZ I) (fun i=>It I (zL I i))
private theorem db8 (I:aU cy) (i:Fin 2) :
   bgZ I (kz (![0,2] i)) =
     acd I (lz (lz (ek i))) := by
 change acd I (coefficients.symm (kz (![0,2] i)))= _
 rw [← cGK i,qU]
private theorem gnq (I:aU cy) :
    (asg I).comp AU=(It I).comp (asi I) := by
  apply qy
  · intro a
    change asg I (oq (c9 FX dV) (C a)) =
      It I (ox (Cr I) (oq (c9 FX aQ) (C a)))
    rw [map_C,map_C,asg,pz ,b21]
    change acd I (coefficients.symm (c9 FX dV a))= _
    rw [← cGI a,qU]
  · intro i
    change asg I (oq (c9 FX dV) (nI i)) =
      It I (ox (Cr I)
        (oq (c9 FX aQ) (nI i)))
    rw [map_X,map_X,asg,pL]
    rfl
private theorem gns (I:aU cy) :
  asg I JN=0:= by
 have h:ox (Cr I) (B4 0 1)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (u9 (Ideal.mem_span_singleton_self _))
 have h₀:bgZ I (kz 0)=acd I (lz (lz (ek 0))) :=
  db8 I 0
 have h₂:bgZ I (kz 2)=acd I (lz (lz (ek 1))) :=
  db8 I 1
 have h' := p5 (It I) h
 simp only [B4,oD,pG,qG,map_zero,b21] at h'
 simpa only [JN,asg,oD,pG,qG,pz ,
  pL,h₀,h₂,zL] using h'
private theorem gnr (I:aU cy) :
   asg I Z6=0:= by
 have h₁:bgZ I (kz 1)=acd I (lz pQ) := by
   change acd I (coefficients.symm (kz 1))= _
   rw [← cGL,qU]
 have h₃:bgZ I (kz 3)=acd I RatFunc.X:= by
   change acd I (coefficients.symm (kz 3))= _
   rw [← cGJ,qU]
 have h:=sub_eq_zero.mpr (d99 I)
 have hm:KT I=bwD I (zL I 2) +
     c9 e7 (aaz I) pQ*bwD I (zL I 3) := by
   simp [aWL,yJ]
 rw [hm,oD,pG,b22] at h
 simpa only [Z6,asg,oD,pG,qG,pz ,
   pL,h₁,h₃,It,xu] using h
private def aFe (I:aU cy) :Ik I →+* B6 I :=
  xm (azD I) (asg I) <| by
    change azD I≤RingHom.ker (asg I)
    apply sup_le
    · rw [yU,wB,gnq]
      intro p hp
      have hz :ox (Cr I) (Q6 p)=0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (wR (vH Q6 hp))
      change It I (asi I p)=0
      exact (p5 (It I) hz).trans (map_zero _)
    · rw [Ideal.span_insert,sup_le_iff]
      exact ⟨(t7 _).mpr (gns I),
        (t7 _).mpr (gnr I)⟩
private theorem ctE (I:aU cy) (a :agF) :
  akr I (acd I a)=aed I a := by
 change akr I (a ⊗ₜ[e7[X]] 1)= _
 simp only [akr,tensorLift_tmul,qz ,mul_one]
private theorem dhr (I:aU cy) (b:aaz I) :
  akr I (aNO I b)=awy I b:= by
 change akr I (1 ⊗ₜ[e7[X]] b)= _
 simp only [akr,tensorLift_tmul,qz ,one_mul]
private theorem gsB (I:aU cy) (b:rM I) :
  awy I (bwD I b)=bwe I b:= by
 change awy I (1 ⊗ₜ[aQ] b)= _
 simp only [awy,tensorLift_tmul,qz ,one_mul]
private theorem gsA (I:aU cy) (a :e7) :
  awy I (c9 e7 (aaz I) a)=aed I (lz a) := by
 change awy I (a ⊗ₜ[aQ] 1)= _
 simp only [awy,tensorLift_tmul,qz ,mul_one]
 rfl
private theorem dhq (I:aU cy) (b:rM I) :
  akr I (It I b)=bwe I b:= by
 change akr I (aNO I (bwD I b))= _
 rw [dhr,gsB]
private theorem dhp (I:aU cy) (i:Fin 4) :
  akr I (It I (zL I i))=Yu I (nI i) := by
 rw [dhq,zL,bNF,aEN,pL]
private theorem dhm (I:aU cy) (p:PI) :
  aFe I (Yu I p)=asg I p :=
 rfl
private theorem dhn (I:aU cy) (a :dV) :
  aFe I (c9 dV (Ik I) a)=acd I (coefficients.symm a) :=
 pz _ _ _
private theorem ctt (I:aU cy) (a :agF) :
  aFe I (aed I a)=acd I a := by
 change aFe I (c9 dV (Ik I) (qm a))= _
 rw [dhn,qU]
private def bp4 (I:aU cy) :B6 I ≃+* Ik I :=
  RingEquiv.ofRingHom (akr I) (aFe I)
    (by
      apply x7
      apply qy
      · intro a
        change akr I (aFe I (c9 dV (Ik I) a)) =
          c9 dV (Ik I) a
        rw [dhn,ctE]
        simp [aed]
      · intro i
        change akr I (aFe I (Yu I (nI i)))=Yu I (nI i)
        rw [dhm,asg,pL,dhp])
    (by
      apply vw
      · apply t8
        intro a
        change aFe I (akr I (acd I a))=acd I a
        rw [ctE,ctt]
      · apply vw
        · apply t8
          intro a
          change aFe I (akr I (aNO I (c9 e7 (aaz I) a)))= _
          rw [dhr,gsA,ctt]
          exact (b22 I a).symm
        · apply x7
          apply qy
          · intro a
            change aFe I (akr I (It I (ox (Cr I) (C a)))) =
              It I (ox (Cr I) (C a))
            rw [dhq,bNF,aEN,pz ,b21]
            exact ctt I _
          · intro i
            change aFe I (akr I (It I (zL I i)))=It I (zL I i)
            rw [dhp,dhm,asg,pL])
theorem proof :aiM.c3:= by
 intro I
 change n5 agF (B6 I)=n5 dV (Ik I)
 apply Algebra.finrank_eq_of_equiv_equiv qm (bp4 I)
 apply t8
 intro a
 change aed I a=akr I (acd I a)
 exact (ctE I a).symm
end
end bzT
end
section
namespace aFM
def avC:ℕ→ℕ
 | 0=>0
 | u+1=>Nat.succ (Nat.div (Nat.mul u (Nat.add (Nat.mul u (Nat.add (Nat.mul 2 u) 21)) 66)) 72)
def aM3 (d n:ℕ) :ℕ×ℕ :=
  let m:=Nat.min n (3*d+1)
  if m≤d+1 then (avC m,0) else
    let a :=m - d
    let jO:=avC (a - 1)+avC (a - 2)+avC (a-3)
    if m≤2*d+3 then (avC m,jO) else
      let b:=m - 2*d
      (avC m+avC (b-3)+avC (b-4)+avC (b - 5),jO)
end aFM
end
section
namespace YV
noncomputable section
open aR dN lB MeasureTheory MvPolynomial
open scoped Pointwise
abbrev M5:=Fin 4→ℝ
def cap (p:mD) :Set M5 :=
  {x | (∀ i,0≤x i)∧x 0 + x 1 + x 2 + x 3≤p.b ∧
    x 1+2*x 2 + 3*x 3≤p.j∧x 3≤p.t}
def bbu (f :nX) (P:Set M5) :Prop :=
 ∀ e∈f.support,(fun i=>(e i:ℝ))∈P
theorem bxf {f :nX} {p:mD} (hf :yy f p) :
   bbu f (cap p) := by
 intro e he
 have htotal:=(le_weightedTotalDegree (1 :Fin 4→ℕ) he).trans
   (show f.weightedTotalDegree 1≤p.b by simpa only [weightedTotalDegree_one] using hf.1)
 have hindex :=(le_weightedTotalDegree (Fin.val :Fin 4→ℕ) he).trans hf.2.1
 have htop:=degreeOf_le_iff.mp hf.2.2 e he
 simp only [vl,vh,Pi.one_apply,mul_one,
   yL] at htotal
 simp only [vl,vh,yL] at hindex
 have hj:e 1+2*e 2 + 3*e 3≤p.j:= by
   change e 0*0+e 1*1+e 2*2+e 3*3≤p.j at hindex
   omega
 refine ⟨fun i=>Nat.cast_nonneg _,?_,?_,?_⟩
 · change (e 0:ℝ)+e 1+e 2+e 3≤(p.b:ℝ)
   exact_mod_cast htotal
 · change (e 1 :ℝ)+2*e 2 + 3*e 3≤(p.j:ℝ)
   exact_mod_cast hj
 · change (e 3:ℝ)≤(p.t:ℝ)
   exact_mod_cast htop
def ahk (F:Set M5→ℝ) (a x :Set M5) :ℝ :=
 F (x+a)-F x
def avz (p q r s :Set M5) :ℝ :=
  ahk (ahk (ahk (ahk
    (fun P=>(nq P).toReal) p) q) r) s 0
end
end YV
end
section
namespace YV
open aR lB
open scoped Pointwise
theorem Nc {p q:mD} (hp:bF p) (hq:bF q) :
  bF (p.plus q) := by
 obtain ⟨hpb,hpj⟩:=hp
 obtain ⟨hqb,hqj⟩:=hq
 constructor <;> dsimp [Shape.plus] <;> omega
theorem auw:cap ⟨0,0,0⟩=0:= by
 change cap ⟨0,0,0⟩ = {(0:M5)}
 ext x
 constructor
 · intro hx
   obtain ⟨h,hb,_,_⟩:=hx
   norm_num at hb
   apply Set.mem_singleton_iff.mpr
   funext i
   have h0:=h 0
   have h1 :=h 1
   have h2 :=h 2
   have h3:=h 3
   change x i=0
   fin_cases i
   · change x 0=0
     linarith
   · change x 1=0
     linarith
   · change x 2=0
     linarith
   · change x 3=0
     linarith
 · rintro rfl
   simp [cap]
private theorem guj {x y A B:ℝ} (hx :0≤x) (hy :0≤y)
   (hA:0≤A) (hB:0≤B) (hs :x+2*y≤A+B) :
   ∃ u v :ℝ,0≤u∧u≤x∧0≤v∧v≤y ∧
     u+2*v≤A∧(x - u)+2*(y - v)≤B:= by
 let u:=min x A
 let v :=min y ((A - u)/2)
 have huA:u≤A:=sI _ _
 have hvA:v≤(A - u)/2 :=sI _ _
 refine ⟨u,v,le_min hx hA,min_le_left _ _,le_min hy (by linarith),
   yl  _ _,by linarith,?_⟩
 rcases t4 y ((A - u)/2) with h | h
 · have hve :v=y :=t3 h
   rcases t4 x A with h | h
   · have hue :u=x :=t3 h
     rw [hue,hve]
     linarith
   · have hue :u=A:=t5 h
     rw [hue,hve]
     linarith
 · have hve :v=(A - u)/2 :=t5 h
   rw [hve]
   linarith
private theorem dFa {p q:mD} (hp:bF p) (hq:bF q)
   {x :M5} (hx :x∈cap (p.plus q)) :x∈cap p+cap q:= by
 have hpb' : (p.j:ℝ)≤p.b:= by exact_mod_cast hp.1
 have hqb' : (q.j:ℝ)≤q.b:= by exact_mod_cast hq.1
 obtain ⟨hx,hb,hj,ht⟩:=hx
 simp only [Shape.plus,Nat.cast_add] at hb hj ht
 let z :=min (x 3) (p.t:ℝ)
 have hz0:0≤z :=le_min (hx 3) (by positivity)
 have hzx :z≤x 3:=yl _ _
 have hzp:z≤(p.t:ℝ) :=sI _ _
 have hzq:x 3 - z≤(q.t:ℝ) := by
   rcases t4 (x 3) (p.t:ℝ) with hh | hh
   · dsimp only [z]
     rw [t3 hh,sub_self]
     positivity
   · dsimp only [z]
     rw [t5 hh]
     linarith
 have hpz : (3:ℝ)*p.t≤p.j:= by exact_mod_cast hp.2
 have hqz : (3:ℝ)*q.t≤q.j:= by exact_mod_cast hq.2
 obtain ⟨u,v,hu0,hux,hv0,hvx,huvp,huvq⟩ :=
   guj (x :=x 1) (y :=x 2) (A:=(p.j:ℝ)-3*z)
     (B:=(q.j:ℝ)-3*(x 3 - z)) (hx 1) (hx 2) (by linarith)
     (by linarith) (by linarith)
 let a :=min (x 0) ((p.b:ℝ) - u - v - z)
 have ha0:0≤a :=le_min (hx 0) (by linarith)
 have hax :a≤x 0:=yl _ _
 have hap:a≤(p.b:ℝ) - u - v - z :=sI _ _
 have haq: (x 0-a)+(x 1 - u)+(x 2 - v)+(x 3 - z)≤(q.b:ℝ) := by
   rcases t4 (x 0) ((p.b:ℝ) - u - v - z) with hh | hh
   · dsimp only [a]
     rw [t3 hh]
     linarith
   · dsimp only [a]
     rw [t5 hh]
     linarith
 let y :M5 := ![a,u,v,z]
 have hy :y∈cap p:= by
   refine ⟨?_,?_,?_,?_⟩
   · intro i
     fin_cases i <;> assumption
   · change a+u+v+z≤(p.b:ℝ)
     linarith
   · change u+2*v+3*z≤(p.j:ℝ)
     linarith
   · exact hzp
 have hxy :x - y∈cap q:= by
   refine ⟨?_,haq,?_,hzq⟩
   · intro i
     fin_cases i <;> exact sub_nonneg.mpr (by assumption)
   · change (x 1 - u)+2*(x 2 - v)+3*(x 3 - z)≤(q.j:ℝ)
     linarith
 exact Set.mem_add.mpr ⟨y,hy,x - y,hxy,by abel⟩
theorem anN {p q:mD} (hp:bF p) (hq:bF q) :
  cap (p.plus q)=cap p+cap q:= by
 apply Set.Subset.antisymm (fun _ hx=>dFa hp hq hx)
 intro x hx
 obtain ⟨y,⟨hy,hyb,hyj,hyt⟩,z,⟨hz,hzb,hzj,hzt⟩,rfl⟩:=Set.mem_add.mp hx
 refine ⟨fun i=>add_nonneg (hy i) (hz i),?_,?_,?_⟩ <;>
  simp only [Pi.add_apply,Shape.plus,Nat.cast_add] <;> linarith
end YV
end
section
namespace ap7
open aR lB YV MeasureTheory Set
open scoped ENNReal Pointwise
private abbrev J7 {n:ℕ} (y :Fin n→ℝ) (x :ℝ) :Fin (n+1)→ℝ :=
 Fin.snoc y x
private theorem gLn {n:ℕ} {S:Set (Fin (n+1)→ℝ)}
   (hS:p9 S) :
   nq S = ∫⁻ x :ℝ,nq {y :Fin n→ℝ | J7 y x∈S} := by
 let e :=MeasurableEquiv.piFinSuccAbove (fun _:Fin (n+1)=>ℝ) (oK n)
 have he :MeasurePreserving e nq
     ((nq :Measure ℝ).prod (nq :Measure (Fin n→ℝ))) :=
   volume_preserving_piFinSuccAbove _ _
 have hE :p9 (e '' S) :=e.measurableSet_image.mpr hS
 have hpre :e ⁻¹' (e '' S)=S:=Set.preimage_image_eq _ e.injective
 calc
   nq S=((nq :Measure ℝ).prod (nq :Measure (Fin n→ℝ))) (e '' S) :=
     (p5 nq hpre.symm).trans (he.measure_preimage hE.nullMeasurableSet)
   _ = _:= by
     rw [Measure.prod_apply hE]
     congr 1
     funext x
     congr 1
     ext y
     change (x,y)∈e '' S↔J7 y x∈S
     rw [e.image_eq_preimage_symm]
     change e.symm (x,y)∈S↔_
     change Fin.insertNth (oK n) x y∈S↔_
     rw [Fin.insertNth_last']
private theorem cvl {n:ℕ} {S:Set (Fin (n+1)→ℝ)}
   (hS:p9 S) {u:ℝ} (hu:0≤u) {f :ℝ→ℝ} (hf :t6 f)
   (hnn : ∀ x∈Icc 0 u,0≤f x)
   (hs : ∀ x,nq {y :Fin n→ℝ | J7 y x∈S} =
     (Icc 0 u).indicator (fun x=>pU (f x)) x) :
   nq S=pU (∫ x in (0:ℝ)..u,f x) := by
 rw [gLn hS]
 simp_rw [hs]
 rw [lintegral_indicator yo ,intervalIntegral.integral_of_le hu,
   ← integral_Icc_eq_integral_Ioc]
 have hi:Integrable f (volume.restrict (Icc 0 u)) :=
   hf.continuousOn.integrableOn_compact isCompact_Icc
 have hn:0 ≤ᵐ[volume.restrict (Icc 0 u)] f :=
   (ae_restrict_iff' yo).2 (Filter.Eventually.of_forall hnn)
 exact (ofReal_integral_eq_lintegral_ofReal hi hn).symm
private def aMA (B J:ℝ) :Set (Fin 2→ℝ) :=
 {y | 0≤y 0∧y 1∈Icc 0 J∧y 0+y 1≤B}
private def aGU (B J:ℝ) :Set (Fin 3→ℝ) :=
 {y | (∀ i,0≤y i)∧y 0+y 1+y 2≤B∧y 1+2*y 2≤J}
private theorem isClosed_nonneg {n:ℕ} : IsClosed {y :Fin n→ℝ | ∀ i,0≤y i} := by
 rw [Set.ofPred_forall]
 exact isClosed_iInter fun i=>oZ pC (oj i)
private theorem c1D {n:ℕ} (y :Fin n→ℝ) (s :ℝ) :
   (∀ i,0≤J7 y s i)↔(∀ i,0≤y i)∧0≤ s := by
 unfold J7
 constructor
 · intro h
   exact ⟨fun i=> by simpa only [Fin.snoc_castSucc] using h i.castSucc,
     by simpa only [u8 ] using h (oK  n)⟩
 · rintro ⟨hy,hs⟩ i
   induction i using Fin.lastCases with
   | last=>simpa only [Fin.snoc_last] using hs
   | cast i=>simpa only [Fin.snoc_castSucc] using hy i
private theorem gLh {B J:ℝ} (hJ:0≤J) (hB:J≤B) :
    nq (aMA B J)=pU (J*(B-J/2)) := by
  have hm:p9 (aMA B J) := by
    apply uh
    exact (oZ pC (oj 0)).inter
      ((isClosed_Icc.preimage (oj 1)).inter
        (oZ ((oj 0).add (oj 1)) pC))
  have hs (x :ℝ) :
      nq {y :Fin 1→ℝ | J7 y x∈aMA B J} =
        (Icc 0 J).indicator (fun x=>pU (B - x)) x := by
    have he (y :Fin 1→ℝ) :
        J7 y x∈aMA B J↔0≤y 0∧x∈Icc 0 J∧y 0 + x≤B:= by
      change 0≤J7 y x 0∧J7 y x (oK 1)∈Icc 0 J ∧
        J7 y x 0+J7 y x (oK 1)≤B↔_
      simp only [J7,Fin.snoc_apply_zero,u8]
    by_cases hx :x∈Icc 0 J
    · have hset : {y :Fin 1→ℝ | J7 y x∈aMA B J} =
          Icc (fun _=>0) (fun _=>B - x) := by
        ext y
        rw [zc,he]
        have hzero (i:Fin 1) :i=0:=Subsingleton.elim _ _
        change (0≤y 0∧x∈Icc 0 J∧y 0 + x≤B)↔(0≤y∧y≤fun _=>B - x)
        simp only [Pi.le_def,Pi.zero_apply,hzero,forall_const,hx,true_and]
        exact and_congr_right fun _=>le_sub_iff_add_le.symm
      rw [hset,Real.volume_Icc_pi,vk hx]
      simp
    · have hset : {y :Fin 1→ℝ | J7 y x∈aMA B J} = ∅ := by
        ext y
        simp [he,hx]
      rw [hset,measure_empty,vj hx]
  rw [cvl hm hJ (by fun_prop) (fun x hx=>sub_nonneg.mpr (hx.2.trans hB)) hs]
  congr 1
  have hd (x :ℝ) :uJ (fun x :ℝ=>B*x - x^2/2) (B - x) x := by
    convert ((th x).const_mul B).sub (((th x).pow 2).div_const 2)
      using 1
    simp
  rw [uW (fun x _=>hd x)
    ((show t6 (fun x :ℝ=>B - x) by fun_prop).intervalIntegrable _ _)]
  ring
private theorem gLi {B J:ℝ} (hJ:0≤J) (hB:J≤B) :
    nq (aGU B J)=pU (J^2*(2*B-J)/8) := by
  have hm:p9 (aGU B J) := by
    apply uh
    exact isClosed_nonneg.inter
      ((oZ (((oj 0).add (oj 1)).add (oj 2))
        pC).inter
        (oZ (f := fun y :Fin 3→ℝ=>y 1+2*y 2)
          (by fun_prop) pC))
  have hs (r :ℝ) :
      nq {y :Fin 2→ℝ | J7 y r∈aGU B J} =
        (Icc 0 (J/2)).indicator
          (fun r=>pU ((J - 2*r)*(B-J/2))) r := by
    have he (y :Fin 2→ℝ) :
        J7 y r∈aGU B J ↔
          (0≤y 0∧0≤y 1∧0≤ r)∧y 0+y 1+r≤B∧y 1+2*r≤J:= by
      have hc: (∀ i,0≤J7 y r i)↔(0≤y 0∧0≤y 1∧0≤ r) := by
        rw [c1D,Fin.forall_fin_two,and_assoc]
      change (∀ i,0≤J7 y r i) ∧
        J7 y r (oY 0)+J7 y r (oY 1) +
          J7 y r (oK 2)≤B ∧
        J7 y r (oY 1)+2*J7 y r (oK 2)≤J↔_
      rw [hc]
      simp only [J7,v9,u8]
    by_cases hr :r∈Icc 0 (J/2)
    · have hset : {y :Fin 2→ℝ | J7 y r∈aGU B J} = aMA (B - r) (J - 2*r) := by
        ext y
        rw [zc,he]
        change _↔0≤y 0∧(0≤y 1∧y 1≤J - 2*r)∧y 0+y 1≤B - r
        have hnr :=hr.1
        constructor
        · rintro ⟨⟨h0,h1,_⟩,h2,h3⟩
          exact ⟨h0,⟨h1,by linarith⟩,by linarith⟩
        · rintro ⟨h0,⟨h1,h2⟩,h3⟩
          exact ⟨⟨h0,h1,hnr⟩,by linarith,by linarith⟩
      have hnr :=hr.1
      have hru:=hr.2
      rw [hset,vk hr,gLh (by linarith) (by linarith)]
      congr 1
      ring
    · have hset : {y :Fin 2→ℝ | J7 y r∈aGU B J} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨⟨_,h1,h2⟩,_,h3⟩:=(he y).mp hy
        exact hr ⟨h2,by linarith⟩
      rw [hset,measure_empty,vj hr]
  have hn (r :ℝ) (hr :r∈Icc 0 (J/2)) :0≤(J - 2*r)*(B-J/2) := by
    have hru:=hr.2
    exact mul_nonneg (by linarith) (by linarith)
  rw [cvl hm (by linarith) (by fun_prop) hn hs]
  congr 1
  have hd (r :ℝ) :
      uJ (fun r :ℝ => -(B-J/2)*(J - 2*r)^2/4)
        ((J - 2*r)*(B-J/2)) r := by
    have hl:=((th r).const_mul 2).const_sub J
    convert ((hl.pow 2).const_mul (-(B-J/2))).div_const 4
      using 1
    simp
    ring
  rw [uW (fun r _=>hd r)
    ((show t6 (fun r :ℝ=>(J - 2*r)*(B-J/2)) by fun_prop).intervalIntegrable _ _)]
  ring
theorem bWq (p:mD) (hp:bF p) :
    32*(nq (cap p)).toReal=(Dn p:ℝ) := by
  let b:ℝ:=p.b
  let j:ℝ:=p.j
  let t:ℝ:=p.t
  have hbj:j≤b:= by
    dsimp [j,b]
    exact_mod_cast hp.1
  have hjt:3*t≤j:= by
    dsimp [t,j]
    exact_mod_cast hp.2
  have ht:0≤t:= by positivity
  have hm:p9 (cap p) := by
    apply uh
    exact isClosed_nonneg.inter
      ((oZ ((((oj 0).add (oj 1)).add (oj 2)).add
        (oj 3)) pC).inter
        ((oZ (f := fun y :Fin 4→ℝ=>y 1+2*y 2 + 3*y 3)
          (by fun_prop) pC).inter
          (oZ (oj 3) pC)))
  have hs (s :ℝ) :
      nq {y :Fin 3→ℝ | J7 y s∈cap p} =
        (Icc 0 t).indicator
          (fun s=>pU ((j-3*s)^2*(2*b - j+s)/8)) s := by
    have he (y :Fin 3→ℝ) :
        J7 y s∈cap p↔s∈Icc 0 t∧y∈aGU (b - s) (j-3*s) := by
      change (∀ i,0≤J7 y s i) ∧
        J7 y s (oY 0)+J7 y s (oY 1) +
          J7 y s (oY 2)+J7 y s (oK 3)≤b ∧
        J7 y s (oY 1)+2*J7 y s (oY 2) +
          3*J7 y s (oK 3)≤j∧J7 y s (oK 3)≤t ↔
        (0≤ s∧s≤t)∧(∀ i,0≤y i)∧y 0+y 1+y 2≤b - s∧y 1+2*y 2≤j-3*s
      rw [c1D]
      simp only [J7,v9,u8 ,le_sub_iff_add_le]
      tauto
    by_cases hsi:s∈Icc 0 t
    · have hss :=hsi.1
      have hst:=hsi.2
      have hset : {y :Fin 3→ℝ | J7 y s∈cap p} = aGU (b - s) (j-3*s) := by
        ext y
        simp [he,hsi]
      rw [hset,vk hsi,gLi (by linarith) (by linarith)]
      congr 1
      ring
    · have hset : {y :Fin 3→ℝ | J7 y s∈cap p} = ∅ := by
        ext y
        simp [he,hsi]
      rw [hset,measure_empty,vj hsi]
  have hn (s :ℝ) (hsi:s∈Icc 0 t) :0≤(j-3*s)^2*(2*b - j+s)/8:= by
    have hss :=hsi.1
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by norm_num)
  rw [cvl hm ht (by fun_prop) hn hs]
  let A:ℝ→ℝ:= fun s =>
    -(2*b - 2*j/3)*(j-3*s)^3/72+(j-3*s)^4/288
  have hd (s :ℝ) :uJ A ((j-3*s)^2*(2*b - j+s)/8) s := by
    have hl:=((th s).const_mul 3).const_sub j
    dsimp [A]
    convert (((hl.pow 3).const_mul (-(2*b - 2*j/3))).div_const 72).add
      ((hl.pow 4).div_const 288) using 1
    simp
    ring
  have hnn:0 ≤ ∫ s in (0:ℝ)..t,(j-3*s)^2*(2*b - j+s)/8 :=
    intervalIntegral.integral_nonneg ht hn
  rw [ENNReal.toReal_ofReal hnn,uW (fun s _=>hd s)
    ((show t6 (fun s :ℝ=>(j-3*s)^2*(2*b - j+s)/8)
      by fun_prop).intervalIntegrable _ _)]
  simp only [A,b,j,t,Dn,Int.cast_natCast,Int.cast_add,Int.cast_sub,
    Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  ring
end ap7
end
section
namespace ap7
noncomputable section
open aR dN BO GJ YV
abbrev ae9 (a h:mD) :=lJ (Fin 4) (VM a h)
abbrev EG (a h:mD) :nX →+* ae9 a h :=
 oq (c9 GeoField (VM a h))
abbrev a4d (a h:mD) :ae9 a h :=
 Uq a (Sum.inl:uL a→aav a h)
abbrev a8j (a h:mD) :ae9 a h :=
 Uq h (Sum.inr :uL h→aav a h)
abbrev axZ (J:aU nX) (a h:mD) :=
 ae9 a h ⧸ (J.map (EG a h) ⊔ qM {a4d a h,a8j a h})
def aJ9 {k :Type*} [CommSemiring k] (F:lJ (Fin 4) k) (p:mD) :Prop :=
 ∀ e∈F.support,(fun i=>(e i:ℝ))∈cap p
end
end ap7
end
