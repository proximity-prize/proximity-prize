import ProximityPrize.SubmissionLower.ZFZJbJc
set_option Elab.async false
open _root_ renaming Finsupp.optionElim_some → zX5, Finsupp.weight_apply → zDM, Finsupp.weight_optionElim → zVB, Int.toNat_le_toNat → z0Z, MvPolynomial.optionEquivRight → zyD, Nat.add_le_add_left → z3b, Nat.mul_comm → z5A
section
set_option autoImplicit true
namespace P6_6
noncomputable section
open P6 (K)
open aR (ao extend af shape aO cK jet Dd)
open Ex (X7 bUb bA3 C6 a3E
  bUq)
open scoped BigOperators Polynomial
open private bcz cBi aDq from ProximityPrize.SubmissionLower.BF
private theorem aio {n D:ℕ} (P:af n) :
    tB P D ↔
      ((zyD ao (Fin n)).symm P).weightedTotalDegree
        (fun v=>v.elim 1 (fun i=>gZ - i.val))≤D:= by
  classical
  rw [MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc: (P.coeff u.some).coeff (u none)≠0:= by
      rw [← bcz,zX5]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm:u.some∈P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz=>hc (by simp [hz]))
    have hi:=Polynomial.le_natDegree_of_ne_zero hc
    rw [← zX5 u,zVB,one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [zDM,smul_eq_mul,z5A] using h _ hm
  · intro h m hm
    let d:=(P.coeff m).natDegree
    have hc: (P.coeff m).coeff d≠0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu:m.optionElim d∈((zyD ao (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [bcz])
    have hb:=h _ hu
    rw [zVB,one_mul] at hb
    simpa only [zDM,smul_eq_mul,z5A] using hb
open MvPolynomial UniqueFactorizationMonoid
open private b7n from ProximityPrize.SubmissionLower.B7
private theorem eyH (P:af 4) (hP:P≠0) (hbox :aO (shape P) m6)
    (hw:tB P M8) (j:ℕ) (hj:j≤(shape P).t) :
    axx j (X7 P) := by
  refine ⟨bUb hP,?_,?_,?_⟩
  · have h:=b7n P (1 :Fin 4→ℕ)
    change (X7 P).weightedTotalDegree 1+1*(shape P).t≤P.weightedTotalDegree 1 at h
    rw [weightedTotalDegree_one,one_mul,weightedTotalDegree_one] at h
    exact (z3b hj _).trans (h.trans hbox.1)
  · have h:=b7n P (fun i=>i.val)
    change (X7 P).weightedTotalDegree (fun i=>i.val)+3*(shape P).t ≤
      P.weightedTotalDegree (fun i=>i.val) at h
    rw [← C6,← C6] at h
    exact (z3b (Nat.mul_le_mul_left 3 hj) _).trans (h.trans hbox.2.1)
  · intro m hm
    obtain ⟨u,hu,hc,h⟩:=cBi P m hm
    have hle :=h (fun i=>gZ - i.val)
    rw [← hc]
    apply (z3b _ _).trans (hw u hu)
    simpa only [zDM,smul_eq_mul,z5A,Fin.val_castSucc] using hle
private theorem d50 {P f :af 4} (hP:P≠0)
    (hbox :aO (shape P) m6) (hw:tB P M8)
    (hf :Irreducible f) (ht:0<(shape f).t) (hd:f∣P) :wm f := by
  refine ⟨hf,ht,⟨?_,?_,?_⟩,?_⟩
  · have h:=weightedTotalDegree_le_of_dvd (1 :Fin 4→ℕ) hd hP
    rw [weightedTotalDegree_one,weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h:=weightedTotalDegree_le_of_dvd (fun i=>i.val) hd hP
    rw [← C6,← C6] at h
    exact h.trans hbox.2.1
  · have h:=weightedTotalDegree_le_of_dvd (Pi.single (3:Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e :=zyD ao (Fin 4)
    have hd' : e.symm f∣e.symm P:= _root_.map_dvd e.symm hd
    have hP' : e.symm P≠0:= fun h=>hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (aio f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((aio P).mp hw))
theorem dRc {Γ:Finset K} {s :K→K[X]} (P:af 4)
    (hP:P≠0) (hbox :aO (shape P) m6)
    (hw:tB P M8)
    (hz : ∀ γ∈Γ,cK P (extend (s γ))=0) :
    ∃ (n:ℕ) (g:af 3) (f :Fin n→af 4),Cover Γ s g f := by
  classical
  let _:StrongNormalizationMonoid (af 4) :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let A:=normalizedFactors P
  let T:=A.toFinset.filter fun q=>0<(shape q).t
  let n:=Fintype.card ↥T
  let e :Fin n ≃ ↥T:=(Fintype.equivFin ↥T).symm
  let f :Fin n→af 4 := fun i=>(e i).val
  have hT : ∀ q∈T,q∈A∧0<(shape q).t:= by
    intro q hq
    simpa [T] using hq
  have hfi (i:Fin n) :f i∈A∧0<(shape (f i)).t:=hT _ (e i).property
  have hd: (∏ i,f i)∣P:= by
    have heq : (∏ i,f i) = ∏ q∈T,q:= by
      rw [show (∏ i,f i) = ∏ q : ↥T,q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  have hs (w:Fin 4→ℕ) :=sum_weightedTotalDegree_le_of_prod_dvd w Finset.univ f hP hd
  have htop:=hs (Pi.single (3:Fin 4) 1)
  simp only [weightedTotalDegree_piSingle] at htop
  refine ⟨n,X7 P,f,⟨eyH P hP hbox hw _ htop,?_,?_,
    fun i=>⟨(hfi i).2,aDq (f i)⟩,?_,?_,?_⟩⟩
  · intro i
    exact d50 hP hbox hw (irreducible_of_normalized_factor _ (hfi i).1)
      (hfi i).2 (dvd_of_mem_normalizedFactors (hfi i).1)
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · have hb:=hs (1 :Fin 4→ℕ)
    simp only [weightedTotalDegree_one] at hb
    have hj:=hs (fun i=>i.val)
    simp only [← C6] at hj
    exact ⟨hb.trans hbox.1,hj.trans hbox.2.1,htop.trans hbox.2.2⟩
  · intro γ hγ
    let S:=extend (s γ)
    by_cases hg:cK (X7 P) S=0
    · exact Or.inl hg
    right
    have hSA:eval (jet S) A.prod=0:= by
      have hdiv := _root_.map_dvd (eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change cK P S∣eval (jet S) A.prod at hdiv
      rw [hz γ hγ,zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hSA
    obtain ⟨q,hq,hqS⟩:=hSA
    have hqlead:cK (X7 q) S≠0:= by
      intro hzero
      obtain ⟨R,hR⟩:=dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR,bA3,cK,map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt:0<(shape q).t:= by
      by_contra! h
      apply hqlead
      rw [← bUq q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT:q∈T:=Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq,hqt⟩
    let j:=e.symm ⟨q,hqT⟩
    have hj:f j=q:=congrArg Subtype.val (e.apply_symm_apply ⟨q,hqT⟩)
    exact ⟨j,by rw [hj,Dd,← a3E]; exact ⟨hqS,hqlead⟩⟩
  · intro γ _ hg i
    rw [← a3E]
    intro hzero
    obtain ⟨R,hR⟩:=dvd_of_mem_normalizedFactors (hfi i).1
    apply hg
    rw [hR,bA3,cK,map_mul]
    exact mul_eq_zero_of_left hzero _
end
end P6_6
end
section
set_option autoImplicit true
namespace P6_6
noncomputable section
open Polynomial
open P6 (K k node jG mJ)
open aR (embed extend jF)
open scoped BigOperators
theorem bZ7 {u D Γ} (M:jG u D) (F:mJ M Γ)
    (γ:K) (hγ:γ∈Γ) : (F.scalar γ).natDegree≤k - 1+M.iF.toNat := by
  rcases (F.mark γ hγ).aic with h | h
  · simp [h]
  · change (F.scalar γ).natDegree≤k - 1+(P1.FJ.iF M).toNat
    omega
theorem eAk {u D Γ} (M:jG u D) (F:mJ M Γ)
    (hw:M.iF≤P6.ajO) :Messages M.word Γ F.scalar := by
  refine ⟨F.distinct,?_,?_,M.word_fixed,fun γ hγ=>(F.mark γ hγ).scalar_fixed⟩
  · intro γ hγ
    have overhead_le :M.iF.toNat≤P6.ajO.toNat :=z0Z hw
    exact (bZ7 M F γ hγ).trans (z3b overhead_le _)
  · intro γ hγ
    let m:=F.mark γ hγ
    exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
theorem eMO {u D Γ} (M:jG u D) (F:mJ M Γ)
    (lo:1≤M.iF) (hi:M.iF≤P6.ajO) :
    ∃ P:jF Γ F.scalar,P.H.natDegree≤P6.ajO.toNat := by
  have hmax :M.iF.toNat≤(extend M.E).natDegree := by
    rw [Polynomial.natDegree_map]
    change M.iF.toNat≤M.E.natDegree
    unfold P6.jG.iF P6.FJ.iF P1.FJ.iF
    omega
  obtain ⟨H,hm,hd,hdiv⟩:=aR.gEn _ (M.E_monic.map embed) _ hmax
  let z := fun γ=>embed (M.label γ)
  have unit {P:K[X]} (hp:IsCoprime P M.E) :IsCoprime (extend P) H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ:K) :extend (M.wK γ)=extend M.A₀+C (z γ)*extend M.A₁:= by
    simp [P6.jG.wK,P6.FJ.wK,P1.FJ.wK,z]
  have hsmall:H.natDegree≤P6.ajO.toNat :=hd.le.trans (z0Z hi)
  refine ⟨⟨H,hm,?_,?_,?_,z,?_,extend M.factor,extend M.Q,extend M.A₀,
    extend M.A₁,unit M.coprime_factor.symm,unit M.offset_reduced,
    unit M.first_amplitude_unit,?_,?_⟩,hsmall⟩
  · rw [hd]
    exact ⟨by omega,(z0Z hi).trans (by decide)⟩
  · intro i hz
    obtain ⟨U,hU⟩:=hdiv
    have he : (extend M.E).eval (embed (node i))≠0:= by
      rw [Polynomial.eval_map_apply]
      exact (map_ne_zero embed).mpr (M.aFF i)
    apply he
    change (M.E.map embed).eval _=0
    rw [hU,Polynomial.eval_mul,hz,zero_mul]
  · intro γ hγ
    rw [hd]
    exact bZ7 M F γ hγ
  · intro a b hab
    exact sub_left_inj.mp (embed.injective hab)
  · intro γ hγ
    rw [← amp]
    exact unit (F.mark γ hγ).pole_unit
  · intro γ hγ
    have eqn:=(F.mark γ hγ).identity
    have orig:M.factor*M.wK γ*F.scalar γ+C (M.label γ)*M.Q =
        M.E*M.decoder (F.mark γ hγ).bad:= by rw [← eqn]; ring
    have mapped:=congrArg (Polynomial.map embed) orig
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C] at mapped
    rw [← amp]
    exact mapped ▸ hdiv.trans (dvd_mul_right _ _)
theorem Messages.mono {w Γ s Δ} (h:Messages w Γ s) (hΔ:Δ⊆Γ) :Messages w Δ s :=
  ⟨h.distinct.mono hΔ,fun γ hγ=>h.degree γ (hΔ hγ),fun γ hγ=>h.lg γ (hΔ hγ),
    h.word_fixed,fun γ hγ=>h.scalar_fixed γ (hΔ hγ)⟩
end
end P6_6
end
