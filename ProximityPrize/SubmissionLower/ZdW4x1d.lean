import ProximityPrize.SubmissionLower.ZucFfdd
import ProximityPrize.SubmissionLower.ZzOuVbd
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, Ideal.span → zye, Ideal.span_singleton_prime → zw5, IsFractionRing.injective → zxb, MvPolynomial.C → znf, MvPolynomial.aeval_X → zTw, MvPolynomial.aeval_eq_eval → zrv, MvPolynomial.eval → zY9, MvPolynomial.map → zDK, MvPolynomial.map_injective → zNV, MvPolynomial.map_map → z6Y, MvPolynomial.optionEquivRight → zyD, MvPolynomial.pderiv → zWe, MvPolynomial.support_map_of_injective → zra, Nat.add_le_add_left → z3b, Nat.le_add_left → zmL, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.sub_le → z7J, Nat.zero_le → zD0, Polynomial.C → z1z, Polynomial.C_injective → zmy, Polynomial.X → z7y, Polynomial.coeff_map → z0b, Polynomial.coeff_zero → zO6, Polynomial.eval_map_apply → zdm, Polynomial.finite_setOfPred_isRoot → zRS, Polynomial.mapRingHom → zhd, Polynomial.map_injective → zTo, Polynomial.natDegree_C → zti
set_option autoImplicit true
set_option Elab.async false
namespace qpI2NNd
noncomputable section
open Polynomial Finset MvPolynomial UniqueFactorizationMonoid PolynomialDifferential
open P6 (K node)
open P6_6 (Messages gZ bf mV)
open P6_6_7 (thirdFiber smallMarks biR ord ord_le)
open aR (af ao shape cK jet qE extend embed ceilDiv)
open oR (qg Rr ang separant)
open aeA (view gLc biB elimination d02
  d0Z cLA cLz)
open we (aGn cH eT qY Yk fW
  zq a3H cVV)
open aA1 (aNx)
open aF0 (power BJ YM)
open private Ka aYc cu8 from ProximityPrize.SubmissionLower.AH
open private bAW from ProximityPrize.SubmissionLower.CD
open private b9N from ProximityPrize.SubmissionLower.I
open private aM6 from ProximityPrize.SubmissionLower.Z3EWiUc
open scoped Polynomial BigOperators nonZeroDivisors
private abbrev leading (R:af 4) :af 3:=(view R).leadingCoeff
private abbrev lowerTotal (r :aR.Shape) :=r.b - r.t
private abbrev lowerTop (r :aR.Shape) :=(r.j-3*r.t)/2
private abbrev anL (u c:ℕ) :=max u ((2*c - 1)*u - c^2)
private abbrev firstScale :ℕ:=P6.t*(4*bf)+mV
private abbrev RatRow :=MvPolynomial (Fin 3) aGn
private abbrev ratRow :af 3 →+* RatRow :=zDK (algebraMap ao[X] aGn)
private abbrev vY:RatRow →+* eT 3:=zDK (algebraMap aGn cH)
private abbrev n8:=Ideal (eT 3)
private abbrev aap:=Σ _:n8,n8
private abbrev center :=qY z7y
private abbrev constants :ao →+* cH :=qY.comp z1z
private theorem ratRow_inj:zq4 ratRow :=
  zNV _ (zxb _ _)
private theorem constants_inj:zq4 constants :=
  fun _ _ h=>zmy (Yk h)
private theorem thirdFiber_eq (R:af 4) (S:ao[X]) :
    thirdFiber R S=(view R).map (zY9 (jet S)) := by
  let e :af 4 →+* ao[X][X] :=(zhd (zY9 (jet S))).comp view.toRingHom
  change MvPolynomial.eval₂Hom z1z (fun i:Fin 4=>if i=3 then z7y else z1z (jet S i)) R=e R
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun a=> by simp [e,view,MvPolynomial.eval_C]) (fun i => ?_)) R
  refine Fin.lastCases (by simp [e,view,show finSuccEquivLast (3:Fin 4)=none from finSuccEquivLast_last]) (fun j => ?_) i
  have hj:j.castSucc≠(3:Fin 4) :=Fin.castSucc_ne_last j
  simp [e,view,hj,jet]
private theorem coeff_zero {R:af 4} {S:ao[X]} (h:thirdFiber R S=0) (i:ℕ) :
    cK ((view R).coeff i) S=0:= by
  rw [thirdFiber_eq] at h
  simpa only [z0b,zO6,cK] using congrArg (fun f :ao[X][X]=>f.coeff i) h
private theorem leading_bounds {R:af 4} (hR:R≠0) :
    leading R≠0∧(leading R).totalDegree≤lowerTotal (shape R) ∧
      (leading R).degreeOf 2≤lowerTop (shape R) := by
  have hdeg: (view R).natDegree=(shape R).t:=gLc R
  refine ⟨Polynomial.leadingCoeff_ne_zero.mpr (fun h=>hR (view.injective (h.trans (map_zero _).symm))),?_,?_⟩
  · have h:=biB (1 :Fin 4→ℕ) R _ le_rfl
    simp only [Pi.one_apply,one_mul,← Pi.one_def,weightedTotalDegree_one] at h
    exact Nat.le_sub_of_add_le (hdeg ▸ h)
  · have h:=biB (fun i:Fin 4=>i.val) R _ le_rfl
    change (leading R).weightedTotalDegree (fun i:Fin 3=>i.val)+3*(view R).natDegree≤R.weightedTotalDegree (fun i:Fin 4=>i.val) at h
    rw [← Ex.C6,← Ex.C6,hdeg] at h
    have h' := biB (fun i:Fin 3=>i.val) (leading R) _ le_rfl
    have hb:2*(leading R).degreeOf 2≤qE (leading R) := by
      change 2*(leading R).degreeOf (Fin.last 2)≤_
      rw [Ex.C6,← gLc (leading R)]
      exact (zmL _ _).trans h'
    change qE (leading R)+3*(shape R).t≤(shape R).j at h
    change (leading R).degreeOf 2≤((shape R).j-3*(shape R).t)/2; omega
private theorem distinct_factors {r :ℕ} {A:af r} (hA:A≠0) :
    ∃ T:Finset (af r),(∀ f∈T,Irreducible f∧f∣A) ∧
      (∀ w:Fin r→ℕ,∑ f∈T,f.weightedTotalDegree w≤A.weightedTotalDegree w) ∧
      (∀ S:ao[X],cK A S=0 → ∃ f∈T,cK f S=0) := by
  classical
  let _:StrongNormalizationMonoid (af r) :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let M:=normalizedFactors A
  refine ⟨M.toFinset,fun f hf=>⟨irreducible_of_normalized_factor f (Multiset.mem_toFinset.mp hf),
      dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hf)⟩,
    fun w=>sum_weightedTotalDegree_le_of_prod_dvd w M.toFinset id hA
      ((Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hA).dvd),fun S hS => ?_⟩
  have hz :=map_dvd (zY9 (jet S)) (prod_normalizedFactors hA).symm.dvd
  change cK A S∣zY9 (jet S) M.prod at hz
  rw [hS,zero_dvd_iff,map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hz
  obtain ⟨f,hf,h0⟩:=hz; exact ⟨f,Multiset.mem_toFinset.mpr hf,h0⟩
private theorem boundary_cover {A:af 3} {u c:ℕ} (hA:A≠0) (hu:A.totalDegree≤u)
    (hc:A.degreeOf 2≤ c) (hcu:c≤u) (hchar :c<K1.p) :
    ∃ (T:Finset (af 3)) (q:af 2),
      (∀ f∈T,Irreducible f∧f∣A∧0<f.degreeOf 2) ∧
      (∑ f∈T,f.totalDegree)≤u∧q≠0∧q.totalDegree≤anL u c ∧
      ∀ S:ao[X],cK A S=0→cK q S=0 ∨ ∃ f∈T,qg 2 f S:= by
  classical
  obtain ⟨T,hfac,hs,hroot⟩:=distinct_factors hA
  let d (f :af 3) :=(view f).natDegree
  have hd (f :af 3) :d f=f.degreeOf 2 :=gLc f
  have hsum: (∑ f∈T,f.totalDegree)≤u :=
    (show (∑ f∈T,f.totalDegree)≤A.totalDegree by simpa only [weightedTotalDegree_one] using hs (1 :Fin 3→ℕ)).trans hu
  have htop: (∑ f∈T,d f)≤ c :=
    (show (∑ f∈T,d f)≤A.degreeOf 2 by simpa only [hd,weightedTotalDegree_piSingle] using hs (Pi.single (2 :Fin 3) 1)).trans hc
  have hn (f :af 3) (hf :f∈T) :elimination f≠0 :=
    d02 (hfac f hf).1 (((single_le_sum (fun j _=>zD0 (d j)) hf).trans htop).trans_lt hchar)
  refine ⟨T.filter fun f=>0<d f,∏ f∈T,elimination f,
    fun f hf=> let ⟨hT,hp⟩:=mem_filter.mp hf; ⟨(hfac f hT).1,(hfac f hT).2,hd f ▸ hp⟩,
    (sum_le_sum_of_subset (filter_subset _ _)).trans hsum,prod_ne_zero_iff.mpr hn,?_,?_⟩
  · rw [← weightedTotalDegree_one,weightedTotalDegree_prod _ _ _ hn]
    refine (bAW T (fun f=>f.totalDegree) d (fun f=>(elimination f).weightedTotalDegree 1)
      u 1 c hsum htop (by simpa using hcu) ?_ ?_ ?_).trans_eq (by simp only [anL,one_mul])
    · intro f _; simpa only [one_mul,hd] using f.degreeOf_le_totalDegree (2 :Fin 3)
    · intro f _ hf; simpa only [Pi.one_apply,← Pi.one_def,weightedTotalDegree_one] using cLA (1 :Fin 3→ℕ) f hf
    · intro f _ hf; simpa only [Pi.one_apply,← Pi.one_def,weightedTotalDegree_one,one_mul] using cLz (1 :Fin 3→ℕ) f hf
  · intro S hS
    obtain ⟨f,hf,hz⟩:=hroot S hS
    rcases d0Z f S hz with he | ⟨hp,hr⟩
    · left; change zY9 (jet S) (∏ f∈T,elimination f)=0; rw [map_prod]; exact prod_eq_zero hf he
    · exact Or.inr ⟨f,mem_filter.mpr ⟨hf,hp⟩,hr⟩
private theorem ordinate_count {w Γ s} (h:Messages w Γ s) {g:af 1} (hg:g≠0)
    (hz : ∀ γ∈Γ,cK g (extend (s γ))=0) :Γ.card≤g.totalDegree := by
  classical
  have hi:Set.InjOn (fun γ=>extend (s γ)) (Γ:Set K) := fun _ hx _ hy heq =>
    h.distinct hx hy (zTo embed embed.injective heq)
  rw [← card_image_of_injOn hi]
  refine (Polynomial.card_le_degree_of_subset_roots (p:=Ka g) fun b hb => ?_).trans (cu8 g)
  obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hb
  rw [Polynomial.mem_roots (fun h0=>hg (Ka.injective (h0.trans (map_zero _).symm)))]
  change (Ka g).eval (extend (s γ))=0; rw [aYc]; exact hz γ hγ
private theorem ceY {w Γ s} (h:Messages w Γ s) (f :af 2) (hf :Irreducible f)
    (hp:0<f.degreeOf 1) (hr : ∀ γ∈Γ,qg 1 f (extend (s γ))) :
    mV*Γ.card≤P6.t*(4*bf*f.totalDegree^2)+mV:= by
  let d:=f.totalDegree; let a :=BJ gZ d; let v :=YM gZ d d
  have hfd:f.degreeOf 1≤d:=f.degreeOf_le_totalDegree 1
  have hd:0<d:=hp.trans_le hfd
  have ha :0<a := by simp [a,BJ]
  have hv :0<v :=lt_min ha (Nat.lt_of_lt_of_le (by decide :0<gZ) (zmL _ _))
  obtain ⟨A⟩:=czH.proof f gZ d d (by decide) (by decide) hd le_rfl hfd
  have hsec:=P6_6_5.bv5 h (d*a) (fun i hi=> by
    refine (cz7.a8m h.distinct f hf hp hr ha hv i hi (A.cut (node i) (w i))
      (ana.aVQ _ (A.ags _ _) (A.top_bound _ _))
      (fun γ hγ=>A.agrees _ (h.degree γ hγ) (hr γ hγ) _ _)).trans ?_
    unfold cappedDegreeMixedVolume; change d*v+f.degreeOf 1*(a - v)≤d*a
    calc _≤d*v+d*(a - v) :=Nat.add_le_add_left (Nat.mul_le_mul_right _ hfd) _
      _ = _:= by rw [← Nat.mul_add,Nat.add_sub_of_le (show v≤a from min_le_left _ _)])
  have h1 :1≤(2*bf)*d:=Nat.mul_pos (by decide) hd
  have hmul :power gZ*(d - 1)≤(2*bf)*d :=
    Nat.mul_le_mul (by decide) (z7J _ _)
  have hcap:a≤4*bf*d:= by
    change 1+power gZ*(d - 1)≤_
    rw [show 4*bf*d=(2*bf)*d+(2*bf)*d by ring]; omega
  have hh:d*a≤4*bf*f.totalDegree^2 :=
    (zBI _ hcap).trans_eq (by change d*(4*bf*d)=4*bf*d^2; ring)
  exact hsec.trans (Nat.add_le_add_right (zBI _ hh) _)
private theorem ebC {w Γ s} (h:Messages w Γ s) {q:af 2} (hq:q≠0)
    (hchar :q.totalDegree<K1.p) (hz : ∀ γ∈Γ,cK q (extend (s γ))=0) :
    mV*Γ.card≤firstScale*q.totalDegree^2 := by
  classical
  obtain ⟨T,hf,ht,hroot⟩:=distinct_factors hq
  let part (f :af 2) :=Γ.filter fun γ=>cK f (extend (s γ))=0
  have hcover :Γ⊆T.biUnion part:= fun γ hγ =>
    let ⟨f,hT,hr⟩:=hroot _ (hz γ hγ); mem_biUnion.mpr ⟨f,hT,mem_filter.mpr ⟨hγ,hr⟩⟩
  have hds : (∑ f∈T,f.totalDegree)≤q.totalDegree := by
    simpa only [weightedTotalDegree_one] using ht (1 :Fin 2→ℕ)
  have hlocal (f :af 2) (hT:f∈T) :mV*(part f).card≤firstScale*f.totalDegree^2 := by
    let hm:=h.mono (Δ:=part f) (filter_subset _ _)
    let d:=f.totalDegree; let c:=(view f).natDegree; let g:=elimination f
    have hc:c≤d:=(gLc f).le.trans (f.degreeOf_le_totalDegree 1)
    have hfc:d<K1.p:=((single_le_sum (fun j _=>zD0 j.totalDegree) hT).trans hds).trans_lt hchar
    have hg:g≠0:=d02 (hf f hT).1 (hc.trans_lt hfc)
    by_cases hp:0<c
    · let ordS:=(part f).filter fun γ=>cK g (extend (s γ))=0
      let regS:=(part f).filter fun γ=>qg 1 f (extend (s γ))
      have hdeg:g.totalDegree+c^2≤(2*c - 1)*d:= by
        simpa only [Pi.one_apply,← Pi.one_def,weightedTotalDegree_one,one_mul] using cLz (1 :Fin 2→ℕ) f hp
      have hd:0<d:=hp.trans_le hc
      have hord:g.totalDegree≤d*(d - 1) := by
        have hp' : 1≤2*c:= by omega
        zify [hd,hp'] at hdeg ⊢; nlinarith [sq_nonneg ((d:ℤ)-(c:ℤ))]
      have h0:=(ordinate_count (hm.mono (Δ:=ordS) (filter_subset _ _)) hg (fun γ hγ=>(mem_filter.mp hγ).2)).trans hord
      have h1 :=ceY (hm.mono (Δ:=regS) (filter_subset _ _)) f (hf f hT).1 ((gLc f) ▸ hp)
        (fun γ hγ=>(mem_filter.mp hγ).2)
      have hsub:part f⊆ordS∪regS:= fun γ hγ =>
        (d0Z f _ (mem_filter.mp hγ).2).elim
          (fun hge=>mem_union_left _ (mem_filter.mpr ⟨hγ,hge⟩))
          (fun hre=>mem_union_right _ (mem_filter.mpr ⟨hγ,hre.2⟩))
      have hpoly :d*(d - 1)+1≤d^2 :=(z3b hd _).trans_eq
        (by rw [pow_two,← Nat.mul_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel hd])
      calc _≤ mV*(ordS.card+regS.card) :=Nat.mul_le_mul_left _ ((card_le_card hsub).trans (card_union_le _ _))
        _≤P6.t*(4*bf*d^2)+mV*(d*(d - 1)+1) := by
          rw [Nat.mul_add,Nat.mul_add,Nat.mul_one]
          exact (Nat.add_le_add (Nat.mul_le_mul_left _ h0) h1).trans_eq (by ring)
        _≤_:=(Nat.add_le_add_left (Nat.mul_le_mul_left mV hpoly) _).trans_eq
          (by change P6.t*(4*bf*d^2)+mV*d^2=firstScale*d^2; unfold firstScale; ring)
    · have hdeg:g.totalDegree≤d:= by
        simpa only [Pi.one_apply,← Pi.one_def,weightedTotalDegree_one] using cLA (1 :Fin 2→ℕ) f (Nat.eq_zero_of_not_pos hp)
      have hcard:=(ordinate_count hm hg fun γ hγ=>(d0Z f _ (mem_filter.mp hγ).2).resolve_right (fun h' => hp h'.1)).trans hdeg
      have hd:d≤d^2 :=Nat.le_self_pow (by decide :2≠0) d
      exact (zBI _ (hcard.trans hd)).trans (ztf _ (zmL _ _))
  calc _≤ mV * ∑ f∈T,(part f).card:=Nat.mul_le_mul_left _ ((card_le_card hcover).trans card_biUnion_le)
    _≤firstScale * ∑ f∈T,f.totalDegree^2 := by rw [Finset.mul_sum,Finset.mul_sum]; exact sum_le_sum hlocal
    _≤_:=Nat.mul_le_mul_left _ ((sum_sq_le_sq_sum_of_nonneg fun f _=>Nat.zero_le f.totalDegree).trans (pow_le_pow_left' hds _))
private theorem view_prime {R:af 4} (hR:Irreducible R) (ht:0<(view R).natDegree) :
    Irreducible ((view R).map ratRow) := by
  let P:=view R
  let:Algebra (af 3) RatRow :=MvPolynomial.algebraMvPolynomial
  let:Algebra (af 3)[X] RatRow[X] :=Polynomial.algebra (af 3) RatRow
  let M:=(ao[X]⁰).map (znf (σ:=Fin 3))
  let:IsLocalization M RatRow :=MvPolynomial.isLocalization (ao[X]⁰) aGn
  let D:=M.map z1z
  let:IsLocalization D RatRow[X] :=Polynomial.isLocalization M RatRow
  have hp:Irreducible P:=(MulEquiv.irreducible_iff view.toMulEquiv).mpr hR
  have hD:Disjoint (D:Set (af 3)[X]) (zye {P} : Ideal (af 3)[X]) := by
    rw [Set.disjoint_left]; rintro _ ⟨_,⟨a,ha,rfl⟩,rfl⟩ hd
    have ha' : z1z (znf (σ:=Fin 3) a)≠0 :=
      Polynomial.C_ne_zero.mpr ((map_ne_zero_iff _ (MvPolynomial.C_injective _ _)).mpr (nonZeroDivisors.ne_zero ha))
    have h:=Polynomial.natDegree_le_of_dvd (Ideal.mem_span_singleton.mp hd) ha'
    rw [zti] at h; exact not_le_of_gt ht h
  have h:=IsLocalization.isPrime_of_isPrime_disjoint D RatRow[X] (zye {P})
    ((zw5 hp.ne_zero).mpr hp.prime) hD
  rw [Ideal.map_span,Set.image_singleton] at h
  have hmap :P.map ratRow≠0:=(map_ne_zero_iff (zhd ratRow)
    (zTo ratRow ratRow_inj)).mpr hp.ne_zero
  exact ((zw5 hmap).mp h).irreducible
private theorem good_eval {F A:Type*} [Field F] [Infinite F] [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (i:F →+* A) {Q:A[X]} (hQ:Irreducible Q) (hd:0<Q.natDegree) :
    ∃ a :F,Q.eval (i a)≠0∧IsRelPrime Q.leadingCoeff (Q.eval (i a)) := by
  classical
  have hbad (p:A) (hp:Prime p) :Set.Finite {a :F | p∣Q.eval (i a)} := by
    let I:Ideal A:=zye {p}
    let:I.IsPrime :=(zw5 hp.ne_zero).mpr hp
    let j:=Ideal.Quotient.mk I
    have hn:Q.map j≠0:= fun hz=> by
      obtain ⟨T,hT⟩:=(Polynomial.C_dvd_iff_dvd_coeff p Q).mpr fun k =>
        Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (by rw [← z0b,hz,zO6]))
      rcases hQ.isUnit_or_isUnit hT with hu | hu
      · exact hp.not_isUnit (Polynomial.isUnit_C.mp hu)
      · rw [hT,Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hp.ne_zero) hu.ne_zero,
          zti,Polynomial.natDegree_eq_zero_of_isUnit hu] at hd; omega
    refine ((zRS hn).preimage (j.comp i).injective.injOn).subset fun a ha => ?_
    change (Q.map j).eval (j (i a))=0; rw [zdm]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ha)
  let T:=(factors Q.leadingCoeff).toFinset
  have hT: (⋃ p∈(T:Set A),{a :F | p∣Q.eval (i a)}).Finite :=
    T.finite_toSet.biUnion fun p hp=>hbad p (prime_of_factor p (Multiset.mem_toFinset.mp hp))
  have h0:=(zRS hQ.ne_zero).preimage i.injective.injOn
  obtain ⟨a,_,ha⟩:=Set.infinite_univ.exists_notMem_finite (h0.union hT)
  have hL:=Polynomial.leadingCoeff_ne_zero.mpr hQ.ne_zero
  refine ⟨a,fun hz=>ha (Or.inl hz),(isRelPrime_iff_no_prime_factors hL).mpr fun p hp hp' hprime => ?_⟩
  obtain ⟨q,hq,hassoc⟩:=exists_mem_factors_of_dvd hL hprime.irreducible hp
  exact ha (Or.inr (Set.mem_iUnion₂.mpr ⟨q,Multiset.mem_toFinset.mpr hq,hassoc.dvd_iff_dvd_left.mp hp'⟩))
private theorem proper_combination (R:af 4) (hR:Irreducible R) (ht:0<(shape R).t) :
    ∃ G:eT 3,G≠0∧G.totalDegree≤(shape R).b ∧
      IsRelPrime (fW (leading R)) G ∧
      ∀ S:ao[X],thirdFiber R S=0→zY9 (zq S) G=0:= by
  classical
  let P:=view R; let Q:=P.map ratRow
  have hP:0<P.natDegree :=(gLc R).symm ▸ ht
  have hQ:Irreducible Q:=view_prime hR hP
  have hdeg:Q.natDegree=P.natDegree :=Polynomial.natDegree_map_eq_of_injective ratRow_inj P
  let:Infinite aGn:=Infinite.of_injective ((algebraMap ao[X] aGn).comp z1z)
    ((zxb ao[X] aGn).comp zmy)
  obtain ⟨a,ha,hc⟩:=good_eval (znf (σ:=Fin 3)) hQ (hdeg.symm ▸ hP)
  let G:=vY (Q.eval (znf a))
  have hL:Q.leadingCoeff=ratRow (leading R) :=Polynomial.leadingCoeff_map_of_injective ratRow_inj P
  have hgeo:IsRelPrime (vY Q.leadingCoeff) G:=axh.fVP _ _ (Polynomial.leadingCoeff_ne_zero.mpr hQ.ne_zero) ha hc
  have hG:G = ∑ k∈range (P.natDegree+1),fW (P.coeff k)*(znf (algebraMap aGn cH a))^k := by
    change vY (Q.eval (znf a))= _; rw [Polynomial.eval_eq_sum_range,hdeg,map_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [map_mul,map_pow,MvPolynomial.map_C,Q,z0b,z6Y]; rfl
  refine ⟨G,(map_ne_zero_iff _ (zNV _ (algebraMap aGn cH).injective)).mpr ha,?_,?_,?_⟩
  · rw [hG]; refine MvPolynomial.totalDegree_finsetSum_le fun k hk=>(MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [← map_pow,MvPolynomial.totalDegree_C,Nat.add_zero]
    have he : (fW (P.coeff k)).totalDegree=(P.coeff k).totalDegree := by
      unfold fW totalDegree; rw [zra _ Yk]
    rw [he]
    have hw:=biB (1 :Fin 4→ℕ) R k (Nat.le_of_lt_succ (mem_range.mp hk))
    simp only [Pi.one_apply,one_mul,← Pi.one_def,weightedTotalDegree_one] at hw
    exact (Nat.le_add_right _ _).trans hw
  · rw [hL] at hgeo; simpa only [vY,ratRow,fW,qY,z6Y] using hgeo
  · intro S hS; rw [hG,map_sum]
    exact sum_eq_zero fun k _=> by rw [map_mul,aNx,coeff_zero hS k,map_zero,zero_mul]
attribute [local instance] MvPolynomial.algebraMvPolynomial
private def flatten (f :af 3) :DifferentialPolynomial ao 2 :=(zyD ao (Fin 3)).symm f
private def bY (f :af 3) :DifferentialPolynomial cH 2 :=zDK constants (flatten f)
private def cut (f :af 3) (x a :K) :eT 3 :=
  taylorAgreementEquation center (bY f) bf (2*bf) (constants (embed x)) (constants (embed a))
private theorem ayL (S:ao[X]) : (S.map constants).eval center=qY S:= by
  rw [Polynomial.eval_map]; change eval₂RingHom constants center S=qY S
  congr 1; exact Polynomial.ringHom_ext (fun a=> by simp [constants]) (by simp [center])
private theorem aQw (f :af 3) (S:ao[X]) :
    differentialSpecialization (flatten f) S=cK f S:= by
  let x :Option (Fin 3)→ao[X] := fun | none=>z7y | some i=>jet S i
  have h:=MvPolynomial.aeval_optionEquivRight_symm (R:=ao) x f
  have hx :x none=Polynomial.X:=rfl
  have hj: (fun i=>x (some i))=jet S:=rfl
  rw [hx,hj,Polynomial.aeval_X_left,show (AlgHom.id ao ao[X]).toRingHom=RingHom.id (ao[X]) from rfl,
    MvPolynomial.map_id,zrv] at h
  unfold flatten at *; unfold cK differentialSpecialization
  refine (AlgHom.congr_fun ?_ _).trans h
  exact MvPolynomial.algHom_ext fun v=> by rw [differentialSpecializationHom,zTw,zTw]; cases v <;> rfl
private theorem cut_degree (f :af 3) (hf :0<f.degreeOf 2) (x a :K) :
    (cut f x a).totalDegree≤4*bf*f.totalDegree := by
  have hcd:jetTotalDegree (bY f)≤f.totalDegree := by
    refine (jetTotalDegree_map_le constants _).trans ?_
    have hw: (jetDegreeWeight:Option (Fin 3)→ℕ)=fun v=>v.elim 0 (fun _=>1) := by funext v; cases v <;> rfl
    rw [jetTotalDegree,hw,← MvPolynomial.totalDegree_optionEquivRight]; simp only [flatten,AlgEquiv.apply_symm_apply,le_refl]
  refine (totalDegree_taylorAgreementEquation_le center (bY f) (taylorExponentSufficient_two_mul 2 bf) _ _).trans ?_
  unfold rationalTaylorCutDegreeBound
  refine (z3b (zBI _ (Nat.sub_le_sub_right hcd 1)) _).trans ?_
  have hd:0<f.totalDegree :=hf.trans_le (f.degreeOf_le_totalDegree 2)
  have h1 :1≤2*bf := by decide
  calc _≤2*bf*(f.totalDegree - 1)+2*bf := by omega
    _=2*bf*f.totalDegree := by rw [← Nat.mul_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel hd]
    _≤_:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
private theorem cut_eval {f :af 3} {S:K[X]} (hD:S.natDegree≤gZ)
    (hS:qg 2 f (extend S)) (x a :K) :
    zY9 (zq (extend S)) (cut f x a)=0↔S.eval x=a := by
  let U:=extend S; let V:=U.map constants
  have hjet:polynomialJet (d:=2) center V=zq U:= by
    funext i; change (hasseDeriv i.val V).eval center=qY (jet U i)
    rw [Polynomial.hasseDeriv_map,ayL]; rfl
  have hsol:differentialSpecialization (bY f) V=0:= by
    dsimp only [V]; rw [bY,← map_differentialSpecialization,aQw,hS.1,Polynomial.map_zero]
  have hsf :differentialSpecialization (PolynomialDifferential.separant (flatten f) (Fin.last 2)) U≠0:= by
    change differentialSpecialization (zWe (some 2) ((zyD ao (Fin 3)).symm f)) U≠0
    rw [← MvPolynomial.optionEquivRight_symm_pderiv]; exact (aQw (zWe 2 f) U).substr hS.2
  have hsep:jetEvaluation (PolynomialDifferential.separant (bY f) (Fin.last 2)) center (polynomialJet center V)≠0:= by
    dsimp only [V]; rw [← eval_differentialSpecialization,bY,← map_separant,← map_differentialSpecialization,ayL]
    exact (map_ne_zero_iff _ Yk).mpr hsf
  have hdeg:V.degree<(bf :WithBot ℕ) :=
    Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans (Polynomial.natDegree_map_le.trans hD)))
  let _:CharP ao K1.p:=charP_of_injective_ringHom embed.injective K1.p
  let _:CharP cH K1.p:=charP_of_injective_ringHom constants_inj K1.p
  have hp:K1.p.Prime :=CharP.char_prime_of_ne_zero cH (by decide)
  rw [cut,← hjet,← zrv,
    taylorAgreementEquation_eq_zero_iff center (bY f) (taylorExponentSufficient_two_mul 2 bf) _ (by rwa [aeval_initialJetSeparant]),
    rationalTaylorPolynomial_polynomialJet center (bY f) V hsol hsep hdeg
      fun i hi ht=>Polynomial.natCast_choose_ne_zero_of_lt_charP hp (ht.trans (by decide)) hi.le]
  simp only [V,U,zdm,constants_inj.eq_iff,embed.injective.eq_iff]
private theorem qv {F G H :eT 3} (hF:F≠0) (hrel :IsRelPrime F G) :
    ∃ T:Finset aap,
      (∀ Q∈T,Q.2.IsPrime∧(affineHilbertPolynomial Q.2).natDegree=1) ∧
      (∑ Q∈T,affineDegree Q.2)≤(G.totalDegree :ℚ)*F.totalDegree ∧
      ∀ x :Fin 3→cH,zY9 x F=0→zY9 x G=0→zY9 x H≠0 →
        ∃ Q∈T,x∈zeroLocus cH Q.2 := by
  classical
  let A:n8:=zye {F}; let C:=A.retainedMinimalPrimes H
  let step (P:n8) :=(P ⊔ zye {G}).retainedMinimalPrimes H
  have hP (P:n8) (hp:P∈C) :A.IsMinimalPrime P:=(Ideal.mem_retainedMinimalPrimes.mp hp).1
  have hprop {P:n8} (hp:A.IsMinimalPrime P) :G∉P:= fun hg=> by
    obtain ⟨z,hzp,hgz⟩:=Ideal.exists_mul_mem_of_mem_minimalPrimes hp hg
    exact hzp (Ideal.mem_span_singleton.mpr (hrel.dvd_of_dvd_mul_left (Ideal.mem_span_singleton.mp hgz)))
  refine ⟨C.sigma step,fun Q hQ => ?_,?_,fun x hx hg hh => ?_⟩
  · obtain ⟨hp,hq⟩:=mem_sigma.mp hQ; have hm:=(Ideal.mem_retainedMinimalPrimes.mp hq).1
    let _:=(hP Q.1 hp).isPrime
    have hd:=natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF (hP Q.1 hp)
    rw [Nat.card_fin] at hd
    have hdim:=principalCut_natDegree_affineHilbertPolynomial_add_one (hprop (hP Q.1 hp)) hm
    exact ⟨hm.isPrime,by omega⟩
  · have hsum : ∑ P∈C,affineDegree P≤(F.totalDegree :ℚ) := by
      simpa only [C,A,bot_sup_eq,affineDegree_bot,mul_one] using
        principalCut_sum_affineDegree_retainedMinimalPrimes_le (P:=(⊥ : n8)) H
          (show F∉(⊥ : n8) from fun h=>hF (Ideal.mem_bot.mp h)) le_rfl
    rw [sum_sigma]
    exact (sum_le_sum fun P hp=> let _:=(hP P hp).isPrime;
      principalCut_sum_affineDegree_retainedMinimalPrimes_le H (hprop (hP P hp)) le_rfl).trans
      (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  · have hxA:x∈zeroLocus cH A:= by simpa only [A,zeroLocus_span,Set.mem_ofPred_eq,Set.mem_singleton_iff,forall_eq,aeval_eq_eval] using hx
    obtain ⟨P,hp,hxP⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus A H x hxA (by rwa [aeval_eq_eval])
    obtain ⟨Q,hq,hxQ⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus _ H x
      (mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hxP,by rwa [aeval_eq_eval]⟩) (by rwa [aeval_eq_eval])
    exact ⟨⟨P,Q⟩,mem_sigma.mpr ⟨hp,hq⟩,hxQ⟩
private theorem chart_capacity {w Γ s} (hm:Messages w Γ s) (f :af 3) (G:eT 3)
    (hf :Irreducible f) (htop:0<f.degreeOf 2) (hrel :IsRelPrime (fW f) G)
    (hpts : ∀ γ∈Γ,qg 2 f (extend (s γ))∧zY9 (zq (extend (s γ))) G=0) :
    ∃ F:Rr w Γ s,Γ⊆F.CF∧F.n≤G.totalDegree*f.totalDegree ∧
      F.BJ≤4*bf*G.totalDegree*f.totalDegree^2 := by
  classical
  have hF:fW f≠0:=(map_ne_zero_iff _ (zNV qY Yk)).mpr hf.ne_zero
  obtain ⟨T,hT,hsum,hcover⟩:=qv (H :=fW (oR.separant f)) hF hrel
  let e :=T.equivFin.symm
  have hcomp (i:Fin T.card) :=hT (e i).val (e i).property
  choose d hd heq using fun i=>aM6 (e i).val.2 (hcomp i).1 (hcomp i).2
  have hdeg: (fW f).totalDegree=f.totalDegree := by
    unfold fW totalDegree; rw [zra _ Yk]
  rw [hdeg] at hsum
  have hds : (∑ i,d i)≤G.totalDegree*f.totalDegree := by
    have hq: ((∑ i,d i:ℕ) :ℚ)≤((G.totalDegree*f.totalDegree :ℕ) :ℚ) := by
      simp only [Nat.cast_sum,Nat.cast_mul]
      calc _ = ∑ i,affineDegree (e i).val.2 :=sum_congr rfl fun i _=>(heq i).symm
        _ = ∑ Q∈T,affineDegree Q.2 := by rw [Equiv.sum_comp e (fun Q:T=>affineDegree Q.val.2)]; exact sum_coe_sort T (fun Q:aap=>affineDegree Q.2)
        _≤_:=hsum
    exact_mod_cast hq
  let part (i:Fin T.card) :=Γ.filter fun γ=>zq (extend (s γ))∈zeroLocus cH (e i).val.2
  have hs (i:Fin T.card) :part i⊆Γ:=filter_subset _ _
  have hcap (i:Fin T.card) :ang w (part i) s (4*bf*f.totalDegree*d i) := by
    let hm' := hm.mono (hs i); let P:=(e i).val.2
    refine b9N fun j hj => ?_
    let q:=cut f (node j) (w j); let J:=P ⊔ zye {q}
    have hprop:q∉P:= fun hq=> let ⟨γ,hγ,hmiss⟩:=hj;
      hmiss ((cut_eval (hm'.degree γ hγ) (hpts γ (hs i hγ)).1 _ _).mp
        (by rw [← aeval_eq_eval]; exact (mem_filter.mp hγ).2 q hq))
    have hb:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime (hcomp i).1 hprop (cut_degree f htop (node j) (w j))
    rw [(hcomp i).2] at hb
    have hJ: (affineHilbertPolynomial J).natDegree=0:=Nat.eq_zero_of_le_zero hb.1
    have hjd:affineDegree J≤((4*bf*f.totalDegree*d i:ℕ) :ℚ) := by
      rw [affineDegree_of_natDegree_eq_zero hJ,Nat.cast_mul _ (d i),← heq i,affineDegree,(hcomp i).2]; simpa [J] using hb.2
    let H :=(part i).filter fun γ=>(s γ).eval (node j)=w j
    have hsub: (↑(H.image fun γ=>zq (n:=3) (extend (s γ))) :Set _)⊆zeroLocus cH J:= by
      intro x hx; obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hx; obtain ⟨hΓ,he⟩:=mem_filter.mp hγ
      exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨(mem_filter.mp hΓ).2,
        by rw [aeval_eq_eval]; exact (cut_eval (hm'.degree γ hΓ) (hpts γ (hs i hΓ)).1 _ _).mpr he⟩
    obtain ⟨hfin,hcard⟩:=finite_zeroLocus_and_ncard_le_affineDegree (K:=cH) J hJ
    have hc:=Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset,card_image_of_injOn ((cVV s (part i) hm'.distinct).mono (filter_subset _ _))] at hc
    exact Nat.cast_le.mp ((Nat.cast_le.mpr hc).trans (hcard.trans hjd))
  let F:Rr w Γ s :=⟨T.card,part,fun i=>4*bf*f.totalDegree*d i,hs,hcap⟩
  refine ⟨F,fun γ hγ => ?_,?_,?_⟩
  · obtain ⟨Q,hQ,hγQ⟩:=hcover (zq (extend (s γ)))
      (by rw [a3H,(hpts γ hγ).1.1,map_zero]) (hpts γ hγ).2
      (by rw [a3H]; exact (map_ne_zero_iff _ Yk).mpr (hpts γ hγ).1.2)
    refine mem_biUnion.mpr ⟨e.symm ⟨Q,hQ⟩,mem_univ _,mem_filter.mpr ⟨hγ,?_⟩⟩
    simpa only [Equiv.apply_symm_apply] using hγQ
  · calc F.n = ∑ _:Fin T.card,1 := by simp [F]
      _ ≤ ∑ i,d i:=sum_le_sum fun i _=>hd i
      _≤_:=hds
  · change (∑ i,4*bf*f.totalDegree*d i)≤_
    rw [← Finset.mul_sum]; exact (zBI _ hds).trans_eq (by ring)
theorem proof :P6_6_7.c7:= by
  classical
  intro C R l ell hR hg ht
  let b:=(shape R).b; let u:=lowerTotal (shape R); let c:=lowerTop (shape R); let g:=anL u c
  let zeroLabels :=C.Δ.filter fun γ=>thirdFiber R (extend (C.s γ))=0
  have hb:b≤4025:=hg.2.2.1.1.trans (z7J _ _)
  have hu:u≤4025:=(z7J _ _).trans hb
  have hcu:c≤u:= by have :=R.degreeOf_le_totalDegree 3; have :=hR.2.1.2.2; dsimp [u,c,lowerTotal,lowerTop]; omega
  obtain ⟨hA,hdA,htA⟩:=leading_bounds hR.1.ne_zero
  obtain ⟨T,q,hf,hd,hq,hdq,hcover⟩:=boundary_cover hA hdA htA hcu ((hcu.trans hu).trans_lt (by decide))
  obtain ⟨G,_,hdG,hrel,hcut⟩:=proper_combination R hR.1 ht
  have hZ:=C.messages.mono (Δ:=zeroLabels) (filter_subset _ _)
  let E :=zeroLabels.filter fun γ=>cK q (extend (C.s γ))=0
  let part (f :af 3) :=zeroLabels.filter fun γ=>qg 2 f (extend (C.s γ))
  have hsub:zeroLabels⊆E∪T.biUnion part:= fun γ hγ =>
    (hcover _ (coeff_zero (mem_filter.mp hγ).2 _)).elim
      (fun hE=>mem_union_left _ (mem_filter.mpr ⟨hγ,hE⟩))
      (fun ⟨f,hf,hr⟩=>mem_union_right _ (mem_biUnion.mpr ⟨f,hf,mem_filter.mpr ⟨hγ,hr⟩⟩))
  have hcard:=(card_le_card hsub).trans ((card_union_le _ _).trans (z3b card_biUnion_le E.card))
  have hbc:g<K1.p:=(max_le (hu.trans (by decide)) ((z7J _ _).trans (Nat.mul_le_mul (by omega :2*c - 1≤8050) hu))).trans_lt (by decide)
  have hE :=ebC (hZ.mono (Δ:=E) (filter_subset _ _)) hq (hdq.trans_lt hbc) (fun γ hγ=>(mem_filter.mp hγ).2)
  change mV*E.card≤(P6.t*(4*bf)+mV)*q.totalDegree^2 at hE
  have hE' : mV*E.card≤P6.t*(4*bf * g^2)+mV*g^2 :=
    (hE.trans (zBI _ (pow_le_pow_left' hdq 2))).trans_eq (by ring)
  have hr :mV * ∑ f∈T,(part f).card≤P6.t*(4*bf*b*u^2)+mV*(b*u) := by
    have hloc (f :af 3) (hft:f∈T) :mV*(part f).card ≤
        P6.t*(4*bf*b*f.totalDegree^2)+mV*(b*f.totalDegree) := by
      have hm:=hZ.mono (Δ:=part f) (filter_subset _ _)
      obtain ⟨hirr,hdiv,htop⟩:=hf f hft
      obtain ⟨F,hF,hn,hc⟩:=chart_capacity hm f G hirr htop (hrel.of_dvd_left (map_dvd (zDK qY) hdiv))
        (fun γ hγ=>⟨(mem_filter.mp hγ).2,hcut _ (mem_filter.mp (mem_filter.mp hγ).1).2⟩)
      exact ((zBI mV (card_le_card hF)).trans (P6_6_5.bJG F hm)).trans
        (Nat.add_le_add (zBI _ (hc.trans (ztf _ (zBI _ hdG))))
          (zBI _ (hn.trans (ztf _ hdG))))
    have hsq: (∑ f∈T,f.totalDegree^2)≤u^2 :=
      (sum_sq_le_sq_sum_of_nonneg fun f _=>zD0 f.totalDegree).trans (pow_le_pow_left' hd _)
    let a :=P6.t*(4*bf*b); let ig:=mV*b
    calc _ = ∑ f∈T,mV*(part f).card:=Finset.mul_sum ..
      _ ≤ ∑ f∈T,(a*f.totalDegree^2+ig*f.totalDegree) :=sum_le_sum fun f ht=>(hloc f ht).trans_eq (by simp only [a,ig,Nat.mul_assoc])
      _=a*(∑ f∈T,f.totalDegree^2)+ig * ∑ f∈T,f.totalDegree := by rw [sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      _≤a*u^2+ig*u:=Nat.add_le_add (Nat.mul_le_mul_left _ hsq) (Nat.mul_le_mul_left _ hd)
      _ = _:= by simp only [a,ig,Nat.mul_assoc]
  have hcharge :mV*zeroLabels.card ≤
      4*bf*P6.t*(b*u^2+g^2)+mV*(b*u+g^2) := by
    refine (zBI mV hcard).trans ?_
    rw [Nat.mul_add]; exact (Nat.add_le_add hE' hr).trans_eq (by ring)
  have hz :zeroLabels.card≤biR (shape R) := by
    have hc:zeroLabels.card≤ ceilDiv (4*bf*P6.t*(b*u^2+g^2)) 46402+(b*u+g^2) := by
      unfold ceilDiv; change 46402*zeroLabels.card≤_+46402*_ at hcharge; omega
    change zeroLabels.card≤ ceilDiv (4*bf*P6.t*(b*u^2+g^2)) 46402+b*u+g^2+u
    simpa only [Nat.add_assoc] using hc.trans (Nat.le_add_right _ u)
  calc smallMarks C R true = ∑ γ∈zeroLabels,ord C R γ:= by simp only [smallMarks,zeroLabels,sum_filter,eq_self,iff_true]
    _ ≤ ∑ _γ∈zeroLabels,b:=sum_le_sum fun γ _=>ord_le C R γ
    _=b*zeroLabels.card:= by simp [Nat.mul_comm]
    _≤_:=Nat.mul_le_mul_left _ hz
end
end qpI2NNd
