import ProximityPrize.SubmissionLower.ZbvbtFa
import ProximityPrize.SubmissionLower.ZX4kd1a
set_option Elab.async false
open _root_ renaming Fin.castSucc → z1o, Fin.castSucc_injective → zX8, Finsupp.single → zhf, Ideal.span → zye, Ideal.span_singleton_prime → zw5, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.map → zDK, MvPolynomial.map_injective → zNV, MvPolynomial.ringHom_ext → zXT, Nat.mul_le_mul_left → zBI, Nat.sub_le → z7J, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.coeff_map → z0b, Polynomial.eq_C_of_natDegree_eq_zero → zr7, Polynomial.map → zGG, Polynomial.map_injective → zTo, RingHom.congr_fun → zLs
section
set_option autoImplicit true
namespace q0TFWAc
noncomputable section
open P6_6 P6_6_7 q6t08kb
open aR (af Shape shape aO extend wU cK)
open Ex (X7)
open dN (GeoJets GeoField bC kC Ch)
open agL (BV)


abbrev Input (C:Context) (R:af 4) (l ell:ℕ) :Prop :=
  HigherIndex C R l ell∧0<(X7 R).degreeOf 2
abbrev body (R:af 4) :=lowerBody (shape R)
def lowerFits (V:af 4) (a :Shape) :Prop :=
  aO (shape V) ⟨a.b,a.j,0⟩∧V.degreeOf 2≤a.t
def ajA (R:af 4) :af 4 :=BV (zhf 2 1) R
abbrev ke (R:af 4) :=kC R (ajA R)
def active (C:Context) (R:af 4) :Finset P6.K :=
  (nonzeroFibers C R).filter (fun γ=>1<ord C R γ)
def curveDegree (T:Ideal GeoJets) (a :Shape) :ℚ :=
  let E :=yz.aCt (a.scale 2) 0
  MvPolynomial.affineDegree (T.comap (MvPolynomial.monomialMap GeoField E).toRingHom)/2
def SectionBound (C:Context) (T:Ideal GeoJets) (a :Shape) :Prop :=
  ∀ (V:af 4),lowerFits V a→bC V∉T →
    ∀ (M:Finset P6.K),M⊆C.Δ →
      (∀ γ∈M,T≤Ch (extend (C.s γ))) →
      ∀ j:P6.K→ℕ,(∀ γ∈M,wU V (extend (C.s γ)) (j γ)) →
        (∑ γ∈M,(j γ:ℚ))≤ curveDegree T a
structure Chart (C:Context) (R:af 4) (T:Ideal GeoJets) where
  sep:af 4
  fits :lowerFits sep (body R)
  proper :bC sep∉T
  unitDebit :1≤ curveDegree T (body R)
  D4 : ∀ i:P6.I,∃ D:af 4,lowerFits D (lowerTaylor (body R)) ∧
    ∀ γ∈active C R,T≤Ch (extend (C.s γ)) →
      cK sep (extend (C.s γ))≠0 →
      (cK D (extend (C.s γ))=0↔(C.s γ).eval (P6.node i)=C.w i)
end
end q0TFWAc
end
section
set_option autoImplicit true
namespace qvavQkd
noncomputable section
open Finset MvPolynomial P6_6_7 q6t08kb UniqueFactorizationMonoid
open aR (af ao shape extend embed cK)
open Ex (X7 YN aQU)
open aeA (view gLc)
open ana (Tv asx bhW Ia b8P u7 bT0)
open scoped Polynomial BigOperators nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem fraction_irreducible {n:ℕ} {f :af n} {i:Fin n}
    (hf :Irreducible f) (hi:0<f.degreeOf i) :
    Irreducible (zDK asx f) := by
  let M:=(ao[X]⁰).map (MvPolynomial.C (σ:=Fin n))
  have hI: (zye {f}).IsPrime :=
    (zw5 hf.ne_zero).mpr hf.prime
  have hdis :Disjoint (M:Set (af n)) (zye {f} : Ideal (af n)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a,ha,rfl⟩ hd
    obtain ⟨q,hq⟩:=Ideal.mem_span_singleton.mp hd
    have ha' : a≠0:=nonZeroDivisors.ne_zero ha
    have hq' : q≠0:= fun h=>ha' (by simpa [h] using hq)
    have hh:=congrArg (MvPolynomial.degreeOf i) hq
    rw [MvPolynomial.degreeOf_C,MvPolynomial.degreeOf_mul_eq hf.ne_zero hq'] at hh
    omega
  have h:=IsLocalization.isPrime_of_isPrime_disjoint M
    (z3y (Fin n) Tv) (zye {f}) hI hdis
  have hn:=(zNV _ bhW).ne hf.ne_zero
  rw [map_zero] at hn
  exact ((zw5 hn).mp
    (by simpa only [MvPolynomial.algebraMap_def,Ideal.map_span,Set.image_singleton] using h)).irreducible
private theorem coeff_degree {n:ℕ} (f :af (n+1)) (j:ℕ) :
    ((view f).coeff j).totalDegree≤f.totalDegree :=
  (totalDegree_coeff_optionEquivLeft_le ao[X] (Fin n) _ j).trans (totalDegree_rename_le _ f)
private theorem eLN (p:af 2) : (u7 p).totalDegree≤p.totalDegree := by
  unfold u7 totalDegree
  exact Finset.sup_mono (support_map_subset asx p)
private theorem plane_cut {F:Type*} [Field F] {g q:z3y (Fin 2) F}
    (hg:Irreducible g) (hq : ¬g∣q) {b:ℕ} (hb:q.totalDegree≤b)
    (S:Finset (Fin 2→F)) (hS : ∀ x∈S,aeval x g=0∧aeval x q=0) :
    S.card≤b*g.totalDegree := by
  classical
  let P:Ideal (z3y (Fin 2) F) :=zye {g}
  have hp:P.IsPrime :=(zw5 hg.ne_zero).mpr hg.prime
  have hqP:q∉P:= fun h=>hq (Ideal.mem_span_singleton.mp h)
  have hd:=natDegree_affineHilbertPolynomial_span_singleton_add_one hg.ne_zero hp.ne_top
  rw [Nat.card_eq_fintype_card,Fintype.card_fin] at hd
  change (affineHilbertPolynomial P).natDegree+1=2 at hd
  have h:=ncard_inter_cut_le_of_retained_le (P:=P) (1 :z3y (Fin 2) F) hqP hb S
    (fun x hx=>⟨by simpa [P,zeroLocus_span] using (hS x hx).1,by simp⟩)
    (c:=1) zero_le_one (by
      intro Q hQ
      have he :=principalCut_natDegree_affineHilbertPolynomial_add_one hqP
        (Ideal.mem_retainedMinimalPrimes.mp hQ).1
      obtain ⟨hf,hbound⟩:=finite_zeroLocus_and_ncard_le_affineDegree (K:=F) Q (by omega)
      rw [mul_one]
      exact le_trans (by exact_mod_cast Set.ncard_le_ncard Set.inter_subset_right hf) hbound)
  have hs : (S:Set (Fin 2→F)) ∩ {z | aeval z q=0} = S :=
    Set.inter_eq_left.mpr fun x hx=>(hS x hx).2
  rw [hs,Set.ncard_coe_finset,mul_one,show P=zye {g} from rfl,
    affineDegree_span_singleton hg.ne_zero] at h
  exact_mod_cast h
private theorem base_count {F:Type*} [Field F] {A:Polynomial (z3y (Fin 2) F)}
    (hA:A.IsPrimitive) {b:ℕ} (hb : ∀ j,(A.coeff j).totalDegree≤b)
    (S:Finset (Fin 2→F)) (hS : ∀ x∈S,∀ j,aeval x (A.coeff j)=0) :
    S.card≤b^2 := by
  classical
  let:StrongNormalizationMonoid (z3y (Fin 2) F) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let L:=A.leadingCoeff
  let M:=normalizedFactors L
  let T:=M.toFinset
  let part (g:z3y (Fin 2) F) :=S.filter fun x=>aeval x g=0
  have hL:L≠0:=Polynomial.leadingCoeff_ne_zero.mpr hA.ne_zero
  have hcover :S⊆T.biUnion part:= by
    intro x hx
    have he :aeval x L=0:=hS x hx A.natDegree
    have ht:=map_dvd (aeval x) (prod_normalizedFactors hL).symm.dvd
    rw [he,zero_dvd_iff,map_multiset_prod,Multiset.prod_eq_zero_iff,
      Multiset.mem_map] at ht
    obtain ⟨g,hg,hz⟩:=ht
    exact mem_biUnion.mpr ⟨g,Multiset.mem_toFinset.mpr hg,mem_filter.mpr ⟨hx,hz⟩⟩
  have hpart (g:z3y (Fin 2) F) (hg:g∈T) :
      (part g).card≤b*g.totalDegree := by
    have hi:=irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
    obtain ⟨j,hj⟩ : ∃ j,¬g∣A.coeff j:= by
      by_contra! h
      exact hi.not_isUnit (hA g ((Polynomial.C_dvd_iff_dvd_coeff g A).mpr h))
    exact plane_cut hi hj (hb j) _ (fun x hx =>
      ⟨(mem_filter.mp hx).2,hS x (mem_filter.mp hx).1 j⟩)
  have hd: (∑ g∈T,g.totalDegree)≤b:= by
    have hdiv : (∏ g∈T,g)∣L :=
      (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hL).dvd
    have h:=sum_weightedTotalDegree_le_of_prod_dvd (1 :Fin 2→ℕ) T id hL hdiv
    simpa only [id_eq,weightedTotalDegree_one] using h.trans
      (show L.weightedTotalDegree (1 :Fin 2→ℕ)≤b by
        rw [weightedTotalDegree_one]
        exact hb A.natDegree)
  calc
    S.card ≤ ∑ g∈T,(part g).card:=(card_le_card hcover).trans card_biUnion_le
    _ ≤ ∑ g∈T,b*g.totalDegree :=sum_le_sum hpart
    _≤b^2 := by rw [← mul_sum,pow_two]; exact zBI _ hd
private theorem fiber_mem {C:Context} {R:af 4} {γ:P6.K}
    (h:γ∈zeroFibers C R) :
    γ∈C.Δ∧aP6 R (extend (C.s γ))=0:= by
  classical
  unfold zeroFibers at h
  exact mem_filter.mp h
private theorem fiber_coeff {R:af 4} {S:ao[X]} (h:aP6 R S=0) (j:ℕ) :
    cK ((view (X7 R)).coeff j) S=0:= by
  have h' : (aP6 R S).coeff j=(0:ao[X][X]).coeff j :=
    congrArg (fun P:ao[X][X]=>P.coeff j) h
  simpa only [aP6,z0b,Polynomial.coeff_zero,cK] using h'
theorem proof :q6t08kb.c5:= by
  classical
  intro C R l ell h hp
  let f :=X7 R
  have ht:=(aQU R).trans h.2.2.1
  have htop:YN R=z1z f := by
    simpa only [f,X7,Polynomial.leadingCoeff,ht] using
      (zr7 ht)
  have hf :Irreducible f := by
    have hi:=h.1.1.map YN
    rw [htop] at hi
    refine ⟨fun hu=>hi.not_isUnit (Polynomial.isUnit_C.mpr hu),?_⟩
    intro a b hab
    have hmul :z1z f=z1z a*z1z b:= by rw [← map_mul,← hab]
    exact (hi.isUnit_or_isUnit hmul).imp Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp
  have hb:f.totalDegree≤(shape R).b:= by
    change ((view R).coeff (YN R).natDegree).totalDegree≤R.totalDegree
    exact coeff_degree R _
  let A:=(view f).map (zDK asx)
  have hAi:Irreducible A:= by
    have hE :A=optionEquivLeft Tv (Fin 2)
        (rename finSuccEquivLast (zDK asx f)) := by
      change zGG _ (optionEquivLeft _ _ (rename _ f))= _
      rw [map_optionEquivLeft,map_rename]
    rw [hE]
    exact ((fraction_irreducible hf hp).map (renameEquiv _ finSuccEquivLast)).map
      (optionEquivLeft _ _)
  have hAd:0<A.natDegree := by
    change 0<((view f).map (zDK asx)).natDegree
    rwa [Polynomial.natDegree_map_eq_of_injective (zNV _ bhW),
      gLc]
  let x (γ:P6.K) :=Ia (extend (C.s γ))
  have hx :Set.InjOn x (zeroFibers C R:Set P6.K) := by
    intro γ hγ η hη heq
    exact C.messages.distinct (@fiber_mem C R γ hγ).1 (@fiber_mem C R η hη).1
      (zTo embed embed.injective (b8P heq))
  rw [← card_image_of_injOn hx]
  apply base_count (hAi.isPrimitive hAd.ne') (b:=(shape R).b)
  · intro j
    change ((zGG (zDK asx) (view f)).coeff j).totalDegree≤_
    rw [z0b]
    exact (eLN ((view f).coeff j)).trans ((coeff_degree f j).trans hb)
  · intro y hy j
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hy
    have he :cK ((view f).coeff j) (extend (C.s γ))=0 :=
      @fiber_coeff R (extend (C.s γ)) (@fiber_mem C R γ hγ).2 j
    change aeval (x γ) ((zGG (zDK asx) (view f)).coeff j)=0
    rw [z0b]
    change aeval (Ia (extend (C.s γ))) (u7 ((view f).coeff j))=0
    rw [bT0,he,map_zero]
end
end qvavQkd
end
section
set_option autoImplicit true
set_option maxHeartbeats 1000000
namespace qsZufGc
noncomputable section
open aR (af ao shape jet Z8 wU extend embed)
open Ex (X7 YN)
open agL (EY)
open P6_6 P6_6_7 q6t08kb MvPolynomial
open scoped Polynomial BigOperators
open private Mt Ka bqd QI from ProximityPrize.SubmissionLower.AH
open private bpk from ProximityPrize.SubmissionLower.CD
open private cSn from ProximityPrize.SubmissionLower.ZZr1mWc
open private orderAt_ord from ProximityPrize.SubmissionLower.ZfVU1Oc
private theorem lower_vars {n:ℕ} (g:af (n+1)) (hg:g.degreeOf (Fin.last n)=0) :
    (g.vars :Set (Fin (n+1)))⊆Set.range Fin.castSucc:= by
  intro i hi
  refine Fin.lastCases ?_ (fun j _=>⟨j,rfl⟩) i hi
  intro h
  exact ((mem_vars_iff_degreeOf_ne_zero.mp h) hg).elim
private theorem two_jets {R:af 4} (ht: (shape R).t=0)
    (hp: (X7 R).degreeOf 2=0) :
    ∃ f :af 2,rename (z1o ∘ z1o) f=R:= by
  obtain ⟨g,hg⟩:=exists_rename_eq_of_vars_subset_range R z1o
    (zX8 3) (lower_vars R ht)
  have hv :YN.toRingHom.comp (rename (R:=ao[X]) z1o).toRingHom =
      Polynomial.C:= by
    apply zXT
    · intro c
      simp [YN,optionEquivLeft_C]
    · intro i
      simp [YN,optionEquivLeft_X_some]
  have ha :X7 R=g:= by
    rw [ X7,← hg,show YN (rename z1o g)=z1z g
      from DFunLike.congr_fun hv g,Polynomial.leadingCoeff_C]
  obtain ⟨f,hf⟩:=exists_rename_eq_of_vars_subset_range g z1o
    (zX8 2) (lower_vars g (ha ▸ hp))
  exact ⟨f,(rename_rename _ _ _).symm.trans (hf ▸ hg)⟩
private abbrev incl:Fin 2→Fin 4 :=z1o ∘ z1o
private theorem incl_inj:Function.Injective incl :=
  (zX8 3).comp (zX8 2)
private theorem irreducible_lower {f :af 2} (h:Irreducible (rename incl f)) :
    Irreducible f := by
  let back :af 4 →ₐ[ao[X]] af 2 :=rename (fun i:Fin 4=>Fin.ofNat 2 i.val)
  have hback (g:af 2) :back (rename incl g)=g:= by
    change rename _ (rename _ g)=g
    rw [rename_rename]
    have hcomp: (fun i:Fin 4=>Fin.ofNat 2 i.val) ∘ incl=id := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp,rename_id_apply]
  refine ⟨fun hu=>h.not_isUnit (hu.map (rename incl)),?_⟩
  intro g q hmul
  have hmul' : rename incl f=rename incl g*rename incl q:= by rw [hmul,map_mul]
  rcases h.isUnit_or_isUnit hmul' with hu | hu
  · exact Or.inl (hback g ▸ hu.map back)
  · exact Or.inr (hback q ▸ hu.map back)
private def slice (S:ao[X]) :af 4 →+* ao[X][X] :=
  eval₂Hom z1z fun i=>if i=0 then z7y else z1z (jet S i)
private def sliceZero:af 4 →+* ao[X][X] :=
  eval₂Hom z1z fun i=>if i=0 then z7y else 0
private theorem dex (R:af 4) (S:ao[X]) :
    sliceZero (Z8 R S)=(slice S R).comp (z7y+Polynomial.C S) := by
  let shift:af 4 →+* af 4 :=
    eval₂Hom MvPolynomial.C (fun i=>z9v i+MvPolynomial.C (jet S i))
  have he :sliceZero.comp shift =
      (Polynomial.compRingHom (z7y+Polynomial.C S)).comp (slice S) := by
    apply zXT
    · intro c
      simp [shift,sliceZero,slice]
    · intro i
      by_cases hi:i=0
      · subst i
        simp [shift,sliceZero,slice,jet]
      · simp [shift,sliceZero,slice,hi]
  exact zLs he R
private theorem slice_order {R:af 4} {S:ao[X]} {n:ℕ} (h:wU R S n) :
    (z7y-Polynomial.C S)^n∣slice S R:= by
  have hX: (z7y ^n).comp (z7y-Polynomial.C S) =
      (z7y-Polynomial.C S)^n:= by rw [Polynomial.pow_comp,Polynomial.X_comp]
  rw [← hX,← Polynomial.dvd_comp_X_add_C_iff,← dex]
  rw [(Z8 R S).as_sum,map_sum]
  apply Finset.dvd_sum
  intro m hm
  rw [sliceZero,eval₂Hom_monomial,Finsupp.prod]
  by_cases hall : ∀ i∈m.support,i=(0:Fin 4)
  · have hprod: (∏ i∈m.support,(if i=(0:Fin 4) then z7y else 0)^m i) =
        (z7y:ao[X][X])^m.sum (fun _ a=>a) := by
      rw [Finsupp.sum,← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun i hi=> by simp [hall i hi]
    rw [hprod]
    exact ((pow_dvd_pow _ (h m hm)).mul_left _)
  · push Not at hall
    obtain ⟨i,hi,hne⟩:=hall
    rw [Finset.prod_eq_zero hi (by simp [hne,Finsupp.mem_support_iff.mp hi]),mul_zero]
    exact dvd_zero _
private def specialize (S:ao[X]) : (af 1)[X] →+* ao[X][X] :=
  (Polynomial.evalRingHom (z1z (jet S (1 :Fin 2)))).comp
    (Polynomial.mapRingHom Ka.toRingHom)
private theorem bOe (S:ao[X]) (a :af 1) :
    specialize S (z1z a)=Ka a := by
  simp [specialize]
private theorem firstView_X0 :
    Mt (z9v 0:af 2)=z1z (z9v 0:af 1) := by
  rw [Mt,AlgEquiv.trans_apply,renameEquiv_apply,rename_X,
    show finSuccEquivLast (0:Fin 2)=some 0 from finSuccEquivLast_castSucc (0:Fin 1),
    optionEquivLeft_X_some]
private theorem firstView_X1 :
    Mt (z9v 1 :af 2)=(z7y: (af 1)[X]) := by
  rw [Mt,AlgEquiv.trans_apply,renameEquiv_apply,rename_X,
    show finSuccEquivLast (1 :Fin 2)=none from finSuccEquivLast_last,optionEquivLeft_X_none]
private theorem specialize_view (S:ao[X]) (f :af 2) :
    specialize S (Mt f)=slice S (rename incl f) := by
  have h: (specialize S).comp Mt.toRingHom=(slice S).comp (rename incl).toRingHom:= by
    apply zXT
    · intro c
      simp [Mt,optionEquivLeft_C,bOe,Ka,slice]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change specialize S (Mt (z9v 1)) =
          slice S (rename incl (z9v 1))
        rw [firstView_X1,rename_X]
        simp [specialize,slice,incl,jet]
      · have hj:j=0:=Subsingleton.elim _ _
        subst j
        change specialize S (Mt (z9v 0)) =
          slice S (rename incl (z9v 0))
        rw [firstView_X0,rename_X,bOe]
        simp [Ka,slice,incl]
  exact zLs h f
private theorem eliminant_order (f :af 2) (S:ao[X]) {n:ℕ}
    (h:wU (rename incl f) S n) :
    (z7y-Polynomial.C S)^(n - 1)∣QI f := by
  let A:=Mt f
  let d:=A.natDegree
  let L:ao[X][X] :=z7y-Polynomial.C S
  have hf :L^n∣specialize S A:= by
    rw [show specialize S A=slice S (rename incl f) from specialize_view S f]
    exact slice_order h
  have he :L^(n - 1)∣specialize S A:=(pow_dvd_pow _ (z7J _ _)).trans hf
  by_cases hd:0<d
  · obtain ⟨p,q,-,-,hpq⟩:=Polynomial.exists_mul_add_mul_eq_C_resultant A A.derivative
      (m:=d) (n:=d - 1) le_rfl (Polynomial.natDegree_derivative_le A) (Or.inl hd.ne')
    have hf' : L^(n - 1)∣specialize S A.derivative := by
      rw [show A.derivative=Mt (pderiv 1 f) from (bqd f).symm,
        specialize_view,← pderiv_rename incl_inj]
      have hder :=q8NBBre.cUA (rename incl f) S (zhf (1 :Fin 4) 1) n h
      rw [cSn,show EY (zhf (1 :Fin 4) 1)=1 by simp [EY]] at hder
      exact slice_order hder
    have hres :=congrArg (specialize S) hpq
    simp only [map_add,map_mul,bOe] at hres
    rw [QI,ite_eq_left hd,← hres]
    exact (he.mul_right _).add (hf'.mul_right _)
  · have hA:A=z1z (A.coeff 0) :=
      zr7 (Nat.eq_zero_of_not_pos hd)
    have hval :specialize S A=Ka (A.coeff 0) :=
      (congrArg (specialize S) hA).trans (bOe _ _)
    rwa [QI,ite_eq_right hd,← hval]
theorem proof :q6t08kb.c6:= by
  classical
  intro C R l ell h hz
  by_cases hb:2≤(shape R).b
  · obtain ⟨f,hf⟩:=two_jets h.2.2.1 hz
    change rename incl f=R at hf
    have hfi:Irreducible f :=irreducible_lower (hf.symm ▸ h.1.1)
    have hB:f.totalDegree=(shape R).b:= by
      change f.totalDegree=R.totalDegree
      rw [← hf,← weightedTotalDegree_one,← weightedTotalDegree_one,
        weightedTotalDegree_rename_of_injective incl_inj]
      rfl
    have hcap: (shape R).b<K1.p :=
      (h.2.1.2.2.1.1.trans (z7J _ _)).trans_lt (show Wk.b<K1.p by decide)
    obtain ⟨hne,hdeg,_⟩:=bpk hb hcap f hfi hB.le
    let v (γ:P6.K) :=extend (C.s γ)
    have hinj:Set.InjOn v (C.Δ:Set P6.K) := by
      intro a ha b hb hab
      exact C.messages.distinct ha hb (zTo embed embed.injective hab)
    calc
      excessWeight C R C.Δ ≤ ∑ γ∈C.Δ,(QI f).rootMultiplicity (v γ) := by
        apply Finset.sum_le_sum
        intro γ _
        have ho:wU (rename incl f) (v γ) (ord C R γ) := by
          rw [hf]
          exact orderAt_ord C R γ
        exact (Polynomial.le_rootMultiplicity_iff hne).mpr (eliminant_order _ _ ho)
      _ = ∑ z∈C.Δ.image v,(QI f).rootMultiplicity z :=
        (Finset.sum_image (s :=C.Δ) (g:=v)
          (f := fun z :ao[X]=>(QI f).rootMultiplicity z) hinj).symm
      _≤(QI f).natDegree :=
        Polynomial.sum_rootMultiplicity_le_natDegree (W:= QI f) (C.Δ.image v)
      _≤(shape R).b^2 :=hdeg.trans (by
        rw [hB,pow_two]
        exact zBI _ (z7J _ _))
  · have he :excessWeight C R C.Δ=0:= by
      apply Finset.sum_eq_zero
      intro γ _
      have hle :=ord_le C R γ
      omega
    rw [he]
    exact Nat.zero_le _
end
end qsZufGc
end
