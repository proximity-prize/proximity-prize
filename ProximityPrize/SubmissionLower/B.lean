import ProximityPrize.SubmissionLower.G
import ProximityPrize.SubmissionLower.H
import ProximityPrize.SubmissionLower.I
import ProximityPrize.SubmissionLower.Z
import ProximityPrize.SubmissionLower.P
set_option Elab.async false
open _root_ renaming AddCommGroup→Au,Algebra→p6,Algebra.EssFiniteType→Kc,Algebra.FormallySmooth→ziC,Algebra.algebraMap→c9,Algebra.linearMap→ZJ,Algebra.smul_def→QL,Algebra.toModule→P7,Bool.false→sH,CommRing→pz,CommSemiring→qx,DecidableEq→G9,ExpChar→EK,Field→nq,Fin.castLE→Pv,Fin.prod_univ_six→RP,Fin.sum_univ_four→zmL,Fin.sum_univ_succ→WX,Fin.sum_univ_two→TZ,FiniteDimensional→X8,FiniteField.pow_card→Kv,Finset→nX,Finset.card_le_card→MK,Finset.card_sdiff_add_card_eq_card→R9,Finset.card_sdiff_of_subset→SL,Finset.card_univ→G1,Finset.mem_filter→Pk,Finset.mem_univ→vG,Finset.mul_sum→FV,Finset.prod_eq_zero→zue,Finset.prod_mul_distrib→Re,Finset.prod_pow_eq_pow_sum→Zf,Finset.range→t4,Finset.subset_univ→ziq,Finset.sum_congr→zg,Finset.sum_eq_zero→Qw,Finset.sum_le_sum→Yc,Finset.sum_range_succ→zpB,Finset.sup_le_iff→Y4,Finset.univ→yJ,Finsupp.add_apply→Hw,Finsupp.prod→KH,Finsupp.single→RD,Finsupp.sum→Un,Finsupp.sum_fintype→WD,Finsupp.weight_apply→Xg,Finsupp.weight_eq_sum→Mz,Finsupp.weight_single→ Il
open _root_ renaming Fintype→Av,Fintype.card→v9,Fintype.card_fin→u9,Function.Injective→p7,Function.Surjective→SU,Ideal→ oj,Ideal.Quotient.factorₐ→Nq,Ideal.Quotient.mk→yl,Ideal.Quotient.mk_surjective→Eg,Ideal.Quotient.mkₐ→Aa,Ideal.comap_comap→zg6,Ideal.comap_isPrime→Oc,Ideal.eq_top_of_isUnit_mem→G0,Ideal.map_map→Ml,Ideal.map_span→sS,Ideal.mem_span_singleton→UZ,Ideal.mk_ker→Kh,Ideal.mul_mem_right→LQ,Ideal.pow_le_pow_right→JM,Ideal.pow_mem_pow→Nj,Ideal.prod_mem_prod→XG,Ideal.span→nI,Ideal.subset_span→vk,Int.natCast_ediv→KA,Int.natCast_nonneg→Zi,Int.ofNat_sub→G4,Int.toNat_of_nonneg→JW,Irreducible→GB,IsCoprime→n5,IsDomain→y5,IsFractionRing.injective→LR,IsLocalRing.maximalIdeal→t3,IsLocalization→Df,IsLocalization.AtPrime.map_eq_maximalIdeal→XJ,IsLocalization.AtPrime.under_maximalIdeal→SD,IsLocalization.flat→zsF,IsLocalization.isPrime_of_isPrime_disjoint→Kl,IsLocalization.map_algebraMap_ne_top_iff_disjoint→GF,IsLocalization.map_units→Mw,IsLocalization.under_map_of_isPrime_disjoint→LO,IsRelPrime→ oZ,IsScalarTower.algebraMap_apply→Xu,IsScalarTower.toAlgHom→Xo,IsUnit→yo,K1.Ox→t5,K1.e9→v8,K1.node→qz,K1.twist→lI
open _root_ renaming KoalaBear.card_ext6→Te,LinearIndependent→Ar,LinearMap.finrank_le_finrank_of_injective→Z0,LinearMap.finrank_range_of_inj→VC,LinearMap.ker→p5,LinearMap.mulLeft→Vs,LinearMap.range_domRestrict→Mj,Localization.AtPrime→Ee,Matrix.cons_val_succ'→S1,Matrix.cons_val_zero'→NY,Module→yL,Module.Finite→ oy,Module.Finite.of_injective→zE,Module.Finite.of_surjective→G3,Module.finrank→lz,Module.finrank_eq_zero_of_subsingleton→Ww,Module.finrank_fintype_fun_eq_card→zvt,Module.length→qJ,Module.length_eq_of_surjective→WK,Monotone→zh,MulZeroClass.mul_zero→th,MvPolynomial→mD,MvPolynomial.C→lV,MvPolynomial.C_injective→ IU,MvPolynomial.X→cy,MvPolynomial.X_mem_restrictWeightedOrder→NX,MvPolynomial.as_sum→RJ,MvPolynomial.cappedDegreeMixedVolume→C4,MvPolynomial.coeff_monomial→Vz,MvPolynomial.coeff_sum→S2,MvPolynomial.commAlgEquiv→GY,MvPolynomial.degreeOf_X→G5,MvPolynomial.degreeOf_le_iff→PD,MvPolynomial.degreeOf_le_totalDegree→x7,MvPolynomial.degreeOf_mul_eq→G2,MvPolynomial.eval₂Hom→qM,MvPolynomial.eval₂Hom_C→PM,MvPolynomial.eval₂Hom_X'→Kz,MvPolynomial.eval₂Hom_monomial→X4,MvPolynomial.finSuccEquiv→NI,MvPolynomial.ker_map→Ye,MvPolynomial.le_totalDegree→Zg,MvPolynomial.map→ oz,MvPolynomial.map_C→wR,MvPolynomial.map_X→GR,MvPolynomial.map_injective→Pf,MvPolynomial.mem_support_iff→zuk,MvPolynomial.monomial→Up
open _root_ renaming MvPolynomial.monomial_eq→VO,MvPolynomial.mul_mem_restrictWeightedOrder→yU,MvPolynomial.quotientBidegreeLE→Pj,MvPolynomial.renameEquiv→Ok,MvPolynomial.renameEquiv_apply→Vl,MvPolynomial.restrictWeightedOrder→vh,MvPolynomial.restrictWeightedOrder_anti→MS,MvPolynomial.ringHom_ext→qU,MvPolynomial.ringHom_ext'→zey,MvPolynomial.sumAlgEquiv→VS,MvPolynomial.totalDegree→SW,MvPolynomial.two_mul_ncard_cappedDegreeExponents_fin_two→Lf,MvPolynomial.uniqueAlgEquiv→Kp,MvPolynomial.uniqueFactorizationMonoid→zhK,MvPolynomial.weightedTotalDegree→vZ,MvPolynomial.weightedTotalDegree_mul_le→Sd,MvPolynomial.weightedTotalDegree_one→WW,MvPolynomial.weightedTotalDegree_piSingle→Gr,Nat.add_assoc→zi,Nat.add_comm→Dz,Nat.add_le_add→NW,Nat.add_le_add_left→Gk,Nat.add_left_comm→ Iw,Nat.cast_add→xI,Nat.cast_mul→Gi,Nat.cast_ofNat→ In,Nat.cast_one→Np,Nat.choose_eq_zero_of_lt→zsx,Nat.eq_zero_of_le_zero→Zh,Nat.find_min'→TI,Nat.le_of_add_le_add_left→VH,Nat.le_succ→Ts,Nat.mul_comm→Gn,Nat.mul_le_mul_left→Cy,Nat.zero_le→N0,Nontrivial→UP,Pi.single→vi,Polynomial→u5,Polynomial.Bivariate.swap→ oq,Polynomial.Bivariate.swap_C→OJ,Polynomial.Bivariate.swap_X→G7,Polynomial.Bivariate.swap_map_C→LP,Polynomial.C→MO,Polynomial.C_injective→z7,Polynomial.X→lJ,Polynomial.X_ne_zero→xm,Polynomial.card_le_degree_of_subset_roots→Rm,Polynomial.coeff_eq_zero_of_natDegree_lt→PA
open _root_ renaming Polynomial.coeff_map→xu,Polynomial.coeff_zero→vw,Polynomial.eval_map_apply→ZK,Polynomial.eval_mul→qy,Polynomial.induction_on'→WY,Polynomial.mapRingHom→wA,Polynomial.map_C→TH,Polynomial.map_id→JQ,Polynomial.map_injective→HZ,Polynomial.map_map→EP,Polynomial.map_mul→vl,Polynomial.map_ne_zero_iff→zeI,Polynomial.map_zero→RC,Polynomial.mem_roots→Qy,Polynomial.natDegree_C_mul_le→Yi,Polynomial.natDegree_add_le→ IT,Polynomial.natDegree_le_of_dvd→Ef,Polynomial.natDegree_lt_iff_degree_lt→Gj,Polynomial.natDegree_map_eq_of_injective→KI,Polynomial.natDegree_map_le→Vq,Polynomial.natDegree_mul→u8,Polynomial.natDegree_sum_le_of_forall_le→XB,Polynomial.smul_eq_C_mul→G8,PrimeSpectrum→pG,PrincipalIdealRing.to_uniqueFactorizationMonoid→Xx,RingHom.comap_ker→Ob,RingHom.comp_apply→t7,RingHom.congr_fun→C5,RingHom.ext→F9,RingHom.id→Mk,RingHom.ker→sI,RingHom.ker_eq_comap_bot→Du,Set.image_insert_eq→Wm,Set.image_singleton→uz,Set.insert_subset_iff→Wl,Set.mem_ofPred_eq→FK,Set.range→ oY,Set.singleton_subset_iff→Yo,Submodule→uh,Submodule.add_mem→pQ,Submodule.equivMapOfInjective→Ze,Submodule.finrank_mono→zd,Submodule.finrank_sup_add_finrank_inf_eq→Nr,Submodule.map_mono→zzl,Submodule.mem_inf→zqd,Submodule.neg_mem→SM,Submodule.span→t6,Submodule.sub_mem→pL
open _root_ renaming Submodule.sum_mem→zo3,Submonoid→zm,Subtype.ext→zS,UniqueFactorizationMonoid→z9,WfDvdMonoid.isRelPrime_of_no_irreducible_factors→zgX,aR.symbols→Pc,add_comm→Dv,add_zero→uJ,akQ.lineMap→ oK,atd.Xn→yQ,congrArg→ oD,congrFun→zf,dvd_mul_left→Fa,dvd_mul_right→FQ,finSuccEquiv→FR,finrank_span_eq_card→Xp,frobenius→xL,gR.Principal.akc→vH,gR.Principal.assemble→zk,gR.Principal.az1→NZ,gR.Principal.degree_sub_lt→ztU,gT.Ambient→ ov,inferInstance→ II,isUnit_of_dvd_unit→G6,ite_eq_left→Qx,ite_eq_right→xW,ite_false→C9,iterateFrobenius→t9,iterateFrobenius_add→SC,iterateFrobenius_one→UY,le_max_left→Bf,le_max_right→FU,le_rfl→qG,map_add→qm,map_dvd→zc,map_mul→ ox,map_pow→wB,map_sum→t8,map_zero→pC,min_eq_right→Sv,mul_assoc→pU,mul_comm→p9,mul_left_cancel₀→wY,mul_left_comm→JK,mul_ne_zero→vj,mul_one→z8,mul_right_cancel₀→Zt,nonZeroDivisors→Ea
open _root_ renaming nonZeroDivisors.ne_zero→zyw,one_mul→zR,one_ne_zero→Pr,pow_ne_zero→Et,pow_one→uW,pow_succ→Dw,smul_eq_mul→Fz,wH.Lower→aU,wH.localColength→yB,xE.denominator→J4,zero_add→ze
set_option autoImplicit true
section
namespace Sr.aiz
open xE akL
noncomputable section
private theorem cG2 (w:Fin 4→ℕ) (d u:ℤ) :
  {e :Jp | (e.weight BU:ℤ)=d∧(e.weight w:ℤ)≤u}.Finite :=
 bGD fun _ h=>h.1
def columns (w:Fin 4→ℕ) (d u:ℤ) :nX Jp :=
 (cG2 w d u).toFinset
theorem aVS {w:Fin 4→ℕ} {d u:ℤ} {e :Jp} :
   e∈columns w d u↔(e.weight BU:ℤ)=d∧(e.weight w:ℤ)≤u :=
 (cG2 w d u).mem_toFinset
def alA (w:Fin 4→ℕ) (d u:ℤ) (i:Fin 4) (r :ℕ) :nX Jp :=
 (columns w d u).filter fun e=>e i< r
theorem aVR {w:Fin 4→ℕ} {d u:ℤ} {i:Fin 4} {r :ℕ} {e :Jp} :
  e∈alA w d u i r ↔
    (e.weight BU:ℤ)=d∧(e.weight w:ℤ)≤u∧e i< r := by
 simp only [alA,Pk,aVS,and_assoc]
theorem cEh (hc:a9U) (d u:ℤ) :
  ((columns Oq d u).card:ℤ)=gd d u:= by
 have h:columns Oq d u=adw d u:= by
  ext e
  exact aVS.trans azA.symm
 rw [h]
 exact hc d u
theorem cEd (w:Fin 4→ℕ) (d u:ℤ) (i:Fin 4) (r :ℕ) :
    ((alA w d u i r).card:ℤ)=((columns w d u).card:ℤ) -
      ((columns w (d - r) (u - r*(w i:ℤ))).card:ℤ) := by
  classical
  let tail:=(columns w d u).filter fun e=>r≤e i
  have hshift (e :Jp) :
      e∈columns w (d - r) (u - r*(w i:ℤ)) ↔
        e+Finsupp.single i r∈tail:= by
    simp only [tail,Pk,aVS,qm,Il,
      Hw ,Finsupp.single_eq_same,BU,Fz ,z8 ,
      xI,Gi]
    omega
  have htail: (columns w (d - r) (u - r*(w i:ℤ))).card=tail.card:= by
    apply Finset.card_bij (fun e _=>e+Finsupp.single i r)
    · exact fun e he=>(hshift e).mp he
    · intro e _ f _ hef
      exact add_right_cancel hef
    · intro e he
      have hr :r≤e i:=(Finset.mem_filter.mp he).2
      have hle :RD i r≤e :=Finsupp.single_le_iff.mpr hr
      have heq :e-Finsupp.single i r+Finsupp.single i r=e :=tsub_add_cancel_of_le hle
      exact ⟨_,(hshift _).mpr (by rwa [heq]),heq⟩
  have hdiff :columns w d u \ tail=alA w d u i r := by
    ext e
    by_cases he :e∈columns w d u <;> simp [tail,alA,he]
  have hp:=R9
    (show tail⊆columns w d u from Finset.filter_subset _ _)
  rw [hdiff,← htail] at hp
  omega
end
end Sr.aiz
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace bz4
noncomputable section
open Polynomial Matrix Finset gR
open scoped BigOperators
variable {F ι:Type} [nq F] [Av ι] [G9 ι]
omit [Av ι] [G9 ι] in
theorem fWB [G9 F] (D:nX ι) (G:nX F) (q:ι→F[X]) (d:ℕ)
  (hd:0<d) (hne : ∀ i∈D,q i≠0) (hdeg : ∀ i∈D,(q i).natDegree≤d)
  (hroots : ∀ γ∈G,d≤(D.filter (fun i=>(q i).eval γ=0)).card) :
  G.card≤D.card:= by
 classical
 have hi (i:ι) (hi:i∈D) : (G.filter (fun γ=>(q i).eval γ=0)).card≤d:= by
  apply (le_trans ?_ (hdeg i hi))
  apply Rm
  intro γ hγ
  exact (Qy (hne i hi)).mpr (Finset.mem_filter.mp hγ).2
 have hswap: (∑ γ∈G,(D.filter (fun i=>(q i).eval γ=0)).card) =
    ∑ i∈D,(G.filter (fun γ=>(q i).eval γ=0)).card:= by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm
 have hc:G.card*d≤D.card*d:= calc
  G.card*d = ∑ _γ∈G,d:= by simp [Gn]
  _ ≤ ∑ γ∈G,(D.filter (fun i=>(q i).eval γ=0)).card:=Yc hroots
  _ = ∑ i∈D,(G.filter (fun γ=>(q i).eval γ=0)).card:=hswap
  _ ≤ ∑ _i∈D,d:=Yc hi
  _=D.card*d:= by simp [Gn]
 exact Nat.le_of_mul_le_mul_right hc hd
omit [Av ι] [G9 ι] in
theorem ecV (x u v :ι→F) (k :ℕ) (G:nX F)
   (E :nX ι) (P:F→F[X]) (S:F→nX ι)
   (hP : ∀ γ∈G,(P γ).degree<k)
   (hout : ∀ γ∈G,∀ i,i∉E→u i+γ*v i=(P γ).eval (x i))
   (havoid : ∀ γ∈G,∀ i∈S γ,i∉E)
   (hbad : ∀ γ∈G,¬ (NM x u k (S γ)∧NM x v k (S γ))) :
   G.card≤1 := by
 classical
 apply Finset.card_le_one.mpr
 intro γ hγ ζ hζ
 by_contra hne
 have hz :ζ-γ≠0:=sub_ne_zero.mpr (Ne.symm hne)
 let V:=(ζ-γ)⁻¹•(P ζ-P γ)
 let U:=P γ-γ•V
 have hV:V.degree<k :=
   Principal.aNc _ (ztU (hP ζ hζ) (hP γ hγ))
 have hU:U.degree<k :=
   ztU (hP γ hγ) (Principal.aNc _ hV)
 have hVe (i:ι) (hi:i∉E) :V.eval (x i)=v i:= by
   simp only [V,eval_smul,eval_sub,Fz ,← hout ζ hζ i hi,← hout γ hγ i hi]
   field_simp [hz]
   ring
 have hUe (i:ι) (hi:i∉E) :U.eval (x i)=u i:= by
   simp only [U,eval_sub,eval_smul,Fz ,hVe i hi,← hout γ hγ i hi]
   ring
 exact hbad γ hγ
   ⟨⟨U,hU,fun i hi=>hUe i (havoid γ hγ i hi)⟩,
     ⟨V,hV,fun i hi=>hVe i (havoid γ hγ i hi)⟩⟩
theorem dU5 (x u v :ι→F) (hx :p7 x)
    (k l t α:ℕ) (hsize :k+l+t=v9 ι) (hα:α<l)
    (hrank :Bx.adJ (QO x u v l t)= α)
    (Γ:nX F) (hΓ : ∀ γ∈Γ,Principal.akD x u v k (k+l) γ) :
    Γ.card≤v9 ι + α:= by
  classical
  let M:= QO x u v l t
  let φ:=c9 F[X] (Bx.lN F)
  have hφ:=LR F[X] (Bx.lN F)
  obtain ⟨B⟩:=zQ.a3O φ M α hrank
  let Δ:=(zQ.pivot B).det
  have hΔdeg:Δ.natDegree≤α:= by
    simpa [Δ] using zQ.aVV φ M α B (fun _=>1)
      (bHF x u v l t)
  let G:=Γ.filter (fun γ=>Δ.eval γ≠0)
  let exceptional:=Γ.filter (fun γ=>Δ.eval γ=0)
  have hExceptional:exceptional.card≤α:= by
    apply (le_trans ?_ hΔdeg)
    apply Rm
    intro γ hγ
    exact (Qy B.minor_ne).mpr (Finset.mem_filter.mp hγ).2
  have hsplit :exceptional.card+G.card=Γ.card :=
    Finset.card_filter_add_card_filter_not (s :=Γ) (p:= fun γ=>Δ.eval γ=0)
  suffices hG:G.card≤v9 ι by omega
  by_cases hG0:G.Nonempty
  · have hdata : ∀ γ:F,∃ (P:F[X]) (S:nX ι),γ∈G →
        k+l≤S.card∧P.degree<k ∧
          (∀ i∈S,P.eval (x i)=u i+γ*v i) ∧
          ¬ (NM x u k S∧NM x v k S) := by
      intro γ
      by_cases hg:γ∈G
      · obtain ⟨S,hS,⟨P,hP,hp⟩,hb⟩:=hΓ γ (Finset.mem_filter.mp hg).1
        exact ⟨P,S,fun _=>⟨hS,hP,hp,hb⟩⟩
      · exact ⟨0,∅,fun h=>(hg h).elim⟩
    choose P S hPS using hdata
    let E :F→nX ι :=
      fun γ=>univ.filter (fun i=>u i+γ*v i≠(P γ).eval (x i))
    have her (γ:F) (i:ι) :i∈E γ↔u i+γ*v i≠(P γ).eval (x i) := by
      simp [E]
    have hsizeE (γ:F) (hg:γ∈G) : (E γ).card≤t:= by
      have hsub:E γ⊆univ \ S γ:= by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨vG _,fun his=>(her γ i).mp hi
          (((hPS γ hg).2.2.1 i his).symm)⟩
      have hle :=MK hsub
      rw [SL (ziq _),G1] at hle
      have :=(hPS γ hg).1
      omega
    have hactual (γ:F) (hg:γ∈G) : (E γ).card= α:= by
      have hr :=zQ.buH φ hφ M α B γ (Finset.mem_filter.mp hg).2
      change ((QO x u v l t).map (evalRingHom γ)).rank= α at hr
      rw [d3p x u v hx γ (P γ) k l t (hPS γ hg).2.1 hsize.le (E γ)
        (by have :=hsizeE γ hg; omega)
        (fun i hi=> by simpa only [her,not_not] using hi)
        (fun i hi=>(her γ i).mp hi)] at hr
      omega
    let H :nX ι:=univ.filter (fun i => ∀ γ∈G,i∈E γ)
    have hH (i:ι) :i∈H ↔ ∀ γ∈G,i∈E γ:= by simp [H]
    have hsub (γ:F) (hg:γ∈G) :H⊆E γ :=
      fun i hi=>(hH i).mp hi γ hg
    obtain ⟨γ₀,hγ₀⟩:=hG0
    have hHle :H.card≤α:= by
      rw [← hactual γ₀ hγ₀]
      exact MK (hsub γ₀ hγ₀)
    have hat :α≤t:=(hactual γ₀ hγ₀) ▸ hsizeE γ₀ hγ₀
    let d:= α - H.card
    have hcard (γ:F) (hg:γ∈G) : (E γ \ H).card=d:= by
      rw [SL (hsub γ hg),hactual γ hg]
    by_cases hd:0<d
    · let f :=mL x H
      let u' := fun i=>f.eval (x i)*u i
      let v' := fun i=>f.eval (x i)*v i
      let M' := QO x u' v' d d
      let A:=M'.submatrix id Fin.castSucc
      let b:= fun i=>M' i (Fin.last d)
      let q:= fun i:ι => ∑ j:Option (Fin d),
        C (x i^(j.elim d Fin.val))*apT.vector A b j
      have hq (γ:F) (hg:γ∈G) (i:ι) :
          (q i).eval γ=A.det.eval γ*(mL x (E γ \ H)).eval (x i) ∧
            A.det.eval γ≠0:= by
        have hdeg: (f*P γ).degree<(k+H.card:ℕ) := by
          have hfdeg:f.degree=(H.card:ℕ) := by
            rw [degree_eq_natDegree (S8 x H).ne_zero,ZQ]
          have h:=(hPS γ hg).2.1
          exact (degree_mul_le _ _).trans_lt (by
            rw [hfdeg,xI,Dv (k :WithBot ℕ)]
            exact WithBot.add_lt_add_left WithBot.coe_ne_bot h)
        have hval (a :ι) :u' a+γ*v' a-(f*P γ).eval (x a) =
            f.eval (x a)*(u a+γ*v a-(P γ).eval (x a)) := by
          simp only [u',v',qy]
          ring
        apply dNc x u' v' hx γ (f*P γ) (k+H.card) d hdeg
          (by dsimp [d]; omega) (E γ \ H) (hcard γ hg) _ _ i
        · intro a ha
          apply sub_eq_zero.mp
          rw [hval]
          by_cases hh:a∈H
          · simp [f,arK x H a hh]
          · have hno:a∉E γ:= fun he=>ha (Finset.mem_sdiff.mpr ⟨he,hh⟩)
            have heq :u a+γ*v a=(P γ).eval (x a) := by
              simpa only [her,not_not] using hno
            simp [heq]
        · intro a ha
          obtain ⟨he,hh⟩:=Finset.mem_sdiff.mp ha
          apply sub_ne_zero.mp
          rw [hval]
          exact vj (fun hz=>hh ((Principal.aVH x hx H a).mp hz))
            (sub_ne_zero.mpr ((her γ a).mp he))
      let D:=(univ :nX ι) \ H
      refine (fWB D G q d hd ?_ ?_ ?_).trans (Finset.card_le_univ D)
      · intro i hi
        have hni:=(Finset.mem_sdiff.mp hi).2
        obtain ⟨γ,hg,he⟩ : ∃ γ∈G,i∉E γ:= by
          by_contra hnone
          apply hni
          apply (hH i).mpr
          intro γ hg
          by_contra he
          exact hnone ⟨γ,hg,he⟩
        intro hz
        obtain ⟨heval,hdet⟩:=hq γ hg i
        rw [hz,eval_zero] at heval
        have hr :=(mul_eq_zero.mp heval.symm).resolve_left hdet
        exact he (Finset.mem_sdiff.mp ((Principal.aVH x hx _ i).mp hr)).1
      · intro i _
        apply XB
        intro j _
        refine (Yi _ _).trans ?_
        calc
          _ ≤ ∑ _r :Fin d,1 :=apT.bPI A b (fun _=>1)
              (fun r c=>bHF x u' v' d d r (Fin.castSucc c))
              (fun r=>bHF x u' v' d d r (Fin.last d)) j
          _=d:= by simp
      · intro γ hg
        rw [← hcard γ hg]
        apply MK
        intro i hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨vG _,(Finset.mem_sdiff.mp hi).2⟩,?_⟩
        rw [(hq γ hg i).1,arK x _ i hi,th]
    · have heq (γ:F) (hg:γ∈G) :E γ=H := by
        apply (Finset.eq_of_subset_of_card_le (hsub γ hg) ?_).symm
        rw [hactual γ hg]
        dsimp [d] at hd
        omega
      have hf :=ecV x u v k G H P S
        (fun γ hg=>(hPS γ hg).2.1)
        (fun γ hg i hi=> by
          rw [← heq γ hg,her,not_not] at hi
          exact hi)
        (fun γ hg i hi hs=>(her γ i).mp (heq γ hg ▸ hs) (((hPS γ hg).2.2.1 i hi).symm))
        (fun γ hg=>(hPS γ hg).2.2.2)
      omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hG0]
end
end bz4
end
section
namespace aFM
open xE GI
open scoped BigOperators
private theorem b9F (u:ℤ) : (avC (u+1).toNat :ℤ)=xY u:= by
 by_cases hu:u<0
 · simp [avC,xY,hu,show (u+1).toNat=0 by omega]
 lift u to ℕ using (by omega)
 rw [show ((u:ℤ)+1).toNat=u+1 by omega]
 simp only [avC,xY,not_lt.mpr (Zi _),C9,Nat.cast_succ]
 change ((↑(u*(u*(2*u+21)+66)/72 :ℕ) :ℤ)+1)= _
 simp only [KA,Gi ,xI,In]
private def aIX (ab:ℕ×ℕ) :ℤ:=(ab.1 :ℤ)-ab.2
private theorem bDu (d:ℕ) (u:ℤ) :
   aIX (aM3 d (u+1).toNat)=aUK (d:ℤ) u:= by
 by_cases hu:u<0
 · simp [aM3,aIX,avC,aUK,hu,show (u+1).toNat=0 by omega]
 let v :=min u (3*(d:ℤ))
 have hvDef :min u (3*(d:ℤ))=v :=rfl
 have hv :0≤v := by dsimp [v]; omega
 have hm:Nat.min (u+1).toNat (3*d+1)=(v+1).toNat := by
   change min (u+1).toNat (3*d+1)=(v+1).toNat
   dsimp [v]
   omega
 have ha (k :ℕ) : (v+1).toNat - d - k=(v-(d:ℤ) - k+1).toNat := by omega
 have hb (k :ℕ) : (v+1).toNat - 2*d - k=(v - 2*(d:ℤ) - k+1).toNat := by omega
 have h₁: ((v+1).toNat≤d+1)↔v≤(d:ℤ) := by omega
 have h₂: ((v+1).toNat≤2*d+3)↔v≤2*(d:ℤ)+2 := by omega
 simp only [aM3,aUK,not_lt.mpr (Zi d),hu,decide_false,
   Bool.false_or,Bool.false_eq_true,C9,hm,hvDef,h₁,h₂]
 change aIX (if v≤(d:ℤ) then _ else _)=(if v≤(d:ℤ) then _ else _)
 by_cases hsmall:v≤(d:ℤ)
 · simp only [Qx hsmall,aIX,Nat.cast_zero,sub_zero,b9F]
 · rw [xW hsmall,xW hsmall]
   by_cases hlarge :v≤2*(d:ℤ)+2
   · simp only [Qx hlarge,aIX,ha,xI,In,Np,b9F]
     ring
   · simp only [xW hlarge,aIX,ha,hb,xI,In,Np,b9F]
     ring
private theorem c6y (f :ℕ→ℕ) (n:ℕ) :
   a7s f n = ∑ k∈t4 n,f k := by
 induction n with
 | zero=>simp [a7s]
 | succ n ih=>rw [a7s,Finset.sum_range_succ,ih]
end aFM
end
section
set_option maxHeartbeats 1000000
namespace bzy
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem efH {k σ τ:Type*} [nq k] [Finite σ]
    (J:oj (mD σ k)) (hJ:J.IsPrime)
    (s :nX τ) (c:τ) (hc:c∈s)
    (u:τ→mD σ k) (hu:u c=1) :
    let F:=FractionRing (mD τ k)
    let ι:mD σ k →+* mD σ F:=oz (c9 k F)
    let g:mD σ F :=
      ∑ m∈s,lV (c9 (mD τ k) F (cy m))*ι (u m)
    let L:=J.map ι ⊔ nI {g}
    (affineHilbertPolynomial L).natDegree≤(affineHilbertPolynomial J).natDegree - 1 ∧
      (L = ⊤ ∨ L.IsPrime∧L.comap ι=J) := by
  classical
  let _:J.IsPrime :=hJ
  let R:=mD σ k
  let A:=R ⧸ J
  let q:R →+* A:=yl J
  let D:=mD τ k
  let F:=FractionRing D
  let T:=mD σ D
  let V:=mD σ F
  let ι₀:R →+* T:=oz lV
  let localize :T →+* V:=c9 T V
  let ι:R →+* V:=oz (c9 k F)
  let G:T := ∑ m∈s,lV (cy m)*ι₀ (u m)
  let P:=J.map ι₀
  let H :=P ⊔ nI {G}
  let M:zm T:=(Ea D).map lV
  have hloc:Df M V:=MvPolynomial.isLocalization (Ea D) F
  have hι:localize.comp ι₀=ι:= by
    apply qU <;> intro x
    · change oz (c9 D F) (oz lV (lV x)) =
        oz (c9 k F) (lV x)
      simp only [wR] <;> rfl
    · change oz (c9 D F) (oz lV (cy x)) =
        oz (c9 k F) (cy x)
      simp only [GR]
  have hG:localize G = ∑ m∈s,lV (c9 D F (cy m))*ι (u m) := by
    simp only [G,t8 ,ox]
    apply zg rfl
    intro m _
    have hm:localize (ι₀ (u m))=ι (u m) :=C5 hι (u m)
    rw [show localize (lV (cy m))=lV (c9 D F (cy m)) from wR _ _,hm]
  have hP:P.map localize=J.map ι:= by
    rw [show P=J.map ι₀ from rfl,Ml,hι]
  dsimp only
  rw [← hG]
  let e :=(GY k σ τ).toRingEquiv
  let move :T →+* mD τ A:=(oz q).comp e.toRingHom
  have he :e.toRingHom.comp ι₀=MvPolynomial.C:= by
    apply qU
    · intro x
      change GY k σ τ (oz lV (lV x))= _
      rw [wR,commAlgEquiv_C,wR]
    · intro i
      change GY k σ τ (oz lV (cy i))= _
      rw [GR,commAlgEquiv_X]
  have hmι (x :R) :move (ι₀ x)=lV (q x) := by
    change oz q (e (ι₀ x))= _
    rw [show e (ι₀ x)=lV x from C5 he x,wR]
  have hmC (d:D) :move (lV d)=oz (q.comp lV) d:= by
    change oz q (GY k σ τ (lV d))= _
    rw [commAlgEquiv_C,MvPolynomial.map_map]
  have hsurj:SU move :=
    (MvPolynomial.map_surjective _ Eg).comp e.surjective
  have hker :sI move=P:= by
    change sI ((oz q).comp e.toRingHom)=J.map ι₀
    rw [← Ob ,Ye,show sI q=J from Kh,
      ← he,← Ml,Ideal.comap_map_of_bijective e.toRingHom e.bijective]
  have hmoveG:move G = ∑ m∈s,cy m*lV (q (u m)) := by
    simp only [G,t8 ,ox ,hmC,hmι,GR]
  obtain ⟨hne,f,hf,hfC⟩ :=
    d0U s c hc (fun m=>q (u m)) (by simp [hu])
  rw [← hmoveG] at hne hf
  have hPprime :P.IsPrime := by
    rw [← hker,Du]
    exact Oc move _
  have hPdisj:Disjoint (M:Set T) (P:Set T) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨d,hd,rfl⟩ hm
    have hn:move (lV d)≠0:= by
      rw [hmC]
      simpa only [pC] using
        (Pf _ (q.comp lV).injective).ne (zyw hd)
    exact hn (RingHom.mem_ker.mp (hker.symm ▸ hm))
  have hPext: (J.map ι).IsPrime :=
    hP ▸ Kl M V P hPprime hPdisj
  have hproper :localize G∉J.map ι:= by
    rw [← hP]
    change G∉(P.map (c9 T V)).under T
    rw [LO M V hPprime hPdisj,← hker]
    exact hne
  have hdegree :=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hPext hproper qG).1
  rw [Ey.ZI J] at hdegree
  refine ⟨hdegree,?_⟩
  have hH :H.map localize=J.map ι ⊔ nI {localize G} := by
    simp only [H,Ideal.map_sup,hP,sS ,uz]
  rw [← hH]
  by_cases htop:H.map localize = ⊤
  · exact Or.inl htop
  have hHdisj:=(GF M V H).mp htop
  have hkerH :sI (f.comp move)=H := by
    rw [← Ob ,hf,← uz (f :=move) (a :=G),
      ← sS ,Ideal.comap_map_of_surjective _ hsurj,
      ← Du,hker,sup_comm]
  have hHprime :H.IsPrime := by
    rw [← hkerH,Du]
    exact Oc (f.comp move) _
  refine Or.inr ⟨Kl M V H hHprime hHdisj,?_⟩
  change (H.map localize).comap ι=J
  rw [← hι,← zg6]
  change ((H.map (c9 T V)).under T).comap ι₀=J
  rw [LO M V hHprime hHdisj,← hkerH]
  ext x
  change f (move (ι₀ x))=0↔x∈J
  rw [hmι,show f (lV (q x))=lV (q x) from C5 hfC (q x)]
  constructor
  · intro hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (IU _ _ (hz.trans (pC lV).symm))
  · intro hx
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx,pC]
open aR dN BO GJ axe
theorem proof :axe.c1 := by
  intro J h hJ _
  let c:uL h:= fun _=>0
  have hc:c∈Bz h:= by simp [c,Bz]
  let u:uL h→GeoJets := fun m => ∏ i:Fin 4,cy i^(m i).val
  have hu:u c=1 := by simp [u,c]
  have hg: (∑ m∈Bz h,
      lV (c9 (mD (uL h) GeoField) (dV h) (cy m)) *
        aeg h (u m))=adK h:= by
    simp [u,aeg,adK]
  have hs :=efH J hJ (Bz h) c hc u hu
  dsimp only at hs
  simp only [aeg] at hg
  rw [hg] at hs
  exact hs
end
end bzy
end
section
namespace aw6
noncomputable section
open Polynomial K1
structure Direction (u:e9) (deleted:nX I) where
 den:K[X]
 U:K[X]
 V:K[X]
 A:Fin 2→K[X]
 out:Fin 2→Fin 2→K[X]
 den_nodes : ∀ i,den.eval (node i)≠0
 U_ne :U≠0
 V_ne :V≠0
 U_dvd:U∣den
 coprime :n5 U V
 phase :U*den.map lI=V*den
 degrees_eq :V.natDegree=U.natDegree
 primitive :n5 (A 0) (A 1)
 height:U.natDegree+uO (A 0) (A 1)+deleted.card≤32680
 out_degree : ∀ i j,(out i j).degree <
   (131072+U.natDegree+uO (A 0) (A 1) :ℕ)
 nodes : ∀ x∉deleted,∀ i j,(out i j).eval (node x) =
   U.eval (node x)*((A i).map lI).eval (node x)*u j x -
   V.eval (node x)*(A j).eval (node x)*lI (u i x)
variable {u:e9} {deleted:nX I}
def Direction.s (F:Direction u deleted) :=uO (F.A 0) (F.A 1)
def Direction.amp (F:Direction u deleted) (γ:K) :=F.A 0+C γ*F.A 1
end
end aw6
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace aw6
noncomputable section
open Polynomial K1 gR ProximityPrize.Benchmark
open scoped BigOperators
theorem ayM {P Q:K[X]} (h:P∣Q) {a :K}
  (hu:Q.eval a≠0) :P.eval a≠0:= by
 obtain ⟨L,rfl⟩:=h
 rw [qy] at hu
 exact left_ne_zero_of_mul hu
private def conjugate :ℕ→K[X]→K[X]
 | 0,P=>P
 | n+1,P=>(conjugate n P).map twist
private theorem bYB (P:K[X]) :conjugate 6 P=P:= by
  have iter (n:ℕ) :conjugate n P=P.map (t9 K p n) := by
    induction n with
    | zero=>simp [conjugate]
    | succ n ih =>
      rw [conjugate,ih,EP ,Dv n 1,
        SC K p 1 n,UY ,lI]
  have card:v9 K=p^6:=Te
  have hs :t9 K p 6=Mk K:= by
    apply F9
    intro x
    change x^p^6=x
    rw [← card]
    exact Kv x
  rw [iter,hs,JQ]
theorem dip (i:I) :lI (node i)=node i:=Native.ahU i
theorem auR (P:K[X]) (i:I) : (P.map lI).eval (node i)=lI (P.eval (node i)) :=
 kL.aC4 lI P (node i) (dip i)
private theorem dOZ {W:K[X]} (hu : ∀ i,W.eval (node i)≠0)
   (n:ℕ) (i:I) : (conjugate n W).eval (node i)≠0:= by
 induction n with
 | zero=>exact hu i
 | succ n ih=>rw [conjugate,auR]; exact (map_ne_zero twist).mpr ih
private theorem dOY {W T:K[X]} (h:W∣T) (ht:T.map lI=T)
   (n:ℕ) :conjugate n W∣T:= by
 induction n with
 | zero=>exact h
 | succ n ih =>
   rw [conjugate,← ht]
   exact zc (wA lI) ih
theorem cVy (W:K[X]) (hu : ∀ i,W.eval (node i)≠0) :
   ∃ L C₀:K[X],L=W*C₀∧L.map lI=L∧(∀ i,L.eval (node i)≠0) ∧
     ∀ N :K[X],(W*N).map lI=W*N → ∃ S:K[X],S.map lI=S∧N=C₀*S:= by
 classical
 let f := fun j:Fin 6=>conjugate j.val W
 let rawL:=Finset.univ.lcm f
 let L:=normalize rawL
 have hdiv (j:Fin 6) :f j∣L :=
   dvd_normalize_iff.mpr (Finset.dvd_lcm (vG j))
 have hnode (i:I) :L.eval (node i)≠0:= by
   apply ayM (normalize_dvd_iff.mpr (Finset.lcm_dvd_prod yJ f))
   rw [eval_prod]
   exact Finset.prod_ne_zero_iff.mpr (fun j _=>dOZ hu j.val i)
 have hne :L≠0:= fun h=>hnode 0 (by rw [h,eval_zero])
 have hm:L.Monic:=monic_normalize (by simpa [L] using hne)
 have hcross :L∣L.map twist:= by
   apply normalize_dvd_iff.mpr
   apply Finset.lcm_dvd
   intro j _
   have step (i:Fin 6) :conjugate (i.val+1) W∣L.map twist :=
     zc (wA lI) (hdiv i)
   by_cases hz :j.val=0
   · change conjugate j.val W∣ _
     rw [hz]
     change W∣ _
     simpa only [show (5:Fin 6).val+1=6 by decide,bYB] using step 5
   · let i:Fin 6:=⟨j.val-1,by omega⟩
     have hi:i.val+1=j.val := by dsimp [i]; omega
     simpa only [hi,f] using step i
 have hfix :L.map lI=L:=(eq_of_dvd_of_natDegree_le_of_leadingCoeff hcross
   Vq (hm.trans (hm.map lI).symm)).symm
 obtain ⟨C₀,hc⟩:=hdiv 0
 change L=W*C₀ at hc
 refine ⟨L,C₀,hc,hfix,hnode,?_⟩
 intro N ht
 have hL:L∣W*N :=normalize_dvd_iff.mpr (Finset.lcm_dvd (fun j _ =>
   dOY (FQ W N) ht j.val))
 obtain ⟨S,hs⟩:=hL
 refine ⟨S,?_,?_⟩
 · apply wY hne
   rw [hs,vl,hfix] at ht
   exact ht
 · have hW:W≠0:= fun h=>hu 0 (by rw [h,eval_zero])
   apply wY  hW
   simpa only [hc,pU ] using hs
variable {u:e9} {deleted:nX I} {F:Direction u deleted} {η γ:K}
 {anchor :B5 u η}
end
end aw6
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace aw6
noncomputable section
open Polynomial K1 gR ProximityPrize.Benchmark
theorem bpp {deleted:nX I} {P Q:K[X]} {d:ℕ}
   (hroom:d+deleted.card≤262144) (hP:P.natDegree<d) (hQ:Q.natDegree<d)
   (hn : ∀ i∉deleted,P.eval (node i)= Q.eval (node i)) :P= Q:= by
 classical
 apply sub_eq_zero.mp
 by_contra hne
 have hcount:=kL.agd node IRSProfile.domain.injective (P-Q) hne
   (yJ \ deleted) (by
     intro i hi
     rw [eval_sub,hn i (Finset.mem_sdiff.mp hi).2,sub_self])
 rw [SL (ziq _),G1 ,
   IRSProfile.card_index] at hcount
 have h:=natDegree_sub_le P Q
 omega
theorem aDT {P:K[X]} {n:ℕ} (hn:0<n) (hd:P.degree<n) :
   P.natDegree<n:= by
 by_cases h:P=0
 · simpa [h] using hn
 exact (Gj h).mpr hd
private theorem gCg {A:Fin 2→K[X]} (hp:n5 (A 0) (A 1)) :
   ∃ j,A j≠0∧(A j).natDegree=max (A 0).natDegree (A 1).natDegree := by
 by_cases h0:A 0=0
 · exact ⟨1,hp.ne_zero_or_ne_zero.resolve_left (not_not.mpr h0),by simp [h0]⟩
 by_cases h1 :A 1=0
 · exact ⟨0,h0,by simp [h1]⟩
 rcases le_total (A 0).natDegree (A 1).natDegree with h|h
 · exact ⟨1,h1,(max_eq_right h).symm⟩
 · exact ⟨0,h0,(max_eq_left h).symm⟩
private theorem a1X (deleted:nX I) (w:I→K) (A P:Fin 2→K[X]) (d s :ℕ)
   (hs :max (A 0).natDegree (A 1).natDegree=s) (hcop:n5 (A 0) (A 1))
   (hpos :0<d) (hroom:d+2*s+deleted.card≤262144)
   (hP : ∀ j,(P j).natDegree<d+s)
   (hn : ∀ i∉deleted,∀ j,(P j).eval (node i)=(A j).eval (node i)*w i) :
   ∃ leftLift:K[X],leftLift.natDegree<d ∧ ∀ i∉deleted,leftLift.eval (node i)=w i:= by
 have hA0: (A 0).natDegree≤ s :=hs ▸ Bf _ _
 have hA1 : (A 1).natDegree≤ s :=hs ▸ FU _ _
 have afu:A 1*P 0=A 0*P 1 := by
   apply bpp hroom
   · exact natDegree_mul_le.trans_lt (by have :=hP 0; omega)
   · exact natDegree_mul_le.trans_lt (by have :=hP 1; omega)
   · intro i hi
     simp only [qy ,hn i hi]
     ring
 obtain ⟨j,hj,hjs⟩:=gCg hcop
 obtain ⟨x,y,hxy⟩:=hcop
 let leftLift:=x*P 0+y*P 1
 have eqj:leftLift*A j=P j:= by
   unfold leftLift
   fin_cases j
   · change (x*P 0+y*P 1)*A 0=P 0
     linear_combination P 0*hxy - y*afu
   · change (x*P 0+y*P 1)*A 1=P 1
     linear_combination P 1*hxy + x*afu
 refine ⟨leftLift,?_,?_⟩
 · by_cases hY:leftLift=0
   · simpa [hY] using hpos
   have hd:=u8 hY hj
   rw [eqj,hjs,hs] at hd
   have :=hP j
   omega
 · intro i hi
   have h:=oD (eval (node i)) hxy
   simp only [eval_add,qy ,eval_one] at h
   simp only [leftLift,eval_add,qy ,hn i hi]
   linear_combination w i*h
end
end aw6
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace aw6
noncomputable section
open Polynomial K1 gR
private theorem cIe {E Q P c a S:K[X]} {z :K} (hz :z≠0)
  (reduced:n5 Q E) (hid :E*P - C z*Q=c*a*S) :
  IsCoprime E c:= by
 obtain ⟨x,y,hxy⟩:=reduced
 have inv :C z⁻¹*C z=(1 :K[X]) := by rw [← C_mul,inv_mul_cancel₀ hz,C_1]
 have eqQ:Q=C z⁻¹*(E*P - c*a*S) := by
  have he :C z*Q=E*P - c*a*S:= by linear_combination -hid
  rw [← he,← pU,inv,zR]
 rw [eqQ] at hxy
 exact ⟨x*C z⁻¹*P+y,-(x*C z⁻¹*a*S),by linear_combination hxy⟩
end
end aw6
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace cxN
noncomputable section
open Polynomial K1 ProximityPrize.Benchmark
section Cyclic
variable {F:Type*} [nq F] {q:ℕ} [EK F q]
private def conjugate (q n:ℕ) [EK F q] (P:F[X]) :F[X] :=
 P.map (t9 F q n)
private theorem cHJ (P:F[X]) :conjugate q 0 P=P:= by simp [conjugate]
private theorem cHI (n:ℕ) (P:F[X]) :
  (conjugate q n P).map (xL F q)=conjugate q (n+1) P:= by
 rw [conjugate,conjugate,EP ,Dv n 1,
  SC F q 1 n,UY]
variable [Av F]
private theorem bYB (card:v9 F=q^6) (P:F[X]) :
  conjugate q 6 P=P:= by
 have hs :t9 F q 6=Mk F:= by
  apply F9
  intro x
  change x^q^6=x
  rw [← card]
  exact Kv x
 rw [conjugate,hs,JQ]
private def weights {S:Type*} [qx S] (A B:ℕ→S) (j:Fin 6) :S :=
 ∏ i:Fin 6,if i.val<j.val then A i.val else B i.val
private theorem gMq {S:Type*} [qx S] (f :S →+* S) (A B:ℕ→S)
  (ha : ∀ n,f (A n)=A (n+1)) (hb : ∀ n,f (B n)=B (n+1))
  (hB:B 6=B 0)
  (h: (∏ i:Fin 6,A i.val) = ∏ i:Fin 6,B i.val) (j:Fin 6) :
  A 0*f (weights A B j)=B 0*weights A B (j+1) := by
 rw [RP ,RP] at h
 change A 0*A 1*A 2*A 3*A 4*A 5=B 0*B 1*B 2*B 3*B 4*B 5 at h
 fin_cases j <;> simp only [weights,RP ,Fin.add_def] <;>
  norm_num [ha,hb,hB]
 all_goals first | ac_rfl | (rw [← h]; ac_rfl)
private theorem eel (card:v9 F=q^6) (x :F) (j:Fin 6) :
   xL F q (x^q^j.val)=x^q^(j+1).val := by
 have hpow:xL F q (x^q^j.val)=x^q^(j.val+1) := by
   change (x^q^j.val)^q= _
   rw [← pow_mul,Dw q j.val]
 rw [hpow]
 by_cases hj:j.val=5
 · have hj' : j=5:=Fin.ext hj
   rw [hj',show (5:Fin 6)+1=0 by decide]
   change x^q^6=x^q^0
   rw [pow_zero,uW,← card,Kv]
 · have hv : (j+1).val=j.val+1 := by
     change (j.val+1) % 6=j.val+1
     exact Nat.mod_eq_of_lt (by omega)
   rw [hv]
private theorem dWA (card:v9 F=q^6) (hq:1<q)
    {a b:F[X]} (hb:b≠0)
    (h: (∏ i:Fin 6,conjugate q i.val a) = ∏ i:Fin 6,conjugate q i.val b) :
    ∃ Q:F[X],Q≠0∧a*Q.map (xL F q)=b*Q:= by
  classical
  let W:=weights (fun n=>conjugate q n a) (fun n=>conjugate q n b)
  let S:u5 F[X] := ∑ j:Fin 6,monomial (q^j.val) (W j)
  have hinj:p7 (fun j:Fin 6=>q^j.val) := by
    intro i j hij
    exact Fin.ext ((pow_right_injective₀ (by omega :0<q) (ne_of_gt hq)) hij)
  have hW:W 0≠0:= by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    change (if j.val<0 then conjugate q j.val a else conjugate q j.val b)≠0
    rw [xW (Nat.not_lt_zero _)]
    exact (zeI (t9 F q j.val).injective).mpr hb
  have hS:S≠0:= by
    intro hz
    apply hW
    have hc:=oD (fun P:u5 F[X]=>P.coeff (q^(0:Fin 6).val)) hz
    simpa only [S,finsetSum_coeff,coeff_monomial,hinj.eq_iff,Finset.sum_ite_eq',
      vG,ite_true,vw] using hc
  have hdeg:S.natDegree≤q^5:= by
    apply XB
    intro j _
    exact natDegree_monomial_le _ |>.trans
      (Nat.pow_le_pow_right (by omega) (by omega :j.val≤5))
  obtain ⟨x,hx⟩ : ∃ x :F,S.eval (C x)≠0:= by
    by_contra! hall
    have hroots : (Finset.univ.map ⟨C,z7⟩:nX F[X]).val⊆S.roots := by
      intro y hy
      obtain ⟨x,_,rfl⟩:=Finset.mem_map.mp (Finset.mem_def.mpr hy)
      exact (Qy hS).mpr (hall x)
    have hcount:=Rm hroots
    rw [Finset.card_map,G1 ,card] at hcount
    exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide :5<6))) (hcount.trans hdeg)
  refine ⟨S.eval (C x),hx,?_⟩
  have hev :S.eval (C x) = ∑ j:Fin 6,W j*C (x^q^j.val) := by
    simp only [S,eval_finsetSum,eval_monomial,C_pow]
  have hstep (j:Fin 6) :a*(W j).map (xL F q)=b*W (j+1) := by
    change a*wA (xL F q) (W j)=b*W (j+1)
    simpa only [cHJ] using
      gMq (wA (xL F q)) _ _ (fun n=>cHI n a)
        (fun n=>cHI n b)
        ((bYB card b).trans (cHJ b).symm) h j
  rw [hev,Polynomial.map_sum,FV,FV]
  simp_rw [vl,TH,← pU,hstep,eel card]
  exact Fintype.sum_equiv (Equiv.addRight (1 :Fin 6)) _ _ (fun _=>rfl)
end Cyclic
theorem denominator {a b:K[X]} (hb:b≠0) (h:Ox a=Ox b) :
  ∃ Q:K[X],Q≠0∧a*Q.map lI=b*Q ∧ ∀ i,Q.eval (node i)≠0:= by
 classical
 let P (d:ℕ) := ∃ Q:K[X],Q≠0∧a*Q.map lI=b*Q∧Q.natDegree=d
 have hex : ∃ d,P d:= by
  obtain ⟨Q,hQ,hphase⟩:=dWA (F:=K) (q:=p) Te (by decide) hb h
  exact ⟨Q.natDegree,Q,hQ,hphase,rfl⟩
 obtain ⟨Q,hQ,hphase,hdeg⟩:=Nat.find_spec hex
 refine ⟨Q,hQ,hphase,?_⟩
 intro i hi
 let L:K[X] :=lJ (R:=K) - C (node i)
 have hL:L≠0:=X_sub_C_ne_zero (node i)
 have hfix :L.map lI=L:= by simp [L,aw6.dip]
 obtain ⟨R,hR⟩:=(dvd_iff_isRoot.mpr hi:L∣Q)
 have hR0:R≠0:= fun hz=>hQ (by rw [hR,hz,th])
 have hphaseR:a*R.map lI=b*R:= by
  apply wY hL
  rw [hR,vl,hfix] at hphase
  rw [← JK L a,← JK L b] at hphase
  exact hphase
 have hmin:=TI hex (show P R.natDegree from ⟨R,hR0,hphaseR,rfl⟩)
 rw [hR,u8 hL hR0,show L.natDegree=1 from natDegree_X_sub_C _] at hdeg
 omega
end
end cxN
end
section
namespace aiI
noncomputable section
open Polynomial K1 aR
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent:=Fin 4 →₀ ℕ
private def kO (m:Exponent) :ℕ :=
 m.sum (fun i a=>(133671 - i.val)*a)
private theorem aaG {w:I→K} {T:ℕ} {P:af 4} :
    Pq w T P ↔
      (∀ m∈P.support,m.sum (fun _ a=>a)≤4012 ∧
        m.sum (fun i a=>i.val*a)≤1650∧m 3≤550 ∧
        (P.coeff m).natDegree+kO m≤T)∧Contact w P:= by
  simp only [Pq,aO,shape,qE,SW,
    PD,Y4 ,tB]
  constructor
  · rintro ⟨⟨hb,hj,ht⟩,hT,hc⟩
    exact ⟨fun m hm=>⟨hb m hm,hj m hm,ht m hm,hT m hm⟩,hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨⟨fun m hm=>(h m hm).1,fun m hm=>(h m hm).2.1,fun m hm=>(h m hm).2.2.1⟩,
      fun m hm=>(h m hm).2.2.2,hc⟩
private def yZ (S:ao[X]) :af 4 →ₗ[ao] ao[X] :=
 (MvPolynomial.aeval (jet S)).toLinearMap.restrictScalars ao
private theorem ajI (S:ao[X]) (P:af 4) :yZ S P=cK P S:= by
 rfl
private theorem bpc (d P:ao[X]) (c:ao) (h:d∣P) :
  d∣c•P:= by
 rw [G8]
 exact h.mul_left _
private def aV (w:I→K) (T:ℕ) :uh ao (af 4) where
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
          m.sum (fun _ a=>a)≤4012∧m.sum (fun i a=>i.val*a)≤1650 ∧
            m 3≤550∧kO m≤T:= by
        rcases hor with h | h
        · obtain ⟨hb,hj,ht,hw⟩:=hP m h
          exact ⟨hb,hj,ht,by omega⟩
        · obtain ⟨hb,hj,ht,hw⟩:=hQ m h
          exact ⟨hb,hj,ht,by omega⟩
      obtain ⟨hb,hj,ht,hw⟩:=Ca
      refine ⟨hb,hj,ht,?_⟩
      have hsum: ((P+Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m)+(Q.coeff m)).natDegree≤_
        exact IT _ _
      have hdegree (R:af 4) (hR:m∈R.support→(R.coeff m).natDegree+kO m≤T) :
          (R.coeff m).natDegree≤T - kO m:= by
        by_cases h:m∈R.support
        · have :=hR h
          omega
        · have hz :R.coeff m=0:= by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz,natDegree_zero]
          exact N0 _
      have hp' := hdegree P (fun h=>(hP m h).2.2.2)
      have hq' := hdegree Q (fun h=>(hQ m h).2.2.2)
      have :=hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← ajI,qm,ajI,ajI]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP:= by
    obtain ⟨hP,hp⟩:=aaG.mp hP
    apply aaG.mpr
    constructor
    · intro m hm
      obtain ⟨hb,hj,ht,hw⟩:=hP m (MvPolynomial.support_smul hm)
      refine ⟨hb,hj,ht,?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h:yZ S (c•P)=c•yZ S P:=(yZ S).map_smul c P
      rw [ajI,ajI] at h
      rw [h]
      exact bpc _ _ c (hp i S hS)
private def bnp (T:ℕ) :
    af 4 →ₗ[ao] (((Fin 4→Fin 4013)×Fin (T+1))→ao) :=
  LinearMap.pi fun u =>
    (Polynomial.lcoeff ao u.2.val).comp
      ((MvPolynomial.lcoeff ao[X] (Finsupp.equivFunOnFinite.symm (fun i=>(u.1 i).val))
        : af 4 →ₗ[ao[X]] ao[X]).restrictScalars ao)
private instance bqa (w:I→K) (T:ℕ) :oy ao (aV w T) := by
  classical
  let f :aV w T →ₗ[ao] (((Fin 4→Fin 4013)×Fin (T+1))→ao) :=
    (bnp T).comp (aV w T).subtype
  have hzero (Q:aV w T) (hQ:f Q=0) :Q=0:= by
    obtain ⟨P,hP⟩:= Q
    change Pq w T P at hP
    apply zS
    change P=0
    apply MvPolynomial.ext
    intro m
    change _=0
    by_contra hnz
    have hm:=MvPolynomial.mem_support_iff.mpr hnz
    have hT: (P.coeff m).natDegree≤T:=(Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u:Fin 4→Fin 4013:= fun i=>⟨m i,Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [vw]
    by_cases hk :k<T+1
    · have hval :=zf hQ (u,⟨k,hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i=>(u i).val))).coeff k=0 at hval
      have heq :Finsupp.equivFunOnFinite.symm (fun i=>(u i).val)=m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact PA (by omega)
  apply zE f
  intro P Q h
  apply sub_eq_zero.mp
  have hz :=f.map_sub P Q
  rw [h,sub_self] at hz
  exact hzero (P-Q) hz
end
end aiI
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace bai
noncomputable section
open Polynomial Matrix gR
variable {F:Type} [nq F]
def slice (s :Fin 2→ℕ→F) (m n:ℕ) :uh F F[X] :=
 degreeLT F n ⊓ ⨅ b,⨅ j:Fin (m+1-n),p5 (NZ (s b) j.val)
theorem avy (s :Fin 2→ℕ→F) (m n:ℕ) (P:F[X]) :
  P∈slice s m n↔P.degree<(n:ℕ) ∧
    ∀ b j,j< m+1-n→NZ (s b) j P=0:= by
 simp only [slice,zqd,mem_degreeLT,Submodule.mem_iInf,
  LinearMap.mem_ker,Fin.forall_iff]
theorem dey (s :Fin 2→ℕ→F) (m n:ℕ) :
  slice s m (n+1)=kL.a7D s m n:= by
 classical
 ext P
 rw [avy,kL.b80]
 simp only [Nat.add_sub_add_right]
instance gRO (s :Fin 2→ℕ→F) (m n:ℕ) :
  X8 F (slice s m n) :=
 zE (Submodule.inclusion (inf_le_left :
  slice s m n≤degreeLT F n)) (Submodule.inclusion_injective _)
theorem bhn (s :Fin 2→ℕ→F) (m:ℕ) :zh (slice s m) := by
 intro a b hab P hP
 obtain ⟨hd,hr⟩:=(avy s m a P).mp hP
 exact (avy s m b P).mpr
  ⟨hd.trans_le (by exact_mod_cast hab),fun k j hj=>hr k j (by omega)⟩
theorem dex (s :Fin 2→ℕ→F) (m n:ℕ) :
   (slice s m n).map (kL.a6K (lJ:F[X]))≤ slice s m (n+1) := by
 rintro _ ⟨P,hP,rfl⟩
 obtain ⟨hd,hr⟩:=(avy s m n P).mp hP
 apply (avy s m (n+1) _).mpr
 change ((lJ:F[X])*P).degree<((n+1 :ℕ) :WithBot ℕ)∧_
 rw [p9 (lJ:F[X]) P]
 refine ⟨?_,?_⟩
 · by_cases hP0:P=0
   · simp [hP0]
   have h:=(Gj hP0).mpr hd
   have hh:=u8 hP0 (xm : (lJ:F[X])≠0)
   rw [natDegree_X] at hh
   exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (P*lJ).natDegree<n+1 by omega))
 · intro b j hj
   change NZ (s b) j (lJ*P)=0
   rw [p9 (lJ:F[X]) P,← uW (lJ:F[X]),
     Principal.bLb]
   exact hr b (j+1) (by omega)
theorem gsd (s :Fin 2→ℕ→F) (m n:ℕ) (hn:n< m) :
    slice s m (n+1) ⊓ (slice s m (n+1)).map (kL.a6K (lJ:F[X])) =
      (slice s m n).map (kL.a6K (lJ:F[X])) := by
  apply le_antisymm
  · rintro _ ⟨hXP,P,hP,rfl⟩
    refine ⟨P,?_,rfl⟩
    by_cases hP0:P=0
    · simp [hP0]
    obtain ⟨_,hr⟩:=(avy s m (n+1) P).mp hP
    change (lJ*P)∈slice s m (n+1) at hXP
    have hXP' : P*lJ∈slice s m (n+1) := by
      simpa only [p9] using hXP
    obtain ⟨hd,hrX⟩:=(avy s m (n+1) (P*lJ)).mp hXP'
    apply (avy s m n P).mpr
    refine ⟨?_,?_⟩
    · have hx :=vj hP0 (xm : (lJ:F[X])≠0)
      have h:=(Gj hx).mpr hd
      rw [u8 hP0 xm,natDegree_X] at h
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (show P.natDegree<n by omega))
    · intro b j hj
      by_cases hz :j=0
      · exact hr b j (by omega)
      · have h:=hrX b (j-1) (by omega)
        rw [← uW  (lJ :F[X]),Principal.bLb,
          show j-1+1=j by omega] at h
        exact h
  · exact le_inf (dex s m n) (zzl (bhn s m (Ts n)))
abbrev acM (s :Fin 2→ℕ→F) (m n:ℕ) :=
 lz F (slice s m n)
theorem grQ (s :Fin 2→ℕ→F) (m:ℕ) :acM s m 0=0:= by
 have h:slice s m 0 = ⊥ := by
  apply le_bot_iff.mp
  intro P hP
  have hd:=((avy s m 0 P).mp hP).1
  by_contra hn
  have hn' : P≠0:= by simpa using hn
  have :=(Gj hn').mpr hd
  omega
 simp [h]
theorem bNX (s :Fin 2→ℕ→F) (m n:ℕ) :
   acM s m (n+1)=lz F
     (p5 (vH s m n).mulVecLin) := by
 classical
 unfold acM
 rw [dey,kL.fU7]
 have hM:kL.aWQ s m n=vH s m n:= by
   ext i j
   simp [kL.aWQ,vH,Dz]
 rw [hM]
theorem grN (s :Fin 2→ℕ→F) (m n:ℕ) (hn:n< m) :
   2*acM s m (n+1)≤acM s m (n+2)+acM s m n:= by
 let f :F[X] →ₗ[F] F[X] :=kL.a6K (lJ:F[X])
 have hf :p7 f := fun _ _ h =>
   wY (xm : (lJ:F[X])≠0) h
 have hmap (k :ℕ) :lz F ((slice s m k).map f)=acM s m k :=
   (Ze f hf _).finrank_eq.symm
 let:X8 F ((slice s m (n+1)).map f) :=
   G3 _ (Ze f hf _).surjective
 have hd:=Nr (slice s m (n+1))
   ((slice s m (n+1)).map f)
 have hover :slice s m (n+1) ⊓ (slice s m (n+1)).map f =
     (slice s m n).map f :=gsd s m n hn
 rw [hover,hmap,hmap] at hd
 have hle :slice s m (n+1) ⊔ (slice s m (n+1)).map f≤ slice s m (n+2) :=
   sup_le (bhn s m (Ts _)) (dex s m (n+1))
 have :=zd hle
 unfold acM at *
 omega
theorem eOB (s :Fin 2→ℕ→F) (m a t:ℕ)
    (hat :a≤t) (htm:t≤ m) (hne :0<acM s m (a+1))
    (hnull:acM s m (t+1)=(t-a)+1) :
    ∃ g:F[X],g≠0∧g.natDegree≤a ∧
      ∀ P:F[X],P.natDegree≤t →
        ((vH s m t).mulVec (fun j=>P.coeff j.val)=0 ↔
          ∃ Q:F[X],Q.natDegree≤t-a∧P=g*Q) := by
  classical
  obtain ⟨g,hg⟩:=Module.finrank_pos_iff_exists_ne_zero.mp hne
  have hg₀:g.val≠0:= fun he=>hg (zS he)
  have hmem:g.val∈kL.a7D s m a := by
    rw [← dey]
    exact g.property
  obtain ⟨hdeg,hrec⟩:=(kL.b80 s m a _).mp hmem
  let gBounded:degreeLT F (a+1) :=⟨g.val,mem_degreeLT.mpr hdeg⟩
  have hgK:Principal.akK s m a g.val :=
    ⟨Principal.ayC gBounded,hrec⟩
  have hprod (Q:F[X]) (hQ:Q.natDegree≤t-a) :
      (vH s m t).mulVec (fun j=>(g.val*Q).coeff j.val)=0:= by
    have hQK:=Principal.deM s m a (t-a) (by omega) g.val Q hgK hQ
    rw [show a+(t-a)=t by omega] at hQK
    exact ((Principal.aPN s m t _).mp hQK).2
  rw [bNX] at hnull
  refine ⟨g.val,hg₀,hgK.1,fun P hP=>⟨?_,?_⟩⟩
  · intro hker
    exact Principal.c1F a (t-a) t (vH s m t)
      g.val hg₀ hgK.1 (by omega) hnull
      (fun Q=>hprod Q.val (Principal.ayC Q)) P hP hker
  · rintro ⟨Q,hQ,rfl⟩
    exact hprod Q hQ
end
end bai
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace bai
noncomputable section
open Polynomial Matrix gR
variable {F:Type} [nq F]
def bzl (s :Fin 2→ℕ→F) (m:ℕ) :Prop :=
 ∃ i j:Fin m,s 0 i.val*s 1 j.val≠s 0 j.val*s 1 i.val
theorem grO (s :Fin 2→ℕ→F) (m:ℕ) :
  acM s m (m+1)=m+1 := by
 have h:slice s m (m+1)=degreeLT F (m+1) := by
  ext P
  rw [avy,mem_degreeLT]
  simp
 unfold acM
 rw [h,(degreeLTEquiv F (m+1)).finrank_eq,zvt,
  u9]
theorem grP (s :Fin 2→ℕ→F) (m:ℕ) (hs :bzl s m) :
   acM s m m+2=m:= by
 obtain ⟨i,j,hij⟩:=hs
 cases m with
 | zero=>exact Fin.elim0 i
 | succ k =>
   rw [bNX]
   let M:=vH s (k+1) k
   let rows :Fin 2→Fin 2×Fin (k+1-k) := fun b=>(b,⟨0,by omega⟩)
   let cols :Fin 2→Fin (k+1) := ![i,j]
   have hdet: (M.submatrix rows cols).det≠0:= by
    rw [Matrix.det_fin_two,sub_ne_zero]
    change s 0 (0+i.val)*s 1 (0+j.val)≠s 0 (0+j.val)*s 1 (0+i.val)
    simpa only [ze] using hij
   have hlo:=Matrix.rank_submatrix_le M rows cols
   rw [Matrix.rank_of_det_ne_zero hdet,u9] at hlo
   have hhi:=M.rank_le_card_height
   rw [Fintype.card_prod,u9,u9] at hhi
   have h:=LinearMap.finrank_range_add_finrank_ker M.mulVecLin
   change M.rank+Module.finrank F (p5 M.mulVecLin)= _ at h
   rw [zvt,u9] at h
   change lz F (p5 M.mulVecLin)+2=k+1
   omega
theorem gBu (d:ℕ→ℕ) (m:ℕ) (hzero :d 0=0)
   (hmono:zh d)
   (hconv : ∀ n< m,2*d (n+1)≤d (n+2)+d n)
   (hlast :d (m+1)=d m+3) :
   ∃ a b c:ℕ,a≤b∧b≤ c∧c≤ m ∧
     ∀ n≤ m+1,d n=(n-a)+(n-b)+(n-c) := by
 let Δ (n:ℕ) :=d (min n m+1) - d (min n m)
 have hΔm:Δ m=3:= by simp [Δ,hlast]
 have hΔmono:zh Δ:= by
   apply monotone_nat_of_le_succ
   intro n
   by_cases hn:n< m
   · simp only [Δ,min_eq_left hn.le,min_eq_left (show n+1≤m by omega)]
     change d (n+1) - d n≤d (n+2) - d (n+1)
     have h₀:d n≤d (n+1) :=hmono (Ts  n)
     have h₁:d (n+1)≤d (n+2) :=hmono (Ts  (n+1))
     have hc:=hconv n hn
     omega
   · simp [Δ,Sv (show m≤n by omega),Sv (show m≤n+1 by omega)]
 have hΔmax (n:ℕ) :Δ n≤3:= by
   by_cases h:n≤ m
   · exact (hΔmono h).trans (by rw [hΔm])
   · simpa [Δ,Sv (show m≤n by omega)] using hΔm.le
 have threshold (q:ℕ) (hq:q≤3) :
     ∃ a≤ m,∀ n,q≤Δ n↔a≤n:= by
   have hex : ∃ n,q≤Δ n:=⟨m,by rwa [hΔm]⟩
   refine ⟨Nat.find hex,TI hex (by rwa [hΔm]),fun n=>⟨TI hex,?_⟩⟩
   intro hn
   exact (Nat.find_spec hex).trans (hΔmono hn)
 obtain ⟨a,ha,hA⟩:=threshold 1 (by decide)
 obtain ⟨b,hb,hB⟩:=threshold 2 (by decide)
 obtain ⟨c,hc,hC⟩:=threshold 3 (by decide)
 have hab:=(hA b).mp (Nat.le_trans (by decide :1≤2) ((hB b).mpr qG))
 have hbc:=(hB c).mp (Nat.le_trans (by decide :2≤3) ((hC c).mpr qG))
 refine ⟨a,b,c,hab,hbc,hc,?_⟩
 intro n
 induction n with
 | zero=>simp [hzero]
 | succ n ih =>
   intro hn
   have hstep:Δ n=d (n+1) - d n:= by
     simp [Δ,min_eq_left (show n≤m by omega)]
   have hprev :=ih (by omega)
   have hle :=hmono (Ts n)
   have hbound:=hΔmax n
   have hA' := hA n
   have hB' := hB n
   have hC' := hC n
   omega
theorem evV (s :Fin 2→ℕ→F) (m:ℕ) (hs :bzl s m) :
  ∃ a b c:ℕ,a≤b∧b≤ c∧c≤ m∧a+b+c=2*m+2 ∧
    ∀ n≤ m+1,acM s m n=(n-a)+(n-b)+(n-c) := by
 have hlast :=grO s m
 have htop:=grP s m hs
 have hmono:zh (acM s m) :=
  fun _ _ h=>zd (bhn s m h)
 obtain ⟨a,b,c,hab,hbc,hc,hdim⟩:=gBu (acM s m) m
  (grQ s m) hmono (grN s m) (by omega)
 have h:=hdim (m+1) qG
 exact ⟨a,b,c,hab,hbc,hc,by omega,hdim⟩
theorem evU (s :Fin 2→ℕ→F) (m a b c:ℕ)
  (hdim : ∀ n≤ m+1,acM s m n=(n-a)+(n-b)+(n-c)) :
  kL.aKl s m a b c:= by
 intro H hH
 obtain ⟨t,ht⟩ : ∃ t,m-H=t+1 :=⟨m-H-1,by omega⟩
 have hrows :H+1=m-t:= by omega
 rw [ht,hrows]
 change lz F (p5 (vH s m t).mulVecLin)= _
 rw [← bNX]
 exact hdim _ (by omega)
end
end bai
end
section
set_option maxHeartbeats 800000
namespace akQ
noncomputable section
open cu gT pI Polynomial
open MvPolynomial (weightedTotalDegree_pow_le mem_restrictWeightedDegree_iff_weightedTotalDegree_le)
private abbrev aUs :aZ →+* Ambient:=oi.comp pZ
private theorem bu8 (i:Fin 3) :
  oi (cy i)=cy (Pv (by decide) i) := by
 simp [oi]
private theorem fZz (P:Jet) :
  iJ P=P.sum fun j g =>
   (g.sum fun i c=>aUs c*cy 2^i)*cy 3^j:= by
 simp only [iJ,A7,coe_eval₂RingHom,eval₂_eq_sum,t7,
  Polynomial.sum,t8 ,ox ,wB,aUs,bu8]
 rfl
private def substitute {F:Type} [nq F] [p6 FX F] (x :Fin 4→lK F) :ov →+* lK F :=
 qM (MvPolynomial.C.comp (c9 FX F)) x
private theorem gpf {F:Type} [nq F] [p6 FX F] (x :Fin 4→lK F) (c:aZ) :
    substitute x (aUs c) =
      MvPolynomial.aeval (fun i:Fin 2=>x (Fin.castLE (by decide) i))
        (oz  (c9  FX F) c) := by
  have he : (substitute x).comp aUs =
      qM (MvPolynomial.C.comp (c9 FX F))
        (fun i:Fin 2=>x (Pv (by decide) i)) := by
    apply qU
    · intro z
      simp [substitute,aUs,pZ,oi]
    · intro i
      fin_cases i <;> simp [substitute,aUs,pZ,oi]
  rw [← t7,he,MvPolynomial.aeval_def]
  apply (MvPolynomial.eval₂Hom_map_hom (c9 FX F) _ lV c).symm
private theorem bgW {F:Type} [nq F] [p6 FX F] (w:Fin 2→ℕ) (x :Fin 4→lK F)
    {P:Jet} {s :Shape} (hP:oU P s) (a b c D:ℕ)
    (hseed : ∀ i:Fin 2,vZ w (x (Pv (by decide) i))≤a)
    (hy :vZ w (x 2)≤b) (hv :vZ w (x 3)≤ c)
    (hcap : ∀ j i,i+j≤ s.B→j≤ s.J→a*s.U + i*b+j*c≤D) :
    vZ w (substitute x (iJ P))≤D:= by
  classical
  have hcoeff (q:aZ) :vZ w (substitute x (aUs q)) ≤
      a*q.totalDegree := by
    rw [gpf]
    refine (MvPolynomial.weightedTotalDegree_aeval_le_of_le (fun _:Fin 2=>a) w _ _
      hseed).trans ?_
    apply Finset.sup_le
    intro m hm
    have hdeg:=Zg (MvPolynomial.support_map_subset _ _ hm)
    have hweight:Finsupp.weight (fun _:Fin 2=>a) m=a*m.degree := by
      simp only [ Xg ,Finsupp.degree_apply,Un,Fz ,
        FV,Gn]
    rw [hweight]
    exact Cy _ hdeg
  rw [fZz]
  simp only [Polynomial.sum,t8 ,ox ,wB,substitute,Kz]
  change vZ w (∑ j∈P.support,
    (∑ i∈(P.coeff j).support,substitute x (aUs ((P.coeff j).coeff i))*x 2^i) *
      x 3^j)≤D
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply zo3
  intro j _
  rw [Finset.sum_mul]
  apply zo3
  intro i hi
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  obtain ⟨hij,hj,hseeddeg⟩:=hP j i (Polynomial.mem_support_iff.mp hi)
  refine (Sd _ _ _).trans (le_trans ?_ (hcap j i hij hj))
  exact NW
    ((Sd _ _ _).trans (NW
      ((hcoeff _).trans (Cy _ hseeddeg))
      ((weightedTotalDegree_pow_le _ _ _).trans (Cy _ hy))))
    ((weightedTotalDegree_pow_le _ _ _).trans (Cy _ hv))
private theorem bPU {F:Type} [nq F] (w:Fin 2→ℕ) (i:Fin 2) :
  vZ w (cy i:lK F)=w i:= by
 rw [cy ,MvPolynomial.weightedTotalDegree_monomial _ _ _ Pr,
  Il,one_smul]
private theorem byF {F:Type} [nq F] (w:Fin 2→ℕ) (a b:F) (i:Fin 2) :
   vZ w (lV a-MvPolynomial.C b*cy i:lK F)≤w i:= by
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
 apply pL
 · simp
 · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
   exact (Sd _ _ _).trans (by simp [bPU])
private abbrev abn:Fin 4→lK aQ :=
 ![lV (ek 0),lV (ek 1),cy 0,cy 1]
private abbrev ep1 :Fin 4→lK aQ :=
 ![cy 0,cy 1,lV (ek 0),lV (ek 1)]
theorem dcY {P:Jet} {s :Shape} (hP:oU P s) :
  (Dk (iJ P)).totalDegree≤ s.B:= by
 rw [← WW]
 exact bgW (F:=aQ) 1 abn hP 0 1 1 s.B
  (fun i=> by fin_cases i <;> simp)
  (by simp [bPU]) (by simp [bPU]) (fun j i hij _=> by simpa using hij)
theorem dcX {P:Jet} {s :Shape} (hP:oU P s) :
  (Dk (iJ P)).degreeOf 1≤ s.J:= by
 rw [← Gr]
 exact bgW (F:=aQ) (vi 1 1) abn hP 0 0 1 s.J
  (fun i=> by fin_cases i <;> simp)
  (by simp [G5]) (by simp) (fun j i _ hj=> by simpa using hj)
theorem cVY {P:Jet} {s :Shape} (hP:oU P s) :
  (CG (iJ P)).totalDegree≤ s.U:= by
 rw [← WW]
 exact bgW (F:=aQ) 1 ep1 hP 1 0 0 s.U
  (fun i=> by fin_cases i <;> simp [bPU])
  (by simp) (by simp) (by simp)
theorem bIu (kK:Bool) {P:Jet} {s :Shape} (hP:oU P s) :
   (oK kK (iJ P)).degreeOf 0≤ s.U:= by
 rw [← Gr]
 refine bgW (F:=dV) (vi 0 1) (Fp kK) hP 1 0 0 s.U ?_ ?_ ?_ (by simp)
 · intro i
   fin_cases i
   · exact (byF (vi 0 1) _ _ 0).trans (by simp)
   · simp [Fp]
 · cases kK
   · simp [Fp]
   · exact (byF (vi 0 1) _ _ 1).trans (by simp)
 · simp [Fp,G5]
theorem c2R {P:Jet} {s :Shape} (hP:oU P s) :
   (oK sH (iJ P)).degreeOf 1≤ s.J:= by
 rw [← Gr]
 refine bgW (F:=dV) (vi 1 1) (Fp sH) hP 0 0 1 s.J ?_ ?_ ?_ ?_
 · intro i
   fin_cases i
   · exact (byF (vi 1 1) _ _ 0).trans (by simp)
   · simp [Fp,G5]
 · simp [Fp]
 · simp [Fp]
 · intro j i _ hj
   simpa using hj
theorem c0s {P:Jet} {s :Shape} (hP:oU P s) :
   (oK true (iJ P)).degreeOf 1≤ s.B:= by
 rw [← Gr]
 refine bgW (F:=dV) (vi 1 1) (Fp true) hP 0 1 1 s.B ?_ ?_ ?_ ?_
 · intro i
   fin_cases i
   · exact (byF (vi 1 1) _ _ 0).trans (by simp)
   · simp [Fp,G5]
 · exact (byF (vi 1 1) _ _ 1).trans (by simp)
 · simp [Fp]
 · intro j i hij _
   simpa using hij
end
end akQ
end
section
namespace akQ
noncomputable section
open cu gT pI Ty
def c1 :Prop :=
  ∀ (F:Type) [nq F] (φ:ov →+* lK F) (k :Fin 4),
    aSD F φ k →
    ∀ (P Q:Jet) (S:nX (oj ov)) (d:ℕ),
      oy F (Zj φ (a07 P Q))→0<d →
      (∀ I∈S,∃ hI:xN I,
        pN I k≠0→(d:ℕ∞)≤Be P Q I hI.prime) →
      d*mass S k≤lz F (Zj φ (a07 P Q))
def c2 :Prop :=
 aSD aQ Dk 0∧aSD aQ CG 3
def c3:Prop :=
  aSD dV (oK sH) 1 ∧
    aSD dV (oK true) 2
def c4 :Prop :=
  ∀ (F:Type) [nq F] (f g:lK F) (a b c e :ℕ),
    oZ f g→f.degreeOf 0≤a→f.degreeOf 1≤b →
    g.degreeOf 0≤ c→ g.degreeOf 1≤e →
    oy F (aBX f g) ∧
      lz F (aBX f g)≤a*e+c*b
def c5:Prop :=
  ∀ (F:Type) [nq F] (f g:lK F) (b j c e :ℕ),
    oZ f g→j≤b→e≤ c →
    f.totalDegree≤b→f.degreeOf 1≤j→ g.totalDegree≤ c→ g.degreeOf 1≤e →
    oy F (aBX f g) ∧
      lz F (aBX f g)≤b*e+c*j - j*e
private theorem ezc {F:Type} [nq F] (φ:ov →+* lK F) (P Q:Jet) :
  (a07 P Q).map φ=nI {φ (iJ P),φ (iJ Q)} := by
 rw [sS ,Wm,uz]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :
    Ty.c5:= by
  intro P Q s t S k d _ _ hrel hs ht hP hQ hd hlocal
  have apply_cap {F:Type} [nq F] (φ:ov →+* lK F) (k :Fin 4)
      (bY:aSD F φ k)
      (cap:oy F (aBX (φ (iJ P)) (φ (iJ Q))) ∧
        lz F (aBX (φ (iJ P)) (φ (iJ Q)))≤aoD s t k)
      (hlocal : ∀ I∈S,∃ hI:xN I,
        pN I k≠0→(d:ℕ∞)≤Be P Q I hI.prime) :
      d*mass S k≤aoD s t k := by
    obtain ⟨hfinite,hdim⟩:=cap
    have hmap :=ezc φ P Q
    have hfinite' : oy F (Zj φ (a07 P Q)) := by
      change oy F (lK F ⧸ (a07 P Q).map φ)
      rwa [hmap]
    refine (h1 F φ k bY P Q S d hfinite' hd hlocal).trans ?_
    change lz F (lK F ⧸ (a07 P Q).map φ)≤aoD s t k
    rwa [hmap]
  fin_cases k
  · apply apply_cap Dk 0 h2.1 _ hlocal
    exact h5 aQ _ _ s.B s.J t.B t.J (h2.1.relPrime _ _ hrel) hs ht
      (dcY hP) (dcX hP) (dcY hQ) (dcX hQ)
  · apply apply_cap (oK sH) 1 h3.1 _ hlocal
    exact h4 dV _ _ s.U s.J t.U t.J (h3.1.relPrime _ _ hrel)
      (bIu sH hP) (c2R hP)
      (bIu sH hQ) (c2R hQ)
  · apply apply_cap (oK true) 2 h3.2 _ hlocal
    exact h4 dV _ _ s.U s.B t.U t.B (h3.2.relPrime _ _ hrel)
      (bIu true hP) (c0s hP) (bIu true hQ) (c0s hQ)
  · apply apply_cap CG 3 h2.2 _ hlocal
    have htotalP:=cVY hP
    have htotalQ:=cVY hQ
    obtain ⟨hfinite,hdim⟩:=h5 aQ _ _ s.U s.U t.U t.U (h2.2.relPrime _ _ hrel)
      qG qG htotalP ((x7 _ 1).trans htotalP)
      htotalQ ((x7 _ 1).trans htotalQ)
    refine ⟨hfinite,?_⟩
    change _≤ s.U*t.U
    simpa [Gn t.U s.U] using hdim
end
end akQ
end
section
namespace cy4
noncomputable section
open cu gT pI akQ
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev ax3:=mD Bool ov
private abbrev Params :=mD (Fin 4) FX
private abbrev Lg:=mD (Fin 2) Params
private abbrev Target :=lK dV
private def toChart {R:Type} [pz R] (kK:Bool) :
    mD Bool (mD (Fin 4) R) →+*
      mD (Fin 2) (mD (Fin 4) R) :=
  qM
    (qM (C.comp C)
      ![C (cy 2) - C (cy 0)*cy 0,cy 0,
        if kK then C (cy 3) - C (cy 1)*cy 1
        else C (cy 3),cy 1])
    (fun i=>if i then C (cy 1) else C (cy 0))
private def a4p {R:Type} [pz R] (kK:Bool) :
    mD (Fin 2) (mD (Fin 4) R) →+*
      mD Bool (mD (Fin 4) R) :=
  qM
    (qM (C.comp C)
      ![cy sH,cy true,
        C (cy 0)+MvPolynomial.X sH*C (cy 1),
        if kK then C (cy 2)+MvPolynomial.X true*C (cy 3)
        else C (cy 2)])
    ![C (cy 1),C (cy 3)]
private def J6 {R:Type} [pz R] (kK:Bool) :
    mD Bool (mD (Fin 4) R) ≃+*
      mD (Fin 2) (mD (Fin 4) R) := by
  refine RingEquiv.ofRingHom (toChart kK) (a4p kK) ?_ ?_
  · apply zey
    · apply qU
      · intro a
        simp [toChart,a4p]
      · intro i
        fin_cases i <;> cases kK <;> simp [toChart,a4p]
    · intro i
      fin_cases i <;> simp [toChart,a4p]
  · apply zey
    · apply qU
      · intro a
        simp [toChart,a4p]
      · intro i
        fin_cases i <;> cases kK <;>
          simp [toChart,a4p,-MvPolynomial.coe_eval₂Hom]
    · intro i
      cases i <;> simp [toChart,a4p]
private abbrev Ek :zm Lg :=
 (Ea Params).map C
private abbrev cNY (kK:Bool) :ax3 →+* Target :=
 (c9 Lg Target).comp (J6 kK).toRingHom
private theorem cX3 (kK:Bool) :
   oK kK=(cNY kK).comp C:= by
 apply qU
 · intro a
   change oK kK (C a) =
    oz (c9 Params dV) (toChart kK (C (C a)))
   simp [oK,toChart]
   rfl
 · intro i
   change oK kK (cy i) =
    oz (c9 Params dV) (toChart kK (C (cy i)))
   fin_cases i <;> cases kK <;>
    simp [oK,Fp,toChart,kz]
private theorem aWu {R:Type} [pz R] (I:oj R) (hI:I.IsPrime) :
   (I.map (C:R →+* mD Bool R)).IsPrime ∧
     (I.map (C:R →+* mD Bool R)).comap C=I:= by
 let _:I.IsPrime :=hI
 let q:mD Bool R →+* mD Bool (R ⧸ I) :=
   oz (yl I)
 have hker :sI q=I.map C:= calc
   sI q=(sI (yl I)).map C :=
     Ye (σ:=Bool) (yl I)
   _=I.map C:= by rw [Kh]
 rw [← hker]
 constructor
 · rw [Du]
   exact Oc q ⊥
 · rw [Ob]
   have hq:q.comp C=C.comp (yl I) := by
     apply F9
     intro a
     simp [q]
   rw [hq,RingHom.ker_comp_of_injective _ (IU _ _),Kh]
private theorem cSE (kK:Bool) :
    @Module.Flat ov Target _ _ (@P7 _ _ _ _ (oK kK).toAlgebra) ∧
    (∀ I:oj ov,I.IsPrime→ I.map (oK kK) ≠ ⊤ →
      (I.map (oK kK)).IsPrime∧(I.map (oK kK)).comap (oK kK)=I) := by
  let slopeAlgebra :p6 ax3 Target :=(cNY kK).toAlgebra
  let _:p6 ax3 Target :=slopeAlgebra
  let S:zm ax3:=Ek.comap (J6 kK).toMulEquiv.toMonoidHom
  let _:Df S Target := by
    apply IsLocalization.of_ringEquiv_left (J6 kK) (M₁:=Ek)
    · change S.map (J6 kK).toMulEquiv.toMonoidHom=Ek
      exact Submonoid.map_comap_eq_of_surjective (J6 kK).surjective _
    · intro x
      rfl
  constructor
  · let ambientAlgebra :p6 ov Target :=(oK kK).toAlgebra
    let _:p6 ov Target :=ambientAlgebra
    let _:yL ov Target := @P7 _ _ _ _ ambientAlgebra
    let _:yL ax3 Target := @P7 _ _ _ _ slopeAlgebra
    let _:IsScalarTower ov ax3 Target :=
      IsScalarTower.of_algebraMap_eq' (cX3 kK)
    let _:Module.Flat ax3 Target :=zsF Target S
    exact Module.Flat.trans ov ax3 Target
  · intro I hI hproper
    rw [cX3,← Ml] at hproper ⊢
    rw [← zg6]
    obtain ⟨hprime,hcontract⟩:=aWu I hI
    let J:oj ax3:=I.map C
    have hd:Disjoint (S:Set ax3) (J:Set ax3) :=
      (GF S Target J).mp hproper
    exact ⟨Kl S Target J hprime hd,
      (oD (fun D:oj ax3=>D.comap C)
        (LO S Target hprime hd)).trans hcontract⟩
private theorem c7Z {R T:Type} [pz R] [pz T]
    [y5 R] [y5 T] [z9 R] [z9 T]
    (φ:R →+* T)
    (hφ : ∀ I:oj R,I.IsPrime→ I.map φ ≠ ⊤ →
      (I.map φ).IsPrime∧(I.map φ).comap φ=I)
    (a b:R) (hab:oZ a b) :oZ (φ a) (φ b) := by
  have hinj:p7 φ:= by
    rw [RingHom.injective_iff_ker_eq_bot,Du]
    simpa using (hφ ⊥ Ideal.isPrime_bot (by simp)).2
  by_cases ha :a=0
  · subst a
    simp only [pC,isRelPrime_zero_left] at hab ⊢
    exact hab.map φ
  have ha' : φ a≠0:= fun h=>ha (hinj (h.trans (pC φ).symm))
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors ha').mpr
  intro d hda hdb hd
  have liftFactor (x :R) :x≠0→d∣φ x →
      ∃ p:R,Prime p∧p∣x∧d∣φ p:= by
    induction x using UniqueFactorizationMonoid.induction_on_prime with
    | h₁=>simp
    | h₂ u hu=>exact fun _ hdu=>(hd.not_isUnit (isUnit_of_dvd_unit hdu (hu.map φ))).elim
    | h₃ x p hx hp ih =>
      intro _ hdp
      rw [ox] at hdp
      rcases hd.dvd_mul.mp hdp with h | h
      · exact ⟨p,hp,FQ p x,h⟩
      · obtain ⟨q,hq,hqx,hdq⟩:=ih hx h
        exact ⟨q,hq,hqx.trans (Fa x p),hdq⟩
  obtain ⟨p,hp,hpa,hdp⟩:=liftFactor a ha hda
  have hproper : (nI {p}).map φ ≠ ⊤ := by
    intro htop
    rw [sS ,uz] at htop
    exact hd.not_isUnit (G6 hdp (Ideal.span_singleton_eq_top.mp htop))
  obtain ⟨hprime,hcontract⟩:=hφ _ (Ideal.isPrime_span_singleton_of_prime hp) hproper
  have hp' : φ p≠0:= fun h=>hp.ne_zero (hinj (h.trans (pC φ).symm))
  rw [sS ,uz ,Ideal.span_singleton_prime hp'] at hprime
  have hpb:φ p∣φ b :=
    ((hd.dvd_prime_iff_associated hprime).mp hdp).dvd'.trans hdb
  apply hp.not_isUnit (hab hpa ?_)
  rw [← UZ,← hcontract,Ideal.mem_comap,sS ,
    uz ,UZ]
  exact hpb
private theorem cLx (kK:Bool) :
   (yQ kK).toRingHom.comp AU=oK kK:= by
 apply qU
 · intro a
   simp [yQ,AU,oK,MvPolynomial.algebraMap_eq]
 · intro i
   fin_cases i <;> cases kK <;>
     simp [yQ,AU,oK,Fp]
private theorem cR8 {A B:Type} [Au A] [Au B]
   [yL dV A] [yL dV B] (e :A ≃ₗ[dV] B)
   (h:oy dV A) :
   oy dV B∧lz dV B=lz dV A :=
 letI:=h
 ⟨G3 e.toLinearMap e.surjective,e.finrank_eq.symm⟩
theorem proof :akQ.c3:= by
  obtain ⟨hf₁,hp₁⟩:=cSE sH
  obtain ⟨hf₂,hp₂⟩:=cSE true
  refine ⟨⟨hf₁,?_,hp₁,c7Z _ hp₁⟩,
    ⟨hf₂,?_,hp₂,c7Z _ hp₂⟩⟩
  · intro I hI
    have e :=(atd.bJ0 I).toLinearEquiv
    have h:=cR8 e hI.a6j
    change oy dV (Zj
      ((yQ sH).toRingHom.comp AU) I) ∧
      lz dV (Zj
        ((yQ sH).toRingHom.comp AU) I) =
        lz dV (ani I) at h
    rwa [cLx] at h
  · intro I hI
    have e :=(atd.bJf I).toLinearEquiv
    have h:=cR8 e hI.bfE
    change oy dV (Zj
      ((yQ true).toRingHom.comp AU) I) ∧
      lz dV (Zj
        ((yQ true).toRingHom.comp AU) I) =
        lz dV (Ik I) at h
    rwa [cLx] at h
end
end cy4
end
section
set_option maxHeartbeats 1000000
namespace bRJ
noncomputable section
open akQ MvPolynomial
private abbrev aer (F:Type) [nq F] :=mD (Option (Fin 1)) F
private abbrev box (F:Type) [nq F] :=
 restrictBidegree (Fin 1) F
variable {F:Type} [nq F]
private theorem bI2 {p:aer F} {i j:ℕ} :
  p∈box F i j↔p.degreeOf none≤ i∧p.degreeOf (some 0)≤j:= by
 simp only [mem_restrictBidegree,PD,Finsupp.degree_eq_sum,Fin.sum_univ_one,
  Finsupp.some_apply]
 exact ⟨fun h=>⟨fun m hm=>(h m hm).1,fun m hm=>(h m hm).2⟩,
  fun h m hm=>⟨h.1 m hm,h.2 m hm⟩⟩
private theorem cSc (i j:ℕ) :
  lz F (box F i j)=(i+1)*(j+1) := by
 simp [box,finrank_restrictBidegree,Nat.card_eq_fintype_card]
private abbrev multiples (p:aer F) (i j:ℕ) :uh F (aer F) :=
 (box F i j).map (Vs F p)
private theorem a4b {p:aer F} (hp:p≠0) (i j:ℕ) :
  lz F (multiples p i j)=(i+1)*(j+1) := by
 rw [multiples,← Mj,
  VC,cSc]
 intro u v huv
 change p*(u:aer F)=p*(v :aer F) at huv
 exact zS (wY hp huv)
private theorem c08 {p:aer F} (i j:ℕ) :
  multiples p i j≤box F (p.degreeOf none+i) (p.degreeOf (some 0)+j) := by
 rintro _ ⟨q,hq,rfl⟩
 exact mul_mem_restrictBidegree (bI2.mpr ⟨qG,qG⟩) hq
private theorem eIs {f g:aer F}
   (hg:g≠0) (hrel :oZ f g) (i j:ℕ) :
   multiples f (g.degreeOf none+i) (g.degreeOf (some 0)+j) ⊓
     multiples g (f.degreeOf none+i) (f.degreeOf (some 0)+j) ≤
     multiples (f * g) i j:= by
 let:z9 F:=Xx
 let:z9 (aer F) :=
   zhK (Option (Fin 1))
 rintro p ⟨⟨u,hu,hpu⟩,⟨v,_,hpv⟩⟩
 change f*u=p at hpu
 change g*v=p at hpv
 have hd:g∣f*u:=⟨v,hpu.trans hpv.symm⟩
 have hd' := UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors hg
   (fun h₁ h₂ hprime=>hprime.not_isUnit (hrel h₂ h₁)) hd
 obtain ⟨w,rfl⟩:=hd'
 have hw:w∈box F i j:= by
   by_cases hz :w=0
   · simp [hz]
   rcases bI2.mp hu with ⟨h₀,h₁⟩
   rw [G2 hg hz] at h₀
   rw [G2 hg hz] at h₁
   exact bI2.mpr ⟨VH h₀,VH h₁⟩
 exact ⟨w,hw,(pU f g w).trans hpu⟩
private theorem dAk {f g:aer F} (hf :f≠0) (hg:g≠0)
   (hrel :oZ f g) (i j:ℕ) :
   lz F (Pj (nI {f,g})
     (f.degreeOf none+g.degreeOf none+i) (f.degreeOf (some 0)+g.degreeOf (some 0)+j)) ≤
     f.degreeOf none*g.degreeOf (some 0)+g.degreeOf none*f.degreeOf (some 0) := by
 let a :=f.degreeOf none
 let b:=f.degreeOf (some 0)
 let c:=g.degreeOf none
 let e :=g.degreeOf (some 0)
 let W:=box F (a+c+i) (b+e+j)
 let U:=multiples f (c+i) (e+j)
 let V:=multiples g (a+i) (b+j)
 let I:oj (aer F) :=nI {f,g}
 let T:=Pj I (a+c+i) (b+e+j)
 let π:=(Aa F I).toLinearMap.domRestrict W
 have hUW:U≤W:= by
   simpa only [U,W,a,b,c,e,zi] using
     (c08 (p:=f) (c+i) (e+j))
 have hVW:V≤W:= by
   simpa only [V,W,a,b,c,e,Iw ,zi] using
     (c08 (p:=g) (a+i) (b+j))
 have hW:U ⊔ V≤W:=sup_le hUW hVW
 have hker : (U ⊔ V).comap W.subtype≤p5 π:= by
   have hUI:U≤I.restrictScalars F:= by
     rintro _ ⟨p,_,rfl⟩
     exact LQ _ _ (vk (by simp))
   have hVI:V≤I.restrictScalars F:= by
     rintro _ ⟨p,_,rfl⟩
     exact LQ _ _ (vk (by simp))
   intro x hx
   have hx' : (x :aer F)∈U ⊔ V:=hx
   exact Ideal.Quotient.eq_zero_iff_mem.mpr ((sup_le hUI hVI) hx')
 have hk :=zd hker
 rw [(Submodule.comapSubtypeEquivOfLe hW).finrank_eq] at hk
 have hover :=zd (eIs hg hrel i j)
 rw [a4b (vj hf hg)] at hover
 have hsum:=Nr U V
 rw [show U=multiples f (c+i) (e+j) from rfl,
   show V=multiples g (a+i) (b+j) from rfl,
   a4b hf,a4b hg] at hsum
 have hrank :=π.finrank_range_add_finrank_ker
 rw [show LinearMap.range π=T from Mj _ _] at hrank
 change _+_=lz F (box F (a+c+i) (b+e+j)) at hrank
 rw [cSc] at hrank
 have htotal:lz F T+Module.finrank F (U ⊔ V:uh F (aer F)) ≤
     (a+c+i+1)*(b+e+j+1) :=
   (Gk hk (lz F T)).trans_eq hrank
 have hpair : (c+i+1)*(e+j+1)+(a+i+1)*(b+j+1) ≤
     lz F (U ⊔ V:uh F (aer F))+(i+1)*(j+1) :=
   hsum.symm.trans_le (Gk hover _)
 have harith :
     (a+c+i+1)*(b+e+j+1)+(i+1)*(j+1) =
     (c+i+1)*(e+j+1)+(a+i+1)*(b+j+1)+(a*e+c*b) := by
   ring
 change lz F T≤a*e+c*b
 omega
private theorem eLK (f g:aer F) (hrel :oZ f g) :
    oy F (aer F ⧸ nI {f,g}) ∧
    lz F (aer F ⧸ nI {f,g}) ≤
      f.degreeOf none*g.degreeOf (some 0)+g.degreeOf none*f.degreeOf (some 0) := by
  classical
  let I:oj (aer F) :=nI {f,g}
  let Q:=aer F ⧸ I
  let k :=f.degreeOf none*g.degreeOf (some 0)+g.degreeOf none*f.degreeOf (some 0)
  change oy F Q∧lz F Q≤k
  have hfI:f∈I:=vk (by simp)
  have hgI:g∈I:=vk (by simp)
  by_cases ht:I = ⊤
  · let:Subsingleton Q:=Ideal.Quotient.subsingleton_iff.mpr ht
    exact ⟨zE (0:Q →ₗ[F] F) (fun x y _=>Subsingleton.elim x y),
      (Ww F Q).le.trans (N0 k)⟩
  have hf :f≠0:= by
    intro hz
    rw [hz] at hrel
    exact ht (G0 I hgI (isRelPrime_zero_left.mp hrel))
  have hg:g≠0:= by
    intro hz
    rw [hz] at hrel
    exact ht (G0 I hfI (isRelPrime_zero_right.mp hrel))
  have hdim (n:ℕ) (x :Fin n→Q) (hx :Ar F x) :n≤k := by
    choose p hp using fun t=>(Eg (I:=I) (x t))
    let i:=Finset.univ.sup fun t:Fin n=>(p t).degreeOf none
    let j:=Finset.univ.sup fun t:Fin n=>(p t).degreeOf (some 0)
    let A:=f.degreeOf none+g.degreeOf none+i
    let B:=f.degreeOf (some 0)+g.degreeOf (some 0)+j
    let S:=Pj I A B
    have hmem (t:Fin n) :x t∈S:= by
      refine mem_quotientBidegreeLE.mpr ⟨p t,bI2.mpr ⟨?_,?_⟩,hp t⟩
      · have hi: (p t).degreeOf none≤ i :=
          Finset.le_sup (f := fun u=>(p u).degreeOf none) (vG t)
        exact hi.trans (Nat.le_add_left _ _)
      · have hj: (p t).degreeOf (some 0)≤j :=
          Finset.le_sup (f := fun u=>(p u).degreeOf (some 0)) (vG t)
        exact hj.trans (Nat.le_add_left _ _)
    let y (t:Fin n) :S:=⟨x t,hmem t⟩
    have hy :Ar F y :=LinearIndependent.of_comp S.subtype hx
    have hy' : n≤lz F S:= by simpa using hy.fintype_card_le_finrank
    exact hy'.trans (dAk hf hg hrel i j)
  have hfinite :oy F Q:= by
    apply Module.rank_lt_aleph0_iff.mp
    by_contra! h
    have hn: ((k+1 :ℕ) :Cardinal)≤Module.rank F Q :=
      Cardinal.natCast_lt_aleph0.le.trans h
    obtain ⟨x,hx⟩:=exists_linearIndependent_of_le_rank hn
    have hh:=hdim (k+1) x hx
    omega
  obtain ⟨x,hx⟩:=exists_linearIndependent_of_le_finrank
    (qG :lz F Q≤lz F Q)
  exact ⟨hfinite,hdim _ x hx⟩
theorem proof :akQ.c4 := by
 intro F _ f g a b c e hrel hf₀ hf₁ hg₀ hg₁
 let ρ:=Ok F (FR 1)
 have hrel' : oZ (ρ f) (ρ g) := by
   apply IsRelPrime.of_map ρ.symm
   simpa using hrel
 have degree₀ (p:lK F) : (ρ p).degreeOf none=p.degreeOf 0:= by
   simp only [ρ,Vl,← show FR 1 0=none from rfl,
     degreeOf_rename_of_injective (FR 1).injective]
 have degree₁ (p:lK F) : (ρ p).degreeOf (some 0)=p.degreeOf 1 := by
   simp only [ρ,Vl,← show FR 1 1=some 0 from rfl,
     degreeOf_rename_of_injective (FR 1).injective]
 let q:=Ideal.quotientEquivAlg (nI ({f,g} : Set (lK F))) ρ (J :=
   nI {ρ f,ρ g}) (by simp [sS ,Wm,uz])
 obtain ⟨hfinite,hbound⟩:=eLK (ρ f) (ρ g) hrel'
 let _:=hfinite
 refine ⟨G3 q.symm.toLinearMap q.symm.surjective,?_⟩
 refine q.toLinearEquiv.finrank_eq.trans_le (hbound.trans ?_)
 simp only [degree₀,degree₁]
 exact NW (Nat.mul_le_mul hf₀ hg₁) (Nat.mul_le_mul hg₀ hf₁)
end
end bRJ
end
section
namespace bRK
noncomputable section
open akQ (lK aBX)
open MvPolynomial
variable {F:Type} [nq F]
private abbrev cap (F:Type) [nq F] (B J:ℕ) :uh F (lK F) :=
 restrictCappedDegree (Fin 2) F 1 B J
private theorem aOM {p:lK F} {B J:ℕ} :
  p∈cap F B J↔p.totalDegree≤B∧p.degreeOf 1≤J:= by
 rw [mem_restrictCappedDegree,PD,SW,Y4]
 exact ⟨fun h=>⟨fun m hm=>(h m hm).1,fun m hm=>(h m hm).2⟩,
  fun h m hm=>⟨h.1 m hm,h.2 m hm⟩⟩
private abbrev multiples (f :lK F) (B J:ℕ) :uh F (lK F) :=
 (cap F B J).map (Vs F f)
private theorem mem_multiples {f p:lK F} (hf :f≠0) {B J:ℕ} :
   p∈multiples f B J ↔
     p∈cap F (f.totalDegree+B) (f.degreeOf 1+J)∧f∣p:= by
 constructor
 · rintro ⟨q,hq,rfl⟩
   exact ⟨mul_mem_restrictCappedDegree (aOM.mpr ⟨qG,qG⟩) hq,⟨q,rfl⟩⟩
 · rintro ⟨hp,q,rfl⟩
   refine ⟨q,?_,rfl⟩
   by_cases hq:q=0
   · rw [hq]
     exact Submodule.zero_mem _
   · rw [aOM,totalDegree_mul_of_isDomain hf hq,G2 hf hq] at hp
     exact aOM.mpr ⟨by omega,by omega⟩
private abbrev OU (B J:ℕ) :ℕ :=
 (cappedDegreeExponents (Fin 2) 1 B J).ncard
private theorem a4b {f :lK F} (hf :f≠0) (B J:ℕ) :
  lz F (multiples f B J)=OU B J:= by
 rw [multiples,← Mj,VC,
  finrank_restrictCappedDegree]
 intro p q h
 exact zS (wY hf h)
private theorem dEy (B J b j c e :ℕ)
    (hJB:J≤B) (hjb:j≤b) (hec:e≤ c) :
    OU (B+b+c) (J+j+e)+OU B J =
      OU (B+c) (J+e)+OU (B+b) (J+j) +
        cappedDegreeMixedVolume b j c e := by
  have h00:=Lf B J hJB
  have Kr :=Lf (B+b) (J+j) (by omega)
  have h01 :=Lf (B+c) (J+e) (by omega)
  have h11 :=Lf (B+b+c) (J+j+e) (by omega)
  have hcalc :
      (J+j+e+1)*(2*(B+b+c)+2 - (J+j+e)) +
        (J+1)*(2*B+2 - J) =
      (J+e+1)*(2*(B+c)+2 - (J+e)) +
        (J+j+1)*(2*(B+b)+2 - (J+j)) +
        2*C4 b j c e := by
    unfold C4
    zify [hec,show J+j+e≤2*(B+b+c)+2 by omega,
      show J≤2*B+2 by omega,show J+e≤2*(B+c)+2 by omega,
      show J+j≤2*(B+b)+2 by omega]
    ring
  change 2*OU B J= _ at h00
  change 2*OU (B+b) (J+j)= _ at Kr
  change 2*OU (B+c) (J+e)= _ at h01
  change 2*OU (B+b+c) (J+j+e)= _ at h11
  rw [← h00,← Kr,← h01,← h11] at hcalc
  omega
private theorem eaw {f g:lK F} (hf :f≠0) (hg:g≠0)
    (hrel :oZ f g) (B J:ℕ) (hJB:J≤B) :
    lz F
      ((cap F (B+f.totalDegree+g.totalDegree) (J+f.degreeOf 1+g.degreeOf 1)).map
        (Aa F (nI {f,g})).toLinearMap) ≤
      C4 f.totalDegree (f.degreeOf 1) g.totalDegree (g.degreeOf 1) := by
  let I:oj (lK F) :=nI {f,g}
  let V:=cap F (B+f.totalDegree+g.totalDegree) (J+f.degreeOf 1+g.degreeOf 1)
  let q:=(Aa F I).toLinearMap
  let π:=q.domRestrict V
  let K:=(p5 π).map V.subtype
  let U:=multiples f (B+g.totalDegree) (J+g.degreeOf 1)
  let W:=multiples g (B+f.totalDegree) (J+f.degreeOf 1)
  let T:=multiples (f * g) B J
  have hU {p:lK F} : p∈U↔p∈V∧f∣p:= by
    simpa [U,V,zi ,Iw ,Dz] using
      (mem_multiples hf (p:=p) (B:=B+g.totalDegree) (J:=J+g.degreeOf 1))
  have hW {p:lK F} : p∈W↔p∈V∧g∣p:= by
    simpa [W,V,zi ,Iw ,Dz] using
      (mem_multiples hg (p:=p) (B:=B+f.totalDegree) (J:=J+f.degreeOf 1))
  have hT {p:lK F} : p∈T↔p∈V∧f * g∣p:= by
    simpa [T,V,totalDegree_mul_of_isDomain hf hg,G2 hf hg,
      zi ,Iw ,Dz] using
      (mem_multiples (vj hf hg) (p:=p) (B:=B) (J:=J))
  have hUW:U ⊓ W=T:= by
    ext p
    simp only [zqd,hU,hW,hT]
    exact ⟨fun ⟨⟨hp,hf'⟩,⟨_,hg'⟩⟩=>⟨hp,hrel.mul_dvd hf' hg'⟩,
      fun ⟨hp,hd⟩=>⟨⟨hp,(FQ f g).trans hd⟩,⟨hp,(Fa g f).trans hd⟩⟩⟩
  have hinK {p:lK F} (hp:p∈V) (hI:p∈I) :p∈K:= by
    refine ⟨⟨p,hp⟩,?_,rfl⟩
    exact LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hI)
  have hfI:f∈I:=vk (by simp)
  have hgI:g∈I:=vk (by simp)
  have hle :U ⊔ W≤K:= by
    apply sup_le
    · intro p hp
      obtain ⟨hp,d,rfl⟩:=hU.mp hp
      exact hinK hp (LQ _ _ hfI)
    · intro p hp
      obtain ⟨hp,d,rfl⟩:=hW.mp hp
      exact hinK hp (LQ _ _ hgI)
  have hdim:=zd hle
  have hsum:=Nr U W
  rw [hUW,a4b hf,a4b hg,a4b (vj hf hg)]
    at hsum
  have hnull:=π.finrank_range_add_finrank_ker
  rw [Mj,finrank_restrictCappedDegree] at hnull
  change lz F (V.map q)+Module.finrank F (p5 π) =
    OU (B+f.totalDegree+g.totalDegree) (J+f.degreeOf 1+g.degreeOf 1) at hnull
  rw [Submodule.finrank_map_subtype_eq] at hdim
  have hcount:=dEy B J f.totalDegree (f.degreeOf 1) g.totalDegree (g.degreeOf 1)
    hJB (x7 f 1) (x7 g 1)
  change lz F (V.map q)≤_
  omega
private theorem eaS {M:Type} [Au M] [yL F M]
   (V:ℕ→uh F M) [∀ N,oy F (V N)] (hmono:zh V)
   (hex : ∀ x :M,∃ N,x∈V N) (d:ℕ)
   (hb : ∀ N,lz F (V N)≤d) :
   oy F M∧lz F M≤d:= by
 classical
 let P:ℕ→Prop := fun k => ∃ N,lz F (V N)=k
 obtain ⟨N,hN⟩:=Nat.findGreatest_spec (P:=P) (hb 0) ⟨0,rfl⟩
 have htop:V N = ⊤ := by
   apply top_unique
   intro x _
   obtain ⟨n,hn⟩:=hex x
   have hle :V N≤V (max N n) :=hmono (Bf _ _)
   have hdim:lz F (V (max N n))≤lz F (V N) := by
     rw [hN]
     exact Nat.le_findGreatest (P:=P) (hb _) ⟨_,rfl⟩
   rw [Submodule.eq_of_le_of_finrank_le hle hdim]
   exact hmono (FU _ _) hn
 let E :V N ≃ₗ[F] M:=(LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv
 exact ⟨G3 E.toLinearMap E.surjective,E.finrank_eq.symm.trans_le (hb N)⟩
private theorem dhC (f g:lK F) (htop:nI {f,g} = ⊤) (d:ℕ) :
  oy F (aBX f g)∧lz F (aBX f g)≤d:= by
 let:Subsingleton (aBX f g) :=Ideal.Quotient.subsingleton_iff.mpr htop
 exact ⟨II,(Ww F _).trans_le (N0 d)⟩
theorem proof :akQ.c5:= by
 intro F _ f g b j c e hrel hjb hec hfb hfj hgc hge
 have hfI:f∈nI ({f,g} : Set (lK F)) :=vk (by simp)
 have hgI:g∈nI ({f,g} : Set (lK F)) :=vk (by simp)
 by_cases hf :f=0
 · have hu:yo g:=hrel (hf ▸ dvd_zero g) dvd_rfl
   exact dhC f g (G0 _ hgI hu) _
 by_cases hg:g=0
 · have hu:yo f :=hrel dvd_rfl (hg ▸ dvd_zero f)
   exact dhC f g (G0 _ hfI hu) _
 let I:oj (lK F) :=nI {f,g}
 let q:=(Aa F I).toLinearMap
 let V (N :ℕ) :=
   (cap F (2*N+f.totalDegree+g.totalDegree) (N+f.degreeOf 1+g.degreeOf 1)).map q
 have hmono:zh V:= by
   intro N M hNM
   apply zzl
   intro p hp
   obtain ⟨ht,hj⟩:=aOM.mp hp
   exact aOM.mpr ⟨by omega,by omega⟩
 have hex (x :aBX f g) : ∃ N,x∈V N := by
   obtain ⟨p,rfl⟩:=Eg x
   refine ⟨p.totalDegree,p,aOM.mpr ⟨by omega,?_⟩,rfl⟩
   have :=x7 p 1
   omega
 obtain ⟨hfin,hle⟩:=eaS V hmono hex _ fun N =>
   eaw hf hg hrel (2*N) N (by omega)
 have hpad:=(cappedDegreeMixedVolume_mono_left (c:=e) (b:=c) hfb hfj)
 have hmix :=cappedDegreeMixedVolume_mono_right (x7 f 1)
   (x7 g 1) hec hgc hge
 have hcap:C4 b j c e=b*e+c*j - j*e := by
   have hsub:j*e≤b*e+c*j :=
     (Nat.mul_le_mul_right _ hjb).trans (Nat.le_add_right _ _)
   unfold C4
   zify [hec,hsub]
   ring
 exact ⟨hfin,hle.trans ((hmix.trans hpad).trans_eq hcap)⟩
end
end bRK
end
section
namespace cy3
noncomputable section
open cu gT pI ac2 akQ
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev aL1 :=mD (Fin 2) aZ
private abbrev aki:Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
 (finSumFinEquiv (m:=2) (n:=2)).symm.trans (Equiv.sumComm (Fin 2) (Fin 2))
private def aEM:ov ≃+* aL1 :=
 ((Ok FX aki).trans
   (VS FX (Fin 2) (Fin 2))).toRingEquiv
private theorem go1 :Dk =
    (c9 aL1 vR).comp aEM.toRingHom:= by
  apply qU
  · intro c
    simp [Dk,aEM]
    rfl
  · intro i
    rw [t7,Dk,Kz]
    change _=c9 aL1 vR
      (VS FX (Fin 2) (Fin 2)
        (Ok FX aki (cy i)))
    rw [Vl,MvPolynomial.rename_X,MvPolynomial.algebraMap_def]
    trans Sum.elim cy (fun j=>lV (ek j)) (aki i)
    · fin_cases i <;> rfl
    · cases aki i <;> simp [ek]
private abbrev Ek :zm aL1 :=
 (Ea aZ).map lV
private theorem dIH (e :ov ≃+* aL1) :
  letI:=((c9 aL1 vR).comp e.toRingHom).toAlgebra
  Df (Ek.map e.symm) vR :=
 IsLocalization.isLocalization_of_base_ringEquiv Ek vR e.symm
private theorem fVO {R S:Type*} [pz R] [pz S] [p6 R S]
    [DecompositionMonoid R] (M:zm R) [Df M S] {a b:R}
    (hab:oZ a b) :oZ (c9 R S a) (c9 R S b) := by
  intro d ha hb
  obtain ⟨c,u,rfl⟩:=IsLocalization.exists_mk'_eq M d
  have hcu:=IsLocalization.mk'_spec S c u
  have aG3 (x :R) (hx :IsLocalization.mk' S c u∣c9 R S x) :
      ∃ t:M,c∣(t:R)*x := by
    have hmem:c9 R S x∈(nI {c}).map (c9 R S) := by
      rw [sS ,uz ,UZ,← hcu,
        (Mw S u).mul_right_dvd]
      exact hx
    obtain ⟨t,ht,htx⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M S _ _).mp hmem
    exact ⟨⟨t,ht⟩,Ideal.mem_span_singleton.mp htx⟩
  obtain ⟨m,hm⟩:=aG3 a ha
  obtain ⟨n,hn⟩:=aG3 b hb
  obtain ⟨x,y,hx,hy,rfl⟩:=exists_dvd_and_dvd_of_dvd_mul hm
  have hyn:y∣(n:R) :=
    (hab.of_dvd_left hy).dvd_of_dvd_mul_right ((Fa y x).trans hn)
  have hu:yo (c9 R S (x*y)) := by
    rw [ox]
    exact (G6 (zc _ hx) (Mw S m)).mul
      (G6 (zc _ hyn) (Mw S n))
  apply G6 _ hu
  rw [← hcu]
  exact FQ _ _
private theorem cFp (φ:ov →+* vR) (k :Fin 4)
    (e :ov ≃+* aL1)
    (hφ:φ=(c9 aL1 vR).comp e.toRingHom)
    (hfinite : ∀ I:oj ov,xN I →
      oy aQ (Zj φ I) ∧
        lz aQ (Zj φ I)=pN I k) :
    aSD aQ φ k := by
  subst φ
  let:p6 ov vR :=
    ((c9 aL1 vR).comp e.toRingHom).toAlgebra
  let M:zm Ambient:=Ek.map e.symm
  let:Df M vR:=dIH e
  refine ⟨zsF vR M,hfinite,?_,?_⟩
  · intro I hI hproper
    change I.map (c9 ov vR) ≠ ⊤ at hproper
    change (I.map (c9 ov vR)).IsPrime ∧
      (I.map (c9 ov vR)).comap (c9 ov vR)=I
    have hd:=(GF M vR I).mp hproper
    exact ⟨Kl M vR I hI hd,
      LO M vR hI hd⟩
  · intro a b hab
    exact fVO M hab
theorem proof :akQ.c2 := by
 constructor
 · refine cFp Dk 0 aEM go1 ?_
   intro I hI
   exact ⟨hI.bg9,rfl⟩
 · refine cFp CG 3 Jl ?_ ?_
   · exact aVL
   · intro I hI
     exact ⟨hI.jet_finite,rfl⟩
end
end cy3
end
section
namespace cyY
theorem proof :aeE.c3:= by
 intro F _ P Q u j v k hproper hP₀ hP₁ hQ₀ hQ₁
 let:z9 F:=Xx
 let:z9 (aeE.lK F) :=
   zhK (Fin 2)
 have hrel :oZ P Q :=
   zgX
     (fun h=>hproper.left_ne h.1) hproper.no_common
 exact bRJ.proof F P Q u j v k hrel hP₀ hP₁ hQ₀ hQ₁
end cyY
end
section
namespace cyX
theorem proof :aeE.c2 := by
 intro F _ P Q b j c k hj hk hProper hPb hPj hQc hQk
 have hRel:oZ P Q :=
  zgX
   (fun h=>hProper.left_ne h.1) hProper.no_common
 exact bRK.proof F P Q b j c k hRel hj hk hPb hPj hQc hQk
end cyX
end
section
namespace aw7
open xE akL aY8
open scoped BigOperators
noncomputable section
private abbrev Slot:=Σ _:ℕ,Σ _:ℕ,Σ _:ℕ,ℕ
private def slots (b j:ℕ) :nX Slot :=
  (t4 (min b (j/3)+1)).sigma (fun z =>
    (t4 (min (b - z) ((j-3*z)/2)+1)).sigma (fun y =>
      (t4 (min (b - z - y) (j-3*z - 2*y)+1)).sigma (fun x =>
        t4 (b - z - y - x+1))))
private def a8D (q:Slot) :ℕ:=q.2.2.2+q.2.2.1+q.2.1+q.1
private def jT (q:Slot) :ℕ:=q.2.2.1+2*q.2.1+3*q.1
private theorem b82 (q:Slot) (b j:ℕ) :
   q∈slots b j↔a8D q≤b∧jT q≤j:= by
 rcases q with ⟨z,y,x,a⟩
 simp only [slots,Finset.mem_sigma,Finset.mem_range,a8D,jT]
 constructor
 · rintro ⟨hz,hy,hx,ha⟩
   exact ⟨by omega,by omega⟩
 · rintro ⟨hb,hj⟩
   exact ⟨by omega,by omega,by omega,by omega⟩
private theorem dFA (b j:ℕ) : (slots b j).card=Pc b j:= by
 simp only [slots,Pc,Finset.card_sigma,Finset.card_range]
private def aQs (e :Jp) :Slot:=⟨e 3,e 2,e 1,e 0⟩
private def a3Q (q:Slot) :Jp :=
 Finsupp.equivFunOnFinite.symm ![q.2.2.2,q.2.2.1,q.2.1,q.1]
private theorem ay9 (e :Jp) :e.weight BU=a8D (aQs e) := by
 simp [Mz ,WX ,BU,a8D,aQs,zi]
private theorem VB (e :Jp) :e.weight Oq=jT (aQs e) := by
 simp [Mz ,WX ,Oq,jT,aQs]
 ring
private theorem d5h (e :Jp) :a3Q (aQs e)=e := by
 ext i
 fin_cases i <;> simp [a3Q,aQs]
private theorem deI (q:Slot) :aQs (a3Q q)=q:= by
 rcases q with ⟨z,y,x,a⟩
 simp [aQs,a3Q]
private theorem dFz (b j d:ℕ) (hd:d≤b) :
   ((slots b j).filter (fun q=>a8D q=d)).card =
     (adw d j).card:= by
 apply Finset.card_nbij' a3Q aQs
 · intro q hq
   obtain ⟨hmem,hgrade⟩:=Finset.mem_filter.mp hq
   have hw:=(b82 q b j).mp hmem
   apply azA.mpr
   change ((a3Q q).weight BU:ℤ)=d ∧
     ((a3Q q).weight Oq:ℤ)≤j
   rw [ay9,VB,deI]
   exact ⟨by exact_mod_cast hgrade,by exact_mod_cast hw.2⟩
 · intro e he
   have hmem:=azA.mp he
   change (e.weight BU:ℤ)=d∧(e.weight Oq:ℤ)≤j at hmem
   rw [ay9,VB] at hmem
   refine Finset.mem_filter.mpr ⟨(b82 _ b j).mpr ⟨?_,?_⟩,?_⟩
   · omega
   · omega
   · omega
 · exact fun q _=>deI q
 · exact fun e _=>d5h e
private theorem gxX (b j:ℕ) :
   (Pc b j:ℤ) =
     ∑ d∈t4 (b+1),((adw d j).card:ℤ) := by
 rw [← Nat.cast_sum]
 congr 1
 rw [← dFA]
 calc
   _ = ∑ d∈t4 (b+1),((slots b j).filter (fun q=>a8D q=d)).card:= by
     apply Finset.card_eq_sum_card_fiberwise
     intro q hq
     have hg:=((b82 q b j).mp hq).1
     exact Finset.mem_range.mpr (by omega)
   _ = _:=zg rfl fun d hd =>
     dFz b j d (by simpa using Finset.mem_range.mp hd)
private theorem dFr (d j:ℕ) :
    ((adw d j).card:ℤ)=gaussian 3 d j:= by
  have h (b:ℕ) :=(gxX b j).symm.trans (dgv b j)
  cases d with
  | zero=>simpa using h 0
  | succ d =>
      have hs :=h (d+1)
      rw [zpB (fun k=>((adw k j).card:ℤ)) (d+1),
        zpB (fun k=>gaussian 3 k j) (d+1),h d] at hs
      exact add_left_cancel hs
private theorem dWc (u:ℕ) :J4 u=row 0 u:= by
 have hdiv : (u:ℤ)/6=((u/6:ℕ) :ℤ) :=(KA u 6).symm
 have hmod: (u:ℤ) % 6=((u % 6:ℕ) :ℤ) :=(Int.natCast_mod u 6).symm
 simp only [bLJ,J4 ,xW (show ¬ (u:ℤ)<0 by omega),hdiv,hmod]
 unfold FI.Lw
 have hr :u % 6<6:=Nat.mod_lt _ (by decide)
 generalize u/6=q
 generalize u % 6=r at hr ⊢
 by_cases hq:q<2
 · interval_cases q <;> interval_cases r <;> decide
 have hq₁:1≤q:= by omega
 have hq₂:2≤q:= by omega
 have hd₃:6∣q*(q - 1)*(q - 2) := by
   simpa [Nat.descFactorial_succ,Nat.factorial_succ,p9,JK,pU] using
    Nat.factorial_dvd_descFactorial q 3
 have h₃:=oD (fun n:ℕ=>(n:ℤ)) (Nat.mul_div_cancel' hd₃)
 simp only [Gi ,In,KA,G4 hq₁,
   G4 hq₂,Np] at h₃
 have hcubic:36*((q:ℤ)*((q:ℤ) - 1)*((q:ℤ) - 2)/6) =
    6*(q:ℤ)*((q:ℤ) - 1)*((q:ℤ) - 2) := by
   linear_combination 6*h₃
 interval_cases r <;>
   norm_num [FI.coefficients,xI,Gi ,KA,
    G4 hq₁,G4 hq₂] <;>
   rw [hcubic] <;> ring
private theorem dWb (u:ℤ) :J4 u=row 0 u:= by
 by_cases hu:u<0
 · simp [J4 ,hu,bgV _ hu]
 · simpa only [JW (show 0≤u by omega)] using dWc u.toNat
theorem proof :akL.c2 := by
 intro d u
 by_cases hd:d<0
 · have hz :adw d u = ∅ := by
     apply Finset.eq_empty_iff_forall_notMem.mpr
     intro e he
     have hg:=(azA.mp he).1
     omega
   simp [hz,gd,hd]
 by_cases hu:u<0
 · have hz :adw d u = ∅ := by
     apply Finset.eq_empty_iff_forall_notMem.mpr
     intro e he
     have hw:=(azA.mp he).2
     omega
   simp [hz,gd,hu]
 let v :=(min u (3*d)).toNat
 have hv : (v :ℤ)=min u (3*d) :=JW (by omega)
 have hd' : (d.toNat :ℤ)=d:=JW (by omega)
 have hclip:adw d u=adw d v := by
   ext e
   simp only [azA,bob,FK,hv]
   rw [ay9,VB]
   unfold a8D jT
   omega
 calc
   _=((adw d.toNat v).card:ℤ) := by rw [hd',hclip]
   _=gaussian 3 d.toNat v :=dFr d.toNat v
   _=gd d u:= by
     rw [cTC]
     simp only [← dWb,hd',hv]
     simp [gd,hd,hu]
     ring_nf
end
end aw7
end
section
namespace bjw
noncomputable section
open aR xE akL MvPolynomial
open scoped BigOperators Pointwise
private structure Certificate (F:Flag) (p:MI) :Prop where
 old_mem:p∈ahV F
 contact_mem:alM p∈vh oH F.order.toNat
private def aL6 (A B:Flag) :Flag :=
 ⟨A.degree+B.degree,A.lower+B.lower,A.upper+B.upper,A.cap+B.cap,
   A.order+B.order⟩
private theorem Certificate.mul {A B:Flag} {p q:MI}
    (hp:Certificate A p) (hq:Certificate B q) :
    Certificate (aL6 A B) (p*q) := by
  constructor
  · change ∀ e∈(p*q).support,e∈arP (aL6 A B)
    intro e he
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (support_mul p q he)
    have ha' : a∈arP A:=hp.old_mem ha
    have hb' : b∈arP B:=hq.old_mem hb
    simp only [arP,FK,aL6,qm,Hw ,
      xI] at ha' hb' ⊢
    exact ⟨by omega,by omega,by omega,by omega⟩
  · rw [ox]
    apply MS oH
      (show (aL6 A B).order.toNat≤A.order.toNat+B.order.toNat by
        change (A.order+B.order).toNat≤A.order.toNat+B.order.toNat
        omega)
    exact yU hp.contact_mem hq.contact_mem
private theorem cEM:Certificate ⟨0,0,0,0,0⟩ 1 := by
 constructor
 · change ∀ e∈(1 :MI).support,e∈arP ⟨0,0,0,0,0⟩
   intro e he
   rw [support_one,Finset.mem_singleton] at he
   subst e
   simp [arP]
 · simp
private def bNg (n:ℕ) (F:Flag) :Flag :=
 ⟨(n:ℤ)*F.degree,(n:ℤ)*F.lower,(n:ℤ)*F.upper,(n:ℤ)*F.cap,
   (n:ℤ)*F.order⟩
private theorem Certificate.pow {F:Flag} {p:MI} (hp:Certificate F p) (n:ℕ) :
   Certificate (bNg n F) (p^n) := by
 induction n with
 | zero=>simpa [bNg] using cEM
 | succ n ih =>
    simpa [bNg,aL6,Nat.cast_succ,add_mul,Dw] using ih.mul hp
private abbrev x0:MI:=cy 0
private abbrev x1 :MI:=cy 1
private abbrev x2 :MI:=cy 2
private abbrev x3:MI:=cy 3
private abbrev U:MI:=x0 - x2 + x3
private def factor (j:Fin 11) :MI :=
 ![x0,x1,x2,x3,x0 - x1 + x2 - x3,x0 - x1,x0 - x1 + x2,
   x0*x1 - x1*x1 + x0*x2,
   x0*x3 - x0*x1 - x1*x2 + x1*x1,
   -(x0*x3) - x0*x2 - x2*x2 + x1*x3 + x1*x2,
   x0*x0*x3 + x0*x0*x2 - (2 :ℕ)•(x0*x1*x2) - x0*x1*x1 + x1*x1*x1] j
private def ct2 (j:Fin 11) :MI :=
 ![x0 + x1 - x2 + x3,x1,x2,x3,x0,x0 - x2 + x3,x0 + x3,
   x0*x1 + x0*x2 + x3*x1 + x3*x2 - x2*x2,
   x0*x3 - x0*x1 - x2*x3 + x3*x3,
   -(x0*x3) - x0*x2 - x3*x3,
   -(x1*x1*x0)+(2 :ℕ)•(x1*U*x3)+U*U*(x3 + x2)] j
private theorem dPK (j:Fin 11) :
  alM (factor j)=ct2 j:= by
 fin_cases j <;>
  simp only [factor,ct2,two_nsmul] <;>
  simp (disch:=decide) [alM,bind₁_X_right,La,x0,x1,x2,x3,U] <;>
  ring
private def marker (j:Fin 11) :Fin 4 := ![0,1, 2,3,0,0,0,1,1, 2,1] j
private theorem b2K (j:Fin 11) :factor j≠0:= by
 intro h
 have he :=oD (eval fun i:Fin 4=>if i=marker j then (1 :ao) else 0) h
 fin_cases j <;> norm_num [factor,marker,x0,x1,x2,x3,eval_X,two_nsmul,Matrix.cons_val] at he
private theorem d5W (j:Fin 11) :factor j∈ahV (Jd j) := by
 fin_cases j <;> simp only [factor,NY ,S1]
 case' «4» =>
  refine pL _ (pQ _ (pL _ ?_ ?_) ?_) ?_
 case' «5» => refine Submodule.sub_mem _ ?_ ?_
 case' «6» => refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
 case' «7» => refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
 case' «8» =>
  refine pQ _ (pL _ (pL _ ?_ ?_) ?_) ?_
 case' «9» =>
  refine pQ _ (pQ _
   (pL _ (pL _ (SM _ ?_) ?_) ?_) ?_) ?_
 case' «10» =>
  refine pQ _
   (pL _ (pL _ (pQ _ ?_ ?_) (nsmul_mem ?_ 2)) ?_) ?_
 all_goals
  simp only [x0,x1,x2,x3,cy ,monomial_mul_monomial,z8 ,ahV,
   monomial_mem_restrictSupport]
  apply Or.inl
  simp only [arP,FK,Jd,NY ,S1 ,Oq,BU,
   qm,Il,one_smul,Hw ,Finsupp.single_apply]
  decide
private theorem dRQ :
  -(x1*x1*x0)+(2 :ℕ)•(x1*U*x3)+U*U*(x3 + x2) ∈
    vh oH 3:= by
 have h₀:x0∈vh oH 3 :=
  NX oH 0 (show 3≤oH 0 by decide)
 have h₁:x1∈vh oH 0:= by simp
 have h₂:x2∈vh oH 1 :=
  NX oH 2 (show 1≤oH 2 by decide)
 have h₃:x3∈vh oH 2 :=
  NX oH 3 (show 2≤oH 3 by decide)
 have h₀' := MS (R:=ao) oH (show 1≤3 by decide) h₀
 have h₃' := MS (R:=ao) oH (show 1≤2 by decide) h₃
 have hU:U∈vh oH 1 :=
  pQ _ (pL _ h₀' h₂) h₃'
 have hFirst:=yU (yU h₁ h₁) h₀
 have hMid :=yU (yU h₁ hU) h₃
 have hLast:=yU (yU hU hU)
  (pQ _ h₃' h₂)
 exact pQ _
  (pQ _ (SM _ hFirst) (nsmul_mem hMid 2)) hLast
private theorem d5O (j:Fin 11) :
   alM (factor j)∈vh oH (Jd j).order.toNat := by
 rw [dPK]
 fin_cases j <;> simp only [ct2,Jd,NY ,S1]
 case' «0» =>
   refine pQ _ (pL _ (pQ _ ?_ ?_) ?_) ?_
 case' «5» => refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
 case' «6» => refine Submodule.add_mem _ ?_ ?_
 case' «7» =>
   refine pL _ (pQ _
     (pQ _ (pQ _ ?_ ?_) ?_) ?_) ?_
 case' «8» =>
   refine pQ _ (pL _ (pL _ ?_ ?_) ?_) ?_
 case' «9» =>
   refine pL _ (pL _ (SM _ ?_) ?_) ?_
 case' «10» => exact dRQ
 all_goals
   simp only [x0,x1,x2,x3,cy ,monomial_mul_monomial,z8 ,
     monomial_mem_restrictWeightedOrder]
   apply Or.inl
   simp only [qm,Il,one_smul,oH,Matrix.cons_val]
   decide
private def a8S (s :nX (Fin 11)) (power :Fin 11→ℕ) :Flag :=
 ⟨∑ j∈s,(power j:ℤ)*(Jd j).degree,
   ∑ j∈s,(power j:ℤ)*(Jd j).lower,
   ∑ j∈s,(power j:ℤ)*(Jd j).upper,
   ∑ j∈s,(power j:ℤ)*(Jd j).cap,
   ∑ j∈s,(power j:ℤ)*(Jd j).order⟩
private theorem dHy (s :nX (Fin 11)) (power :Fin 11→ℕ) :
    Certificate (a8S s power) (∏ j∈s,factor j^power j) := by
  induction s using Finset.induction_on with
  | empty=>simpa [a8S] using cEM
  | insert j s hj ih =>
      have h:Certificate (Jd j) (factor j) :=
        ⟨d5W j,d5O j⟩
      simpa [a8S,Finset.sum_insert hj,Finset.prod_insert hj,aL6,bNg] using
        (h.pow (power j)).mul ih
private theorem dr1 (F:Flag) (power :Fin 11→ℕ) :
  aL6 (a8S yJ power) (BH F power)=F:= by
 cases F
 simp [aL6,a8S,BH]
private theorem mem_ker_iff {F:Flag} (p:ahV F) :
  p∈p5 (KP F) ↔
    alM (p:MI)∈vh oH F.order.toNat :=
 weightedTruncation_eq_zero_iff _ _ _
theorem proof :akL.c5:= by
 intro F power
 let R:=BH F power
 let T:MI := ∏ j,factor j^power j
 have hT:T≠0:=Finset.prod_ne_zero_iff.mpr fun j _=>Et _ (b2K j)
 have hCert:Certificate (a8S yJ power) T:=dHy yJ power
 let multiply :p5 (KP R) →ₗ[ao] MI :=
   (Vs ao T).comp
     ((ahV R).subtype.comp (p5 (KP R)).subtype)
 have hMul (p:p5 (KP R)) :Certificate F (multiply p) := by
   have hp:Certificate R (p.1 :MI) :=⟨p.1.2,(mem_ker_iff p.1).mp p.2⟩
   have h:=hCert.mul hp
   rw [show aL6 (a8S yJ power) R=F from dr1 F power] at h
   exact h
 let lift:=multiply.codRestrict (ahV F) fun p=>(hMul p).old_mem
 let f :=lift.codRestrict (p5 (KP F)) fun p =>
   (mem_ker_iff (lift p)).mpr (hMul p).contact_mem
 refine ⟨f,?_⟩
 intro p q hpq
 apply zS
 apply zS
 exact wY hT (oD (fun r :p5 (KP F)=>(r.1 :MI)) hpq)
end
end bjw
end
section
namespace aYY
noncomputable section
open xE akL
open Sr.aiz
private theorem dFq (hc:a9U) (d u:ℤ) :
   ((columns oH d u).card:ℤ)=gd d u:= by
 have hweight (i:Fin 4) :oH (finRotate 4 i)=Oq i:= by
   fin_cases i <;> rfl
 have h: (columns Oq d u).card=(columns oH d u).card:= by
   apply Finset.card_equiv (Finsupp.equivCongrLeft (finRotate 4))
   intro e
   simp only [aVS,Finsupp.equivCongrLeft_apply,Xg ,
     Finsupp.sum_equivMapDomain,BU,hweight]
 rw [← h,cEh hc]
private theorem cwO (e :Jp) :
    (e.weight Oq:ℤ) =
      (e.weight BU:ℤ)+(e.weight oH :ℤ)-4*(e 0:ℤ) := by
  have h:e.weight Oq+4*e 0=e.weight BU + e.weight oH := by
    simp only [Mz ,zmL,Fz]
    change e 0*0+e 1*1+e 2*2+e 3*3+4*e 0 =
      (e 0*1+e 1*1+e 2*1+e 3*1) +
        (e 0*3+e 1*0+e 2*1+e 3*2)
    omega
  omega
theorem proof :akL.c4 := by
  classical
  intro hc F
  let balance :ℤ:=F.order - 1-F.lower+F.degree
  let jO:ℤ:=min F.degree (balance/4)+1
  change _=if balance<0 then 0 else
    gd F.degree (F.order - 1) -
      gd (F.degree - jO) (F.order - 1 - 3*jO) -
      gd F.degree (F.lower - 1)+gd (F.degree - jO) (F.lower - 1)
  by_cases hb:balance<0
  · rw [Qx hb]
    have hempty :aAu F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨hg,hl,ho⟩:=b83.mp he
      have hw:=cwO e
      dsimp only [balance] at hb
      omega
    simp [hempty]
  rw [xW hb]
  have hdiv :0≤balance/4 := by omega
  by_cases hd:F.degree<0
  · have hempty :aAu F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hg:=(b83.mp he).1
      omega
    have hmin:min F.degree (balance/4)=F.degree :=min_eq_left (by omega)
    have hr :F.degree - jO = -1 := by
      dsimp only [jO]
      rw [hmin]
      omega
    simp [hempty,hr,gd,hd]
  have hremoved:0≤jO:= by
    have hmin:0≤ min F.degree (balance/4) :=le_min (by omega) hdiv
    dsimp only [jO]
    omega
  let r :=jO.toNat
  have hr : (r :ℤ)=jO:= by
    dsimp only [r]
    omega
  have hcap (e :Jp) :e 0< r↔(e 0:ℤ)≤ min F.degree (balance/4) := by
    dsimp only [jO] at hr
    omega
  let DV:=alA oH F.degree (F.order - 1) 0 r
  let old:=alA Oq F.degree (F.lower - 1) 0 r
  have hsub:old⊆DV:= by
    intro e he
    obtain ⟨hg,hi,ha⟩:=aVR.mp he
    have ha' := (le_min_iff.mp ((hcap e).mp ha)).2
    have hw:=cwO e
    have hbal:4*(e 0:ℤ)≤balance := by omega
    dsimp only [balance] at hbal
    exact aVR.mpr ⟨hg,by omega,ha⟩
  have hdiff :aAu F=DV \ old:= by
    ext e
    rw [b83,Finset.mem_sdiff]
    change ((e.weight BU:ℤ)=F.degree∧F.lower≤(e.weight Oq:ℤ) ∧
      (e.weight oH :ℤ)<F.order)↔e∈DV∧e∉old
    simp only [DV,old,aVR]
    constructor
    · rintro ⟨hg,hi,ho⟩
      have hw:=cwO e
      have hgrade :=Finsupp.le_weight BU (s :=(0:Fin 4)) (by decide) e
      have hd' : (e 0:ℤ)≤F.degree := by omega
      have hb' : 4*(e 0:ℤ)≤balance := by
        dsimp only [balance]
        omega
      have ha :=(hcap e).mpr (le_min hd' (by omega))
      refine ⟨⟨hg,by omega,ha⟩,?_⟩
      intro he
      have hi' := he.2.1
      omega
    · rintro ⟨⟨hg,ho,ha⟩,hn⟩
      refine ⟨hg,?_,by omega⟩
      by_contra! hi
      exact hn ⟨hg,by omega,ha⟩
  have hcard:=R9 hsub
  rw [← hdiff] at hcard
  have hcontact :=cEd oH F.degree (F.order - 1) 0 r
  have hold:=cEd Oq F.degree (F.lower - 1) 0 r
  change (DV.card:ℤ)= _ at hcontact
  change (old.card:ℤ)= _ at hold
  simp only [dFq hc,hr,show (oH 0:ℤ)=3 by rfl,
    p9  jO 3] at hcontact
  simp only [cEh hc,hr,show (Oq 0:ℤ)=0 by rfl,th,sub_zero] at hold
  omega
end
end aYY
end
section
namespace bjv
open xE akL
noncomputable section
private def alA (d u cap:ℤ) :nX Jp :=
 (adw d u).filter fun e=>(e 3:ℤ)≤ cap
private theorem aVR {d u cap:ℤ} {e :Jp} :
  e∈alA d u cap↔e∈adw d u∧(e 3:ℤ)≤ cap :=
 Pk
private theorem cEl {s t:nX Jp} (h:t⊆s) :
  ((s \ t).card:ℤ)=(s.card:ℤ)-(t.card:ℤ) := by
 have hc:=R9 h
 omega
private theorem cD8 (hc:a9U) (d u cap:ℤ) :
    ((alA d u cap).card:ℤ)=U1 d u cap:= by
  by_cases hcap:cap<0
  · have hempty :alA d u cap = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have h:=(aVR.mp he).2
      omega
    simp [hempty,U1,hcap]
  · let r :=(cap+1).toNat
    have hr : (r :ℤ)=cap+1 :=JW (by omega)
    have eq :alA d u cap=Sr.aiz.alA Oq d u 3 r := by
      ext e
      rw [aVR,Sr.aiz.aVR,azA,
        bob,FK]
      have er : (e 3:ℤ)< r↔(e 3:ℤ)≤ cap:= by omega
      constructor
      · rintro ⟨⟨a,b⟩,c⟩
        exact ⟨a,b,by omega⟩
      · rintro ⟨a,b,c⟩
        exact ⟨⟨a,b⟩,by omega⟩
    rw [eq,Sr.aiz.cEd,Sr.aiz.cEh hc,Sr.aiz.cEh hc]
    simp only [U1,xW hcap,hr,show (Oq 3:ℤ)=3 by rfl]
    rw [show d-(cap+1)=d-cap-1 by omega,p9]
private theorem dFm {d u v cap:ℤ} (huv :u≤v) :
  alA d u cap⊆alA d v cap:= by
 intro e he
 rw [aVR,azA] at he ⊢
 obtain ⟨⟨hd,hu⟩,hcap⟩:=he
 exact ⟨⟨hd,hu.trans huv⟩,hcap⟩
private theorem eGk (F:Flag) :
    aWa F =
      alA F.degree F.upper F.cap \
        alA F.degree (min F.upper (F.lower - 1)) F.cap:= by
  ext e
  simp only [eAc,arP,Finset.mem_sdiff,aVR,
    azA,bob,FK]
  constructor
  · rintro ⟨hd,hl,hu,hcap⟩
    refine ⟨⟨⟨hd,hu⟩,hcap⟩,?_⟩
    rintro ⟨⟨_,hcut⟩,_⟩
    have h:=hcut.trans (min_le_right _ _)
    omega
  · rintro ⟨⟨⟨hd,hu⟩,hcap⟩,hexcluded⟩
    refine ⟨hd,?_,hu,hcap⟩
    by_contra hl
    exact hexcluded ⟨⟨hd,le_min hu (by omega)⟩,hcap⟩
theorem proof :akL.c3:= by
 intro hc F
 rw [eGk,cEl (dFm (min_le_left _ _)),
  cD8 hc,cD8 hc,oldCount]
end
end bjv
end
section
namespace K1_13_7_4
noncomputable section
open Polynomial aR wH
open scoped BigOperators
def IM (S:ao[X]) :af 3 →+* af 3 :=
 qM lV (fun i=>cy i+MvPolynomial.C (jet S i))
theorem Yk :p7 qY :=
 (c9 iP cH).injective.comp
   (LR ao[X] iP)
def aH2 :af 3 →+* Lower :=oz qY
@[simp] theorem gP1 (F:af 3) :aH2 F=fW F:=rfl
theorem d3Y (V:uh ao (af 3)) (I:Set (oj aU))
    (hfin:I.Finite) (hw : ∀ p∈I,∃ R∈V,fW R∉p) :
    ∃ R∈V,∀ p∈I,fW R∉p:= by
  have :Finite I:=hfin.to_subtype
  let lin:af 3 →ₗ[ao] Lower := {
    toFun:=aH2
    map_add' := qm aH2
    map_smul' := by
      intro a R
      simp only [RingHom.id_apply,QL,ox]
      congr 1
      rw [ Xu ao ao[X] (af 3),
        Xu ao cH aU]
      change aH2 (lV (c9 ao ao[X] a)) =
        lV (c9 ao cH a)
      rw [aH2,wR]
      congr 1 }
  let W (p:I) :uh ao V :=
    ((p.val.restrictScalars ao).comap lin).comap V.subtype
  have hW (p:I) :W p ≠ ⊤ := by
    obtain ⟨R,hR,hn⟩:=hw p.val p.property
    intro h
    apply hn
    change (⟨R,hR⟩:V)∈W p
    simp [h]
  obtain ⟨R,hR⟩:=Submodule.exists_forall_notMem_of_forall_ne_top
    (ι:=I) (K:=ao) (M:=V) W hW
  exact ⟨R.val,R.property,fun p hp=>hR ⟨p,hp⟩⟩
theorem cbc {P Q:af 3} {p:oj aU} :
  Ib P Q≤p↔fW P∈p∧fW Q∈p:= by
 simp [Ib,Ideal.span_le,Wl,Yo]
theorem bPj {P Q R:af 3} {p:oj aU} :
  asD P Q R≤p↔fW P∈p∧fW Q∈p∧fW R∈p:= by
 simp [asD,Ideal.span_le,Wl,Yo]
theorem aD7 {P Q:af 3} (hpq:bbj P Q)
  {p:oj aU} (hp:p∈(Ib P Q).minimalPrimes) :p.height=2 := by
 have :p.IsPrime :=hp.isPrime
 have hncard: ({fW P,fW Q} : Set aU).ncard≤2 :=
  (Set.ncard_insert_le _ _).trans (by simp)
 have hle :p.height≤2 :=
  (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hp).trans (by exact_mod_cast hncard)
 have hP:=(cbc.mp hp.le).1
 have hQ:=(cbc.mp hp.le).2
 have hnP:fW P≠0:= by
  simpa [fW] using (Pf _ Yk).ne hpq.1
 have hpbot:p ≠ ⊥ := fun h=>hnP (Ideal.mem_bot.mp (h ▸ hP))
 have hone :1≤p.height:= by
  have h:=Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hpbot)
  simpa [Ideal.height_bot] using h
 have hnot:p.height≠1 := by
  intro h
  have hprincipal:=UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h
  obtain ⟨x,hx⟩:=hprincipal.principal
  change p=nI {x} at hx
  have hxP:x∣fW P:=Ideal.mem_span_singleton.mp (by rw [← hx]; exact hP)
  have hxQ:x∣fW Q:=Ideal.mem_span_singleton.mp (by rw [← hx]; exact hQ)
  have hxunit :yo x :=hpq.2.2 hxP hxQ
  exact Ideal.IsPrime.ne_top' (hx.trans (Ideal.span_singleton_eq_top.mpr hxunit))
 exact le_antisymm hle ((ENat.add_one_le_iff (by simp : (1 :ℕ∞) ≠ ⊤)).mpr
  (lt_of_le_of_ne hone (Ne.symm hnot)))
theorem emB (p:pG aU) :p.asIdeal.height≤3:= by
 have h:=Ideal.height_le_ringKrullDim_of_isPrime (I:=p.asIdeal)
 have hd:ringKrullDim aU=3:= by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,ringKrullDim_eq_zero_of_field]
  simp
 rw [hd] at h
 exact WithBot.coe_le_coe.mp h
theorem br7 {q:pG aU} {J:oj aU}
    (hq:q.asIdeal∈J.minimalPrimes) :yB q J < ⊤ := by
  let A:=Ee q.asIdeal
  let L:=J.map (c9 aU A)
  change qJ A (A ⧸ L) < ⊤
  have hmin:t3 A∈L.minimalPrimes := by
    rw [show L=J.map (c9 aU A) from rfl,
      IsLocalization.minimalPrimes_map q.asIdeal.primeCompl A,Set.mem_preimage,
      SD A q.asIdeal]
    exact hq
  have :IsArtinianRing (A ⧸ L) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing L hmin
  exact lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L,
        isArtinian_of_surjective_algebraMap (Eg (I:=L))⟩))
def pointPrime (y :Sz) :pG Lower :=
 ⟨oF y,RingHom.ker_isPrime (MvPolynomial.eval y)⟩
theorem cvd {q:pG aU} {F:aU} {d:ℕ}
  (hd:0<d) (h:afc q F d) :F∈q.asIdeal:= by
 let A:=Ee q.asIdeal
 change c9 aU A F∈t3 A^d at h
 have hm:c9 aU A F∈t3 A:= by
  simpa using JM (I:=t3 A) hd h
 change F∈(t3 A).under aU at hm
 rwa [SD A q.asIdeal] at hm
theorem cb5 {F:af 3} {S:ao[X]} {d:ℕ} (hF:wU F S d) :
   afc (pointPrime (Ud S)) (fW F) d:= by
 let y :=Ud S
 let q:=pointPrime y
 let A:=Ee q.asIdeal
 let ev :af 3 →+* Lower :=qM (MvPolynomial.C.comp qY)
   (fun i=>cy i-MvPolynomial.C (y i))
 have hev :ev.comp (IM S)=aH2 := by
   apply qU <;> intro i <;>
     simp [IM,ev,aH2,y,Ud]
 have heval :ev (IM S F)=fW F:=DFunLike.congr_fun hev F
 have hmem (i:Fin 3) :ev (cy i)∈q.asIdeal:= by
   simp [q,pointPrime,oF,ev,RingHom.mem_ker]
 have hprod (a :Fin 3 →₀ ℕ) :
     (a.prod (fun i k=>ev (cy i)^k))∈q.asIdeal^EY a := by
   unfold EY Un KH
   rw [← Zf]
   exact XG fun i _=>Nj (hmem i) (a i)
 have hrow:fW F∈q.asIdeal^d:= by
   rw [← heval,RJ (IM S F),t8]
   apply Ideal.sum_mem
   intro a ha
   rw [VO,ox ,KH,map_prod]
   apply Ideal.mul_mem_left
   have hda :d≤EY a :=hF a ha
   apply JM (I:=q.asIdeal) hda
   simpa only [wB,KH] using hprod a
 change c9 aU A (fW F)∈t3 A^d
 rw [← XJ q.asIdeal A,← Ideal.map_pow]
 exact Ideal.mem_map_of_mem _ hrow
end
end K1_13_7_4
end
section
namespace K1_13_7_4
noncomputable section
open Polynomial aR
open scoped BigOperators
def Uz {A:Type*} [qx A] :
    mD (Fin 3) A →+* mD (Fin 3) (mD (Fin 3) A) :=
  qM (MvPolynomial.C.comp lV)
    (fun i=>lV (cy i)+MvPolynomial.X i)
private theorem cco {A:Type*} [qx A] (i:Fin 3) (k :ℕ)
    (f :A) :
    (lV f+MvPolynomial.X i)^k =
      ∑ j∈t4 (k+1),Up (RD i j)
        (f^(k - j)*(k.choose j:A)) := by
  rw [Dv,add_pow]
  apply zg rfl
  intro j _
  rw [MvPolynomial.X_pow_eq_monomial,← wB,← MvPolynomial.C_eq_coe_nat,
    pU,← ox ,p9,MvPolynomial.C_mul_monomial,z8]
private theorem cs6 {A:Type*} [qx A]
    (m a :Fin 3 →₀ ℕ) (c:A) :
    (Uz (Up m c)).coeff a =
      Up (m-a) (c * ∏ i:Fin 3,((m i).choose (a i) :A)) := by
  classical
  unfold Uz
  rw [ X4 ,Finsupp.prod_pow,t7,
    MvPolynomial.coeff_C_mul]
  simp_rw [cco]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_prod]
  rw [S2]
  simp only [Vz]
  have hindex (b:Fin 3→ℕ) :
      (∑ i:Fin 3,RD i (b i)) =
        Finsupp.equivFunOnFinite.symm b:= by
    simpa using (Finsupp.univ_sum_single (Finsupp.equivFunOnFinite.symm b))
  simp_rw [hindex]
  by_cases ha : ∀ i,a i≤ m i
  · have hmem: (a :Fin 3→ℕ)∈Fintype.piFinset (fun i=>t4 (m i+1)) :=
      Fintype.mem_piFinset.mpr fun i=>Finset.mem_range_succ_iff.mpr (ha i)
    rw [Finset.sum_eq_single_of_mem (a :Fin 3→ℕ) hmem]
    · have hea :Finsupp.equivFunOnFinite.symm (a :Fin 3→ℕ)=a :=
        Finsupp.equivFunOnFinite.symm_apply_apply a
      simp only [hea,↓reduceIte]
      rw [VO,Finsupp.prod_pow,ox ,map_prod,
        Re]
      simp only [Finsupp.tsub_apply,map_natCast]
      ac_rfl
    · intro b _ hb
      have hba :Finsupp.equivFunOnFinite.symm b≠a := by
        intro h
        exact hb (by simpa using oD (fun x :Fin 3 →₀ ℕ=>(x :Fin 3→ℕ)) h)
      simp [hba]
  · push Not at ha
    obtain ⟨i,hi⟩:=ha
    have hzero : (∏ k :Fin 3,((m k).choose (a k) :A))=0 :=
      zue (vG i) (by simp [zsx hi])
    rw [hzero,th,pC]
    suffices (∑ b∈Fintype.piFinset (fun i=>t4 (m i+1)),
        if Finsupp.equivFunOnFinite.symm b=a then
          ∏ i:Fin 3,(cy i:mD (Fin 3) A)^(m i - b i) *
            ((m i).choose (b i) :mD (Fin 3) A) else 0)=0 by
      rw [this,th]
    apply Qw
    intro b hb
    have hn:Finsupp.equivFunOnFinite.symm b≠a := by
      intro h
      have hbi:=Fintype.mem_piFinset.mp hb i
      have he :b i=a i:= by
        simpa using oD (fun x :Fin 3 →₀ ℕ=>x i) h
      exact (not_lt_of_ge (Finset.mem_range_succ_iff.mp (he ▸ hbi))) hi
    simp [hn]
theorem taylor_coeff {A:Type*} [qx A] (F:mD (Fin 3) A)
  (a :Fin 3 →₀ ℕ) : (Uz F).coeff a=BV a F:= by
 unfold BV
 conv_lhs=>rw [RJ F,t8 ,S2]
 exact zg rfl fun m _=>cs6 m a (F.coeff m)
private theorem gqf (S:ao[X]) (F:af 3) (a :Fin 3 →₀ ℕ) :
    IM S (BV a F)=BV a (IM S F) := by
  have h: (oz (IM S)).comp Uz=Uz.comp (IM S) := by
    apply qU <;> intro x
    · simp [IM,Uz]
    · simp only [t7,IM,Uz,Kz ,
        qm,PM,wR,GR]
      ac_rfl
  have hc:=oD (fun P:mD (Fin 3) (af 3)=>P.coeff a)
    (C5 h F)
  simpa only [t7,MvPolynomial.coeff_map,taylor_coeff] using hc
theorem cUA (F:af 3) (S:ao[X]) (a :Fin 3 →₀ ℕ) (d:ℕ)
    (hF:wU F S d) :wU (BV a F) S (d-EY a) := by
  classical
  intro m hm
  change m∈(IM S (BV a F)).support at hm
  rw [gqf] at hm
  change d-EY a≤EY m
  by_contra! hd
  apply (MvPolynomial.mem_support_iff.mp hm)
  unfold BV
  rw [S2]
  apply Qw
  intro v hv
  rw [Vz]
  split_ifs with he
  · by_cases ha :a≤v
    · have hvd:d≤EY v :=hF v hv
      have hsum:EY v=EY a+EY m:= by
        have hv :a+m=v :=he ▸ add_tsub_cancel_of_le ha
        rw [← hv]
        simp [EY,WD,Hw ,Finset.sum_add_distrib]
      omega
    · have ⟨i,hi⟩ : ∃ i,v i<a i:= by simpa [Finsupp.le_def,not_forall] using ha
      have hz : (∏ i:Fin 3,((v i).choose (a i) :ao[X]))=0 :=
        zue (vG  i) (by simp [zsx hi])
      rw [hz,th ]
  · rfl
end
end K1_13_7_4
end
section
namespace K1_13_7_4
noncomputable section
open Polynomial aR wH
open scoped BigOperators
def c1 :Prop :=
  ∀ (q:pG aU) (F:af 3) (d:ℕ),q.asIdeal.height=2 →
    (∀ a :Fin 3 →₀ ℕ,EY a<d→fW (BV a F)∈q.asIdeal) →
    afc q (fW F) d
def c2 :Prop :=
  ∀ (n:ℕ),n=2∨n=3 →
    ∀ (q:pG aU) (F:Fin n→aU) (a :Fin n→ℕ),
      q.asIdeal.height=n →
      q.asIdeal∈(nI (oY F)).minimalPrimes →
      (∀ i,0<a i)→(∀ i,afc q (F i) (a i)) →
      (↑(∏ i,a i) :ℕ∞)≤yB q (nI (oY F))
end
end K1_13_7_4
end
section
namespace bRE
open aR wH K1_13_7_4
open scoped BigOperators
private theorem d2Y {R B:Type*} [qx R] [pz B]
    (f g:mD (Fin 3) R →+* B)
    (hC : ∀ r,f (lV r)=g (lV r))
    (I:oj B) (d:ℕ) (hI:I ^d = ⊥)
    (hX : ∀ i,f (cy i) - g (cy i)∈I)
    (F:mD (Fin 3) R)
    (hF : ∀ a,EY a<d→ g (BV a F)=0) :
    f F=0:= by
  let u (i:Fin 3) :=f (cy i) - g (cy i)
  let eval :=qM g u
  have he :eval.comp Uz=f := by
    apply qU
    · intro r
      simpa only [t7,eval,Uz,PM]
        using (hC r).symm
    · intro i
      simp only [t7,eval,Uz,Kz ,
        qm,PM,u]
      abel
  rw [← C5 he F,t7]
  conv_lhs=>rw [RJ (Uz F),t8]
  apply Qw
  intro a _
  rw [show eval=qM g u from rfl,X4 ,
    taylor_coeff]
  by_cases ha :EY a<d
  · rw [hF a ha,zero_mul]
  · have hm: (a.prod fun i k=>u i^k)∈I ^EY a := by
      unfold KH EY Un
      rw [← Zf]
      exact XG fun i _=>Nj (hX i) (a i)
    have hz : (a.prod fun i k=>u i^k)=0 :=
      Ideal.mem_bot.mp (hI ▸ JM (Nat.le_of_not_gt ha) hm)
    rw [hz,th]
private theorem cN7 {A:Type*} [pz A] (m:oj A) (d:ℕ)
  (hle :m^d≤ m) : (sI (Ideal.Quotient.factor hle))^d = ⊥ := by
 rw [Ideal.Quotient.factor_ker,← Ideal.map_pow (yl (m^d)) m d]
 exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Kh])
private theorem d4L {K A:Type*} [nq K] [PerfectField K]
   [pz A] [p6 K A] [Kc K A]
   (m:oj A) [m.IsMaximal] (d:ℕ) (hle :m^d≤ m) :
   ∃ s : (A ⧸ m) →ₐ[K] (A ⧸ (m^d)),
     ∀ y,Nq K hle (s y)=y := by
 let:nq (A ⧸ m) :=Ideal.Quotient.field m
 let π:=Nq K hle
 have hπ:SU π:=Ideal.Quotient.factor_surjective hle
 have hnil:IsNilpotent (sI π.toRingHom) :=⟨d,cN7 m d hle⟩
 exact ⟨Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K _) π hπ hnil,
   Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K _) π hπ hnil⟩
theorem proof :K1_13_7_4.c1 := by
 intro q F d _ hF
 let A:=Ee q.asIdeal
 let m:=t3 A
 change c9 aU A (fW F)∈m^d
 by_cases hd:d=0
 · simp [hd]
 let B:=A ⧸ (m^d)
 let L:=A ⧸ m
 let K:=cH
 let hle :m^d≤ m:= by
   simpa only [uW] using
     (JM (I:=m) (Nat.one_le_iff_ne_zero.mpr hd))
 let π:B →ₐ[K] L:=Nq K hle
 obtain ⟨s,hs⟩:=d4L (K:=K) m d hle
 have hnil: (sI π.toRingHom)^d = ⊥ := cN7 m d hle
 let e :aU →ₐ[K] B :=
   (Aa K (m^d)).comp (Xo K aU A)
 let f :=e.toRingHom.comp aH2
 let g:=(s.comp (π.comp e)).toRingHom.comp aH2
 have hC (r :u5 ao) :f (lV r)=g (lV r) := by
   simp only [f,g,t7,aH2,wR]
   exact (e.commutes (qY r)).trans ((s.comp (π.comp e)).commutes (qY r)).symm
 have hX (i:Fin 3) :f (cy i) - g (cy i)∈sI π.toRingHom:= by
   change π (f (cy i) - g (cy i))=0
   rw [map_sub]
   change π (f (cy i))-π (s (π (f (cy i))))=0
   rw [hs,sub_self]
 have hlow (a :Fin 3 →₀ ℕ) (ha :EY a<d) :g (BV a F)=0:= by
   have hm:c9 aU A (fW (BV a F))∈m:= by
     change fW (BV a F)∈m.under aU
     rw [SD A q.asIdeal]
     exact hF a ha
   have hz :=Ideal.Quotient.eq_zero_iff_mem.mpr hm
   change s (yl m (c9 aU A (fW (BV a F))))=0
   rw [hz,pC]
 exact Ideal.Quotient.eq_zero_iff_mem.mp (d2Y f g hC _ d hnil hX F hlow)
end bRE
end
section
namespace aRX
noncomputable section
open wH LinearMap
abbrev At (q:pG aU) :=Ee q.asIdeal
abbrev XQ (q:pG aU) (M:Type*) [Au M]
 [yL aU M] :=LocalizedModule q.asIdeal.primeCompl M
def avs (q:pG aU) (M:Type*) [Au M]
    [yL aU M] :ℕ∞ := qJ (At q) (XQ q M)
def cYq (q:pG aU) (I:oj aU) :
    XQ q (aU ⧸ I) ≃ₗ[At q] (At q ⧸ I.map (c9 aU (At q))) := by
  let S:=q.asIdeal.primeCompl
  let f :=ZJ aU (At q)
  have hI:Submodule.localized' (At q) S f I=I.map (c9 aU (At q)) := by
    rw [Submodule.localized'_eq_span,Ideal.map,nI,Algebra.coe_linearMap]
  let e :=IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (aU ⧸ I))
    (Submodule.toLocalizedQuotient' (At q) S f I)
  exact (e.extendScalarsOfIsLocalization S (At q)).trans (Submodule.quotEquivOfEq _ _ hI)
theorem b70 (q:pG aU) (I:oj aU) :
   avs q (aU ⧸ I)=yB q I :=
 (cYq q I).length_eq
theorem evG {A:Type*} [pz A] (I:oj A) (t:A) :
   qJ A ((A ⧸ I) ⧸ range (lsmul A (A ⧸ I) t)) =
     qJ A (A ⧸ I ⊔ nI {t}) := by
 let H :=(nI {t}).map (Aa A I)
 have heq :range (lsmul A (A ⧸ I) t)=H.restrictScalars A:= by
   ext x
   change (∃ y :A ⧸ I,t•y=x)↔x∈H
   simp only [H,sS ,uz ,Ideal.mem_span_singleton']
   simp [QL,p9]
 rw [heq]
 exact ((Submodule.Quotient.restrictScalarsEquiv A H).trans
   (DoubleQuot.quotQuotEquivQuotSupₐ A I (nI {t})).toLinearEquiv).length_eq
theorem evF (q:pG aU) (I:oj aU) (t:aU) :
    qJ (At q)
      ((At q ⧸ I.map (c9 aU (At q))) ⧸
        range (lsmul (At q) (At q ⧸ I.map (c9 aU (At q)))
          (c9 aU (At q) t)))=yB q (I ⊔ nI {t}) := by
  rw [evG]
  change _=qJ (At q) (At q ⧸ (I ⊔ nI {t}).map (c9 aU (At q)))
  rw [Ideal.map_sup,sS ,uz]
theorem bDL (q:pG aU) (I:oj aU) (t:aU)
    (h:IsSMulRegular (At q ⧸ I.map (c9 aU (At q))) (c9 aU (At q) t))
    (hfin:yB q (I ⊔ nI {t}) < ⊤) :
    aAR (c9 aU (At q) t) (XQ q (aU ⧸ I)) ∧
      auJ (c9 aU (At q) t) (XQ q (aU ⧸ I)) =
        ((yB q (I ⊔ nI {t})).toNat :ℤ) := by
  have hc:=cI0 (c9 aU (At q) t) (cYq q I)
  rw [hc.1,hc.2]
  have hk :=(isSMulRegular_iff_ker_lsmul_eq_bot
    (At q ⧸ I.map (c9 aU (At q))) (c9 aU (At q) t)).mp h
  unfold aAR auJ
  rw [hk,Module.length_bot,evF]
  exact ⟨⟨by simp,hfin⟩,by simp⟩
theorem cYo {p q:pG aU} (h : ¬ p.asIdeal≤q.asIdeal) :
   avs q (aU ⧸ p.asIdeal)=0:= by
 rw [b70]
 have htop:p.asIdeal.map (c9 aU (At q)) = ⊤ := by
   by_contra hne
   apply h
   intro x hx
   by_contra hn
   exact Set.disjoint_left.mp
     ((GF q.asIdeal.primeCompl (At q) _).mp hne)
     (show x∈q.asIdeal.primeCompl from hn) hx
 simp [yB,htop,Module.length_eq_zero]
theorem cYp (q:pG aU) :
  avs q (aU ⧸ q.asIdeal)=1 := by
 rw [b70]
 change qJ (At q) (At q ⧸ q.asIdeal.map (c9 aU (At q)))=1
 rw [ XJ,Module.length_eq_one_iff]
 exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal _).1
end
end aRX
end
section
namespace aqa
open wH K1_13_7_4
open scoped BigOperators
def c1 :Prop :=
  ∀ (n:ℕ),n=2∨n=3 →
    ∀ (q:pG aU),q.asIdeal.height=n →
      ∀ (f :Fin n→Local q),
        (nI (oY f)).radical=t3 (Local q) →
        ∀ (i:Fin n) (y :Local q),f i*y∈K7 f i→y∈K7 f i
def c2 :Prop :=
  ∀ (n:ℕ),n=2∨n=3 →
    ∀ (q:pG aU),q.asIdeal.height=n →
      ∀ (t:ℕ),0<t →
        ((t+n - 1).choose n:ℕ∞) ≤
          qJ (Local q) (Local q ⧸ t3 (Local q)^t)
theorem of_children (h1 :c1) (h2 :c2) :K1_13_7_4.c2 := by
  classical
  intro n hn q F a hheight hmin ha hv
  let R:=Local q
  let m:=t3 R
  let f :Fin n→R:= fun i=>c9 aU R (F i)
  let I:=nI (oY f)
  have hmap : (nI (oY F)).map (c9 aU R)=I:= by
    rw [sS ,← Set.range_comp]
    rfl
  have hrad:I.radical=m:= by
    rw [← hmap,IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes R q.asIdeal _ hmin]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have hcancel (e :Fin n→ℕ) (he : ∀ j,0<e j) (i:Fin n) (y :R)
      (hy :f i*y∈K7 (fun j=>f j^e j) i) :
      y∈K7 (fun j=>f j^e j) i:= by
    let d (j:Fin n) :ℕ:=if j=i then 1 else e j
    let g (j:Fin n) :R:=f j^d j
    have hd (j:Fin n) :0<d j:= by
      by_cases hj:j=i <;> simp [d,hj,he j]
    have hg: (nI (oY g)).radical=m :=
      (cek f d hd).trans hrad
    have hgi:g i=f i:= by simp [g,d]
    have hremain:K7 g i=K7 (fun j=>f j^e j) i:= by
      unfold K7
      congr 1
      exact Set.image_congr fun j hj=> by
        have hji:j≠i:=hj
        simp [g,d,hji]
    rw [← hremain] at hy ⊢
    exact h1 n hn q hheight g hg i y (by simpa only [hgi] using hy)
  let M := ∏ i,a i
  let b (i:Fin n) := ∏ j∈Finset.univ.erase i,a j
  have hb (i:Fin n) :0<b i:=Finset.prod_pos fun j _=>ha j
  have hab (i:Fin n) :b i*a i=M :=
    Finset.prod_erase_mul yJ a (vG i)
  let g (i:Fin n) :=f i^b i
  have hcontain:nI (oY g)≤ m^M:= by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have horder :f i∈m^a i:=hv i
    change f i^b i∈m^M
    simpa only [← pow_mul,p9 (a i) (b i),hab i] using
      Nj horder (b i)
  have hlength:=dNn hn m g hcontain (h2 n hn q hheight)
  have hscale :=c46 f b hb hcancel
  change (↑(M^n) :ℕ∞)≤yC (nI (oY g)) at hlength
  rw [hscale] at hlength
  have hprod: (∏ i,b i)*M=M^n:= by
    change (∏ i,b i)*(∏ i,a i)=M^n
    rw [← Re]
    simp only [hab,Finset.prod_const,G1 ,u9]
  have hbprod:0 < ∏ i,b i:=Finset.prod_pos fun i _=>hb i
  have hb0: (↑(∏ i,b i) :ℕ∞)≠0:= by exact_mod_cast hbprod.ne'
  rw [← hprod,ENat.natCast_mul] at hlength
  have hbound:=(ENat.mul_le_mul_left_iff hb0 (ENat.natCast_ne_top _)).mp hlength
  change (M:ℕ∞)≤yC ((nI (oY F)).map (c9 aU R))
  rw [hmap]
  exact hbound
end aqa
end
section
namespace aRV
open wH aqa IsLocalRing
private theorem evN {A B:Type*} [pz A] [pz B]
  (f :A →+* B) (hf :SU f) :
  qJ B B≤qJ A A:= by
 let:p6 A B:=f.toAlgebra
 rw [← WK (M:=B) hf]
 exact Module.length_le_of_surjective (ZJ A B) hf
theorem proof :aqa.c2 := by
  intro n hn q hq t ht
  let R:=Local q
  let K:=ResidueField R
  let m:=t3 R
  have hd:lz K (CotangentSpace R)=n:= by
    have h:=(IsRegularLocalRing.iff_finrank_cotangentSpace R).mp II
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal R,hq] at h
    exact_mod_cast h
  by_cases h:2≤t
  · let:ziC aU R :=
      Algebra.FormallySmooth.of_isLocalization q.asIdeal.primeCompl
    let:ziC cH R :=
      Algebra.FormallySmooth.comp cH aU R
    let:Kc aU R :=
      Algebra.EssFiniteType.of_isLocalization R q.asIdeal.primeCompl
    let:Kc cH R :=
      Algebra.EssFiniteType.comp cH aU R
    let:Kc cH K :=
      Algebra.EssFiniteType.of_surjective (Xo cH R K)
        (residue_surjective (R:=R))
    obtain ⟨f,hf⟩:=d4n (k :=cH) h
      (Module.finBasisOfFinrankEq K (CotangentSpace R) hd)
    change _≤qJ R (R ⧸ m^t)
    rw [WK (R:=R ⧸ m^t) Eg]
    exact (evK K n t ht).trans (evN f hf)
  · have ht' : t=1 := by omega
    subst t
    rw [uW ,show 1+n - 1=n by omega,Nat.choose_self,Np ]
    change (1 :ℕ∞)≤qJ  R K
    rw [WK  (residue_surjective (R:=R)),Module.length_eq_one]
end aRV
end
section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace aBb
noncomputable section
open cu gT YY
open scoped Polynomial
private theorem dVI {F A B:Type} [nq F] [pz A] [pz B]
  [p6 F A] [p6 F B] [y5 A] [UP B]
  [oy F A] [oy F B] (f :A →ₐ[F] B) :
  ∃ g:ℕ,0<g∧lz F B=lz F A*g:= by
 let:nq A:=fieldOfFiniteDimensional F A
 let:p6 A B:=f.toRingHom.toAlgebra
 let:IsScalarTower F A B:=IsScalarTower.of_algebraMap_eq fun r=>(f.commutes r).symm
 let:oy A B:=Module.Finite.of_restrictScalars_finite F A B
 exact ⟨lz A B,Module.finrank_pos,(Module.finrank_mul_finrank F A B).symm⟩
theorem assemble
    (seedTower : ∀ I:oj ov,I.IsPrime→UP (rM I) →
      y5 (rM I) ∧
      ∃ (f :aLP (xg I) →ₐ[aQ] abX (Si I))
        (j:abX (Si I) →ₐ[aQ] rM I),
        p7 f∧p7 j)
    (planeDegree : ∀ Q:aZ,Q≠0 →
      lz aQ (aLP (nI {Q}))= Q.totalDegree)
    (yInclusion : ∀ I:oj ov,
      ∃ j:SI (Si I) →ₐ[aQ] as2 I,p7 j) :
    YY.c2 := by
  intro I C hI hY hC hImg
  obtain ⟨hPrime,_,hFinite,hPositive⟩:=hI
  let:=hPrime
  let:=hFinite
  let:=hY
  have :UP (rM I) :=(Module.finrank_pos_iff_of_free _ _).mp hPositive
  obtain ⟨hDomain,f,j,hf,hj⟩:=seedTower I hPrime II
  have :=hDomain
  have :y5 (abX (Si I)) :=hj.isDomain j
  have :y5 (aLP (xg I)) :=hf.isDomain f
  have :oy aQ (abX (Si I)) :=
    zE j.toLinearMap hj
  have :oy aQ (aLP (xg I)) :=
    zE f.toLinearMap hf
  have hQ:oz U7 C≠0:= by
    have hinj:p7 U7 :=
      (LR L[X] FX).comp z7
    exact fun h=>hC.ne_zero ((Pf U7 hinj) (h.trans (pC _).symm))
  have hD:lz aQ (aLP (xg I))=C.totalDegree := by
    rw [hImg,planeDegree _ hQ,bnQ]
  obtain ⟨g,hg,hmul⟩:=dVI f
  rw [hD] at hmul
  obtain ⟨y,hy⟩:=yInclusion I
  have hrY:oy aQ (SI (Si I)) :=
    zE y.toLinearMap hy
  refine ⟨g,hg,⟨Ideal.IsPrime.comap oi,C,hC,hImg,II,hmul,hrY,?_⟩,?_⟩
  · exact Z0 (f :=y.toLinearMap) hy
  · rw [← hmul]
    exact Z0 (f :=j.toLinearMap) hj
end
end aBb
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Aj
noncomputable section
open Polynomial K1 gR ProximityPrize.Benchmark
def GC:K[X] →+* kB:=c9 K[X] kB
theorem aAg:p7 GC :=
 LR K[X] kB
theorem aC8:p7 sZ :=
 HZ GC aAg
theorem ari (f :K[X]) (x :K) : (jH f).eval (C x)=C (f.eval x) := by
 simp [jH,eval_map]
theorem a5o (S:nX I) (P:nC)
  (hz : ∀ i∈S,P.eval (C (node i))=0) :jH (mL node S)∣P:= by
 classical
 apply (Polynomial.map_dvd_map GC aAg
  ((S8 node S).map MO)).mp
 rw [EP ,b8d]
 apply kL.bsf _
  ((aAg.comp z7).comp IRSProfile.domain.injective)
 intro i hi
 change (P.map GC).eval (GC (C (node i)))=0
 rw [ZK,hz i hi,pC]
theorem bYN (G A B:kB[X])
  (hg:G≠0) (ha :A≠0) (hmax : ∀ D,D ∣G*A→D ∣G*B→D ∣G) :
  IsCoprime A B:= by
 classical
 apply EuclideanDomain.isCoprime_of_dvd (fun h=>ha h.1)
 intro d hnonunit _ hda hdb
 obtain ⟨q,hq⟩:=hmax (G*d) (mul_dvd_mul_left G hda) (mul_dvd_mul_left G hdb)
 have heq :1=d*q:=wY hg (by
  calc
    G*1=G:=z8 _
    _=(G*d)*q:=hq
    _=G*(d*q) :=pU _ _ _)
 exact hnonunit (isUnit_iff_dvd_one.mpr ⟨q,heq⟩)
private theorem cEN {F ι:Type} [nq F] {q k H :ℕ} {x a b:ι→F}
  (R:kL.axT q x a b k H) (i:ι)
  (hU: (zk (fun j=>R.coefficients (0,j))).eval (C (x i))=0)
  (hV: (zk (fun j=>R.coefficients (1,j))).eval (C (x i))=0) :
  R.output.eval (C (x i))=0:= by
 simpa only [hU,hV,zero_mul,ze] using (R.nodes i).symm
end
end Aj
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Aj
noncomputable section
open Polynomial K1 gR
private def bp6 {F:Type*} [nq F] (x :F) (n:ℕ) :F:=x^n
private theorem eaq {F:Type*} [nq F] (x :F) :
 bp6 x 0=1 :=pow_zero x
private theorem eap {F:Type*} [nq F] (x :F) (n:ℕ) :
 bp6 x (n+1)=bp6 x n*x :=Dw x n
private theorem c1n (x :K) (n:ℕ) :bp6 x n=x^n:= by
 rw [CompPoly.Extension.Ext.pow_def]
 induction n with
 | zero=>rw [eaq,npowBinRec_zero]
 | succ n ih=>rw [eap,npowBinRec_succ,ih]
private theorem eEt {q k H :ℕ} {x a b:I→K}
    (R:kL.axT q x a b k H) (i:I) :
    (zk (fun j=>R.coefficients (0,j))).eval (C (x i)) *
        (C (a i)+Polynomial.X (R:=K)*C (b i)) +
      (zk (fun j=>R.coefficients (1,j))).eval (C (x i)) *
        (C (a i^q)+Polynomial.X (R:=K)^q*C (b i^q)) =
      R.output.eval (C (x i)) := by
  rw [← c1n (a i) q,← c1n (b i) q]
  unfold bp6
  exact R.nodes i
private theorem dEf {A:Type*} [pz A] [y5 A]
  {g U V W a b e :A} (hg:g≠0)
  (h: (g*U)*a+(g*V)*b=g*W) : (e*U)*a+(e*V)*b=e*W:= by
 have h₀:U*a+V*b=W :=
  wY hg (by simpa only [mul_add,pU] using h)
 simpa only [mul_add,pU] using oD (fun t=>e*t) h₀
private theorem bPb {u:e9} {q k H :ℕ}
  (R:kL.axT q node (u 0) (u 1) k H)
  (S:nX I) (G U V W:nC)
  (hG : ∀ i∉S,G.eval (C (node i))≠0)
  (hU:zk (fun j=>R.coefficients (0,j))=G*U)
  (hV:zk (fun j=>R.coefficients (1,j))=G*V)
  (hW:R.output=G*W) (e :K[X]) :
  ad9 q u S (C e*U) (C e*V) (C e*W) := by
 intro i hi
 have hn := @eEt q k H node (u 0) (u 1) R i
 simp only [hU,hV,hW,qy] at hn
 simpa only [qy ,eval_C] using
  (dEf (e :=e) (hG i hi) hn)
end
end Aj
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 850000
namespace Aj
noncomputable section
open Polynomial K1 gR
def Vf :nC →+* kB[X] :=wA GC
private theorem bIq (P:K[X]) : (jH P).natDegree=P.natDegree :=
 KI z7 P
private theorem go9 (n:ℕ) : (seed^n).natDegree=0:= by
 apply Zh
 exact natDegree_pow_le.trans (by simp [seed])
private theorem diz (P Q:K[X]) (n:ℕ) :
   (jH P+seed^n*jH Q).natDegree≤uO P Q:= by
 apply (IT _ _).trans
 apply max_le
 · rw [bIq]
   exact Bf _ _
 · apply natDegree_mul_le.trans
   rw [go9,ze,bIq]
   exact FU _ _
private theorem gBn (q:ℕ) (a :K[X]) (β:Fin 2→K[X]) :
  (NJ q a β).natDegree≤a.natDegree+uO (β 0) (β 1) := by
 unfold NJ
 apply natDegree_mul_le.trans
 rw [bIq]
 apply Gk
 exact (diz _ _ q).trans
  (max_le_max Vq Vq)
private theorem aQO:NJ p=(JO:K[X]→(Fin 2→K[X])→nC) := by
 unfold NJ JO
 rfl
private theorem dhe (a :K[X]) (β:Fin 2→K[X]) :
  (JO a β).natDegree≤a.natDegree+uO (β 0) (β 1) := by
 rw [← aQO]
 exact gBn p a β
private theorem dhf (b:K[X]) (α:Fin 2→K[X]) :
  (J9 b α).natDegree≤b.natDegree+uO (α 0) (α 1) := by
 unfold J9
 rw [natDegree_neg]
 apply natDegree_mul_le.trans
 rw [bIq]
 apply Gk
 simpa only [uW] using diz (α 0) (α 1) 1
private theorem bYj {L:Type*} [pz L] {A B P Q:L}
   (hcop:n5 A B) (hcross :A*Q=B*P) :
   ∃ E,P=E*A∧Q=E*B:= by
 obtain ⟨r,t,hbez⟩:=hcop
 refine ⟨r*P+t*Q,?_,?_⟩
 · calc
     P=(r*A+t*B)*P:= by rw [hbez,zR]
     _=r*(A*P)+t*(B*P) := by ring
     _=r*(A*P)+t*(A*Q) := by rw [hcross]
     _=(r*P+t*Q)*A:= by ring
 · calc
     Q=(r*A+t*B)*Q:= by rw [hbez,zR]
     _=r*(A*Q)+t*(B*Q) := by ring
     _=r*(B*P)+t*(B*Q) := by rw [hcross]
     _=(r*P+t*Q)*B:= by ring
private theorem c09 {A B P Q E :kB[X]} {H :ℕ}
   (ha :A≠0) (hb:B≠0) (hp:P=E*A) (hq:Q=E*B)
   (hmax :max A.natDegree B.natDegree=H)
   (hpd:P.natDegree≤H) (hqd:Q.natDegree≤H) :E.natDegree=0:= by
 by_cases he :E=0
 · simp [he]
 rw [hp,u8 he ha] at hpd
 rw [hq,u8 he hb] at hqd
 omega
private theorem co8 {P Q:nC} {s :kB} (j:ℕ)
  (h:Vf P=C s*Vf Q) :
  GC (P.coeff j)=s*GC (Q.coeff j) := by
 have hc:=oD (fun F:kB[X]=>F.coeff j) h
 change (P.map GC).coeff j=(C s*Q.map GC).coeff j at hc
 simpa only [coeff_C_mul,xu] using hc
private theorem cKB {ι:Type*} [Av ι]
    (A B:ι→K[X]) (hprim:M4.IsPrimitive A) (s :kB)
    (hB : ∀ i,GC (B i)=s*GC (A i)) :
    ∃ e :K[X],GC e=s := by
  obtain ⟨w,hw⟩:=(M4.a6R A).mp hprim
  refine ⟨∑ i,w i*B i,?_⟩
  calc
    GC (∑ i,w i*B i) =
        ∑ i,GC (w i)*(s*GC (A i)) := by
      simp only [t8 ,ox ,hB]
    _=s * ∑ i,GC (w i)*GC (A i) := by
      rw [FV]
      apply zg rfl
      intro i _
      ring
    _=s*GC (∑ i,w i*A i) := by simp only [t8 ,ox]
    _=s := by rw [hw,map_one,z8]
private theorem c5O {α β:Fin 2→K[X]}
   (ha :n5 (α 0) (α 1)) (hb:n5 (β 0) (β 1))
   (hd:α 0*β 1= α 1*β 0) :
   ∃ t:K,t≠0 ∧ ∀ i,β i=C t*α i:= by
 obtain ⟨c,h0,h1⟩:=bYj (A:= α 0) (B:= α 1) ha hd
 obtain ⟨r,s,h⟩:=hb
 have hunit :yo c:=isUnit_iff_dvd_one.mpr ⟨r*α 0+s*α 1,by
   calc
     1=r*β 0+s*β 1 :=h.symm
     _=c*(r*α 0+s*α 1) := by rw [h0,h1]; ring⟩
 have hc:c=C (c.coeff 0) :=eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hunit)
 refine ⟨c.coeff 0,?_,?_⟩
 · intro hz
   apply hunit.ne_zero
   rw [hc,hz,C_0]
 · intro i
   fin_cases i
   · change β 0=C (c.coeff 0)*α 0
     exact h0.trans (oD (fun z=>z*α 0) hc)
   · change β 1=C (c.coeff 0)*α 1
     exact h1.trans (oD (fun z=>z*α 1) hc)
private theorem fWr (q:ℕ) (a :K[X]) (α β:Fin 2→K[X]) (t:K)
  (heq : ∀ i,(β i).map lI=C t*(α i).map lI) :
  NJ q (a*C t) α=NJ q a β:= by
 simp only [NJ,heq,jH,vl,TH]
 ring
private theorem c8n (a :K[X]) (α β:Fin 2→K[X]) (t:K)
  (heq : ∀ i,(β i).map lI=C t*(α i).map lI) :
  JO (a*C t) α=JO a β:= by
 rw [← aQO]
 exact fWr p a α β t heq
end
end Aj
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace Aj
noncomputable section
open Polynomial K1
private def ay2 {F:Type*} [nq F] (A B:F[X]) (p:ℕ) :Fin 4→F[X] :=
 ![A,(lJ (R:=F))*A,B,(lJ (R:=F))^p*B]
private theorem ebJ {F:Type*} [nq F] (A:F[X]) (hA:A≠0) :
  Ar F ![A,(lJ (R:=F))*A] := by
 apply linearIndependent_fin2.mpr
 refine ⟨vj xm hA,?_⟩
 intro c hc
 change c•((lJ (R:=F))*A)=A at hc
 rw [G8 ,← pU] at hc
 have h:C c*(lJ (R:=F))=1 :=Zt hA (hc.trans (zR _).symm)
 have hc₀:=oD (fun Q:F[X]=>Q.coeff 0) h
 simp only [coeff_C_mul,coeff_X_zero,th,coeff_one_zero,zero_ne_one] at hc₀
private theorem deT {F:Type*} [nq F] {A W:F[X]}
  (hA:A≠0) (hW:W≠0) (hm:W∈t6 F (oY ![A,(lJ (R:=F))*A])) :
  A.natDegree≤W.natDegree∧W.natDegree≤A.natDegree+1 := by
 obtain ⟨c,hc⟩:=(Submodule.mem_span_range_iff_exists_fun F).mp hm
 have h:C (c 0)*A+C (c 1)*((lJ (R:=F))*A)=W:= by
  simpa only [TZ,Matrix.cons_val_zero,Matrix.cons_val_one,G8] using hc
 let P:=C (c 0)+C (c 1)*(lJ (R:=F))
 have hW' : W=P*A:= by rw [← h]; dsimp [P]; ring
 have hP:P≠0:= fun hz=>hW (by rw [hW',hz,zero_mul])
 have hPd:P.natDegree≤1 := by
  apply (IT _ _).trans
  exact max_le (by simp) (natDegree_mul_le.trans (by simp))
 have he :=oD Polynomial.natDegree hW'
 rw [u8 hP hA] at he
 omega
private theorem cY7 {F:Type*} [nq F] (A B:F[X]) (p:ℕ)
  (hA:A≠0) (j:Fin 4)
  (hj:ay2 A B p j∉t6 F (oY ![A,(lJ (R:=F))*A])) :
  3≤lz F (t6 F (oY (ay2 A B p))) := by
 let f :Fin 3→F[X] :=Fin.snoc ![A,(lJ (R:=F))*A] (ay2 A B p j)
 have hf :Ar F f :=linearIndependent_finSnoc.mpr ⟨ebJ A hA,hj⟩
 have hs :oY f⊆oY (ay2 A B p) := by
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨j,rfl⟩
 have :=Module.Finite.span_of_finite F (Set.finite_range (ay2 A B p))
 have hd:=zd (R:=F) (Submodule.span_mono hs)
 simpa only [ Xp hf,u9] using hd
private theorem gBs {F:Type*} [nq F] (A B:F[X]) (p:ℕ)
    (hA:A≠0) (hB:B≠0) (hp:1<p) :
    lz F (t6 F (oY (ay2 A B p)))=4 ∨
      lz F (t6 F (oY (ay2 A B p)))=3:= by
  have hle :lz F (t6 F (oY (ay2 A B p)))≤4 := by
    simpa only [Set.finrank,u9] using finrank_range_le_card (R:=F) (ay2 A B p)
  have hge :3≤lz F (t6 F (oY (ay2 A B p))) := by
    by_cases hm:B∈t6 F (oY ![A,(lJ (R:=F))*A])
    · apply cY7 A B p hA 3
      change (lJ (R:=F))^p*B∉t6 F (oY ![A,(lJ (R:=F))*A])
      intro hpow
      have hne : (lJ (R:=F))^p*B≠0:=vj (Et _ xm) hB
      have hBdeg:=(deT hA hB hm).1
      have hpowdeg:=(deT hA hne hpow).2
      rw [u8 (Et _ xm) hB,(monic_X (R:=F)).natDegree_pow,
        natDegree_X,Nat.mul_one] at hpowdeg
      omega
    · exact cY7 A B p hA 2 hm
  omega
private theorem dNK (U V:nC) (q:ℕ) :
  (fun j:Fin 4=>sZ (oq
    (if j=0 then U else if j=1 then seed*U else if j=2 then V else seed^q*V))) =
  ay2 (sZ (oq U)) (sZ (oq V)) q:= by
 funext j
 fin_cases j <;> simp [ay2,seed,G7,sZ,vl,
  Polynomial.map_pow,Polynomial.map_X]
private theorem fS6 (q:ℕ) (hq:1<q)
  (U V:nC) (hu:U≠0) (hv :V≠0) :
  ajp q U V=4∨ajp q U V=3:= by
 let A:=sZ (oq U)
 let B:=sZ (oq V)
 have hs (W:nC) (hn:W≠0) :sZ (oq W)≠0:= by
  intro h
  apply hn
  apply (oq (R:=K)).injective
  apply aC8
  simpa only [pC,sZ,RC] using h
 unfold ajp
 rw [dNK]
 exact gBs A B q (hs U hu) (hs V hv) hq
theorem fS5 (U V:nC) (hu:U≠0) (hv :V≠0) :
  Xb U V=4∨Xb U V=3 :=
 fS6 p (by decide) U V hu hv
end
end Aj
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace Aj
noncomputable section
open Polynomial K1
def c1 :Prop :=
  ∀ U V:nC,U≠0→V≠0→Xb U V=3 →
    Nonempty (biW U V)
def c2 :Prop :=
  ∀ (U V:nC) (H :ℕ),U≠0→V≠0 →
    n5 (sZ U) (sZ V) →
    max U.natDegree V.natDegree=H→H<p - 1 →
    ∀ S:biW U V,
      S.a.natDegree+uO (S.β 0) (S.β 1)≤H ∧
      S.b.natDegree+uO (S.α 0) (S.α 1)≤H
end
end Aj
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace czL
open Polynomial K1
noncomputable section
private def shape {R:Type*} [qx R] (n:ℕ) (u v :R) :R[X] :=
 C u+Polynomial.X (R:=R)^n*C v
private theorem cpl {R:Type*} [qx R] {n:ℕ} (hn:n≠0) (u v :R) :
   (shape n u v).coeff 0=u∧(shape n u v).coeff n=v := by
 constructor
 · simp [shape,p9 (lJ (R:=R)^n) (C v),Ne.symm hn]
 · simp [shape,p9 (lJ (R:=R)^n) (C v),coeff_C_of_ne_zero hn]
private theorem ccF {F:Type*} [nq F] {n:ℕ} (hn:n≠0)
  {u v :F[X]} (hcop:n5 u v) : (shape n u v).IsPrimitive := by
 intro d hd
 obtain ⟨h0,hn'⟩:=cpl hn u v
 have h:=(C_dvd_iff_dvd_coeff _ _).mp hd
 exact hcop.isUnit_of_dvd' (h0 ▸ h 0) (hn' ▸ h n)
private theorem coB {F:Type*} [nq F] {a :F[X]} {P:F[X][X]}
  (ha :a≠0) (hP:P.IsPrimitive) :oZ (C a) P:= by
 intro d hda hdP
 have hdeg:d.natDegree=0 :=
  Zh ((Ef hda (C_ne_zero.mpr ha)).trans_eq (natDegree_C a))
 rw [eq_C_of_natDegree_eq_zero hdeg] at hdP ⊢
 exact (hP _ hdP).map C
private def Ss {F:Type*} [nq F] (P:F[X][X]) :ℕ :=
 (oq P).natDegree
private theorem biO {F:Type*} [nq F] (a :F[X]) :Ss (C a)=a.natDegree := by
 rw [Ss,OJ,KI z7]
private theorem byQ {F:Type*} [nq F] {P Q:F[X][X]}
  (hP:P≠0) (hQ:Q≠0) :Ss (P*Q)=Ss P+Ss Q:= by
 unfold Ss
 rw [ox]
 exact u8 (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hP)
  (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hQ)
private theorem dmh {F:Type*} [nq F] (P:F[X][X]) (n:ℕ) :
  Ss (P^n)=n*Ss P:= by
 rw [Ss,wB,natDegree_pow,Ss]
private theorem dmi {F:Type*} [nq F] {n:ℕ} (hn:n≠0) (u v :F[X]) :
   Ss (shape n u v)=max u.natDegree v.natDegree := by
 have hc (i:ℕ) :
     (oq (shape n u v)).coeff i=shape n (u.coeff i) (v.coeff i) := by
   rw [shape,qm,ox ,wB,OJ,OJ,Bivariate.swap_Y,
     ← C_pow,coeff_add,coeff_C_mul,xu,xu,shape]
 unfold Ss
 apply le_antisymm
 · apply natDegree_le_iff_coeff_eq_zero.mpr
   intro i hi
   rw [hc,PA ((Bf _ _).trans_lt hi),
     PA ((FU _ _).trans_lt hi)]
   simp [shape]
 · apply max_le
   · by_cases hu:u=0
     · simp [hu]
     apply le_natDegree_of_ne_zero
     intro hz
     have h:=oD (fun W:F[X]=>W.coeff 0) ((hc u.natDegree).symm.trans hz)
     rw [(cpl hn _ _).1,vw] at h
     exact hu (leadingCoeff_eq_zero.mp h)
   · by_cases hv :v=0
     · simp [hv]
     apply le_natDegree_of_ne_zero
     intro hz
     have h:=oD (fun W:F[X]=>W.coeff n) ((hc v.natDegree).symm.trans hz)
     rw [(cpl hn _ _).2,vw] at h
     exact hv (leadingCoeff_eq_zero.mp h)
private theorem cIB {F:Type*} [nq F] {U V P Q:F[X][X]}
  (hU:U≠0) (hV:V≠0) (hcop:oZ P Q) (hcross :U*Q=V*P) :
  Ss P≤Ss U∧Ss Q≤Ss V:= by
 have hp:P∣U:=hcop.dvd_of_dvd_mul_right (by rw [hcross]; exact Fa _ _)
 have hq:Q∣V:=hcop.symm.dvd_of_dvd_mul_right (by rw [← hcross]; exact Fa _ _)
 exact ⟨Ef (zc oq hp)
    (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hU),
  Ef (zc oq hq)
    (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hV)⟩
private theorem dsI {F:Type*} [nq F] (q:ℕ) [EK F q] (hq:q≠0)
    {u v r s :F[X]} (huv :n5 u v) (hrs :n5 r s) :
    oZ (shape 1 u v) (shape q r s) ∨
      ∃ t:F[X],yo t∧shape q r s=C t*(shape 1 u v)^q:= by
  by_cases hv :v=0
  · left
    subst v
    have hu:yo u:=huv.isUnit_of_dvd (dvd_zero _)
    simpa [shape] using (hu.map (C:F[X] →+* F[X][X])).isRelPrime_left
  have hAffine :shape 1 u v=C v*lJ (R:=F[X])+C u:= by
    rw [shape,uW,Dv,p9 (lJ (R:=F[X]))]
  have hirr :GB (shape 1 u v) := by
    rw [hAffine]
    exact irreducible_C_mul_X_add_C hv huv.symm.isRelPrime
  rcases hirr.dvd_or_isRelPrime (n:=shape q r s) with hdiv | hcop
  · right
    have hpow: (shape 1 u v)^q=shape q (u^q) (v^q) := by
      simp only [shape,uW,add_pow_expChar _ _ q,mul_pow,← C_pow]
    have hdiff :C (v^q)*shape q r s - C s*(shape 1 u v)^q =
        C (v^q*r - s*u^q) := by
      rw [hpow]
      simp only [shape,ox ,map_sub]
      ring
    have hc:shape 1 u v∣C (v^q*r - s*u^q) := by
      rw [← hdiff]
      exact dvd_sub (hdiv.mul_left _) ((dvd_pow_self _ hq).mul_left _)
    have hcross :v^q*r=s*u^q:= by
      apply sub_eq_zero.mp
      by_contra hne
      have hd:=Ef hc (C_ne_zero.mpr hne)
      rw [hAffine,natDegree_linear hv,natDegree_C] at hd
      omega
    have hp:n5 (u^q) (v^q) :=huv.pow
    obtain ⟨e,f,hbez⟩:=hp
    let t:=e*r+f*s
    have hr :r=t*u^q:= by
      calc
        r=(e*u^q+f*v^q)*r := by rw [hbez,zR]
        _=t*u^q:= by
          dsimp [t]
          linear_combination f*hcross
    have hs :s=t*v^q:= by
      calc
        s=(e*u^q+f*v^q)*s := by rw [hbez,zR]
        _=t*v^q:= by
          dsimp [t]
          linear_combination-e*hcross
    have ht:shape q r s=C t*(shape 1 u v)^q:= by
      rw [hpow,hr,hs]
      simp only [shape,ox]
      ring
    exact ⟨t,ccF hq hrs t (ht ▸ FQ _ _),ht⟩
  · exact Or.inl hcop
private theorem aVi {F:Type*} [nq F] (q:ℕ) [EK F q] (hq:1<q)
    {U₀ V:F[X][X]} {H :ℕ} (hU₀:U₀≠0) (hV:V≠0)
    (hU₀H :Ss U₀≤H) (hVH :Ss V≤H) (hsmall:H<q - 1)
    {a b u v r s :F[X]} (ha :a≠0) (hb:b≠0)
    (hab:n5 a b) (huv :n5 u v) (hrs :n5 r s)
    (hdir :U₀ * -(C b*shape 1 u v)=V*(C a*shape q r s)) :
    a.natDegree+max r.natDegree s.natDegree≤H ∧
      b.natDegree+max u.natDegree v.natDegree≤H := by
  have hq0:q≠0:= by omega
  let U := -U₀
  have hU:U≠0:=neg_ne_zero.mpr hU₀
  have hUH :Ss U≤H := by
    simpa only [U,Ss,map_neg,natDegree_neg] using hU₀H
  have hcross :U*(C b*shape 1 u v)=V*(C a*shape q r s) := by
    exact (neg_mul_comm U₀ (C b*shape 1 u v)).trans hdir
  let A:=shape 1 u v
  let B:=shape q r s
  have hA:A.IsPrimitive :=ccF Pr huv
  have hB:B.IsPrimitive :=ccF hq0 hrs
  have hab' : oZ (C a) (C b) :=(hab.map C).isRelPrime
  have hAd:Ss A=max u.natDegree v.natDegree :=dmi Pr _ _
  have hBd:Ss B=max r.natDegree s.natDegree :=dmi hq0 _ _
  rcases dsI q hq0 huv hrs with hcop | ⟨t,ht,hpow⟩
  · have hcop' : oZ (C a*B) (C b*A) :=
      (hab'.mul_right (coB ha hA)).mul_left
        ((coB hb hB).symm.mul_right hcop.symm)
    obtain ⟨hP,hQ⟩:=cIB hU hV hcop' hcross
    rw [byQ (C_ne_zero.mpr ha) hB.ne_zero,biO,hBd] at hP
    rw [byQ (C_ne_zero.mpr hb) hA.ne_zero,biO,hAd] at hQ
    exact ⟨hP.trans hUH,hQ.trans hVH⟩
  · change B=C t*A^q at hpow
    let D:=C a*C t*A^(q - 1)
    have hD:oZ D (C b) :=
      (hab'.mul_left ((ht.map C).isRelPrime_left)).mul_left
        (coB hb hA).symm.pow_left
    have hfactor :C a*B=D *A:= by
      have hqpow:A^q=A^(q - 1)*A:= by
        rw [← Dw ,Nat.sub_add_cancel (by omega :1≤q)]
      simp only [D,hpow,hqpow,pU]
    have hnew :U*C b=V*D:= by
      apply Zt hA.ne_zero
      calc
        (U*C b)*A=U*(C b*A) :=pU _ _ _
        _=V*(C a*B) :=hcross
        _=(V*D)*A:= by rw [hfactor,pU V D A]
    obtain ⟨hDle,hble⟩:=cIB hU hV hD hnew
    have ht0:t.natDegree=0:=natDegree_eq_zero_of_isUnit ht
    have hDa :Ss D =a.natDegree+(q - 1)*Ss A:= by
      dsimp [D]
      rw [byQ (vj (C_ne_zero.mpr ha) (C_ne_zero.mpr ht.ne_zero))
            (Et _ hA.ne_zero),
        byQ (C_ne_zero.mpr ha) (C_ne_zero.mpr ht.ne_zero),biO,biO,
        dmh,ht0,uJ]
    have hzero :Ss A=0:= by
      by_contra hn
      have hle :=(Cy (q - 1) (Nat.one_le_iff_ne_zero.mpr hn))
      rw [Nat.mul_one] at hle
      rw [hDa] at hDle
      omega
    have hBzero :Ss B=0:= by
      rw [hpow,byQ (C_ne_zero.mpr ht.ne_zero) (Et _ hA.ne_zero),
        biO,dmh,hzero,ht0,Nat.mul_zero,uJ]
    rw [hDa,hzero,Nat.mul_zero,uJ] at hDle
    rw [biO] at hble
    rw [← hBd,← hAd,hBzero,hzero,uJ,uJ]
    exact ⟨hDle.trans hUH,hble.trans hVH⟩
private theorem gxS (q:ℕ) (a :K[X]) (β:Fin 2→K[X]) :
  oq (Aj.NJ q a β)=C a*shape q ((β 0).map lI) ((β 1).map lI) := by
 simp only [Aj.NJ,shape,jH,seed,qm,ox ,wB,LP ,
  G7]
private theorem gBo:Aj.NJ p=JO:= by
 unfold Aj.NJ JO
 rfl
private theorem gxT (b:K[X]) (α:Fin 2→K[X]) :
  oq (J9 b α) = -(C b*shape 1 (α 0) (α 1)) := by
 simp only [J9,shape,jH,seed,qm,ox ,map_neg,LP ,
  G7,uW]
private theorem eEs (q:ℕ) [EK K q] (hq:1<q)
  (U V:nC) (H :ℕ) (hU:U≠0) (hV:V≠0)
  (hmax :max U.natDegree V.natDegree=H) (hsmall:H<q - 1)
  (a b:K[X]) (α β:Fin 2→K[X]) (ha :a≠0) (hb:b≠0)
  (hab:n5 a b) (hα:n5 (α 0) (α 1)) (hβ:n5 (β 0) (β 1))
  (hdir :Z4 U V (Aj.NJ q a β) (J9 b α)) :
  a.natDegree+uO (β 0) (β 1)≤H ∧
    b.natDegree+uO (α 0) (α 1)≤H := by
 have hUH :U.natDegree≤H :=hmax ▸ Bf _ _
 have hVH :V.natDegree≤H :=hmax ▸ FU _ _
 have hcross :oq U * -(C b*shape 1 (α 0) (α 1)) =
    oq V*(C a*shape q ((β 0).map lI) ((β 1).map lI)) := by
  have h:=oD (oq (R:=K)) hdir
  change oq (U*J9 b α)=oq (V*Aj.NJ q a β) at h
  rwa [ox ,ox ,gxT,gxS] at h
 have hxU:Ss (oq U)=U.natDegree := by
  rw [Ss,Bivariate.swap_swap_apply]
 have hxV:Ss (oq V)=V.natDegree := by
  rw [Ss,Bivariate.swap_swap_apply]
 have hβ' : n5 ((β 0).map lI) ((β 1).map lI) :=
  hβ.map (wA lI)
 have h:=aVi (F:=K) q hq
  (U₀:=oq U) (V:=oq V) (H :=H)
  (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hU)
  (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hV)
  (hxU ▸ hUH) (hxV ▸ hVH) hsmall
  (a :=a) (b:=b) (u:= α 0) (v := α 1)
  (r :=(β 0).map lI) (s :=(β 1).map lI)
  ha hb hab hα hβ' hcross
 simpa only [uO,KI twist.injective] using h
theorem proof :Aj.c2 := by
 intro U V H hU hV _ hmax hsmall S
 apply eEs p (by decide) U V H hU hV hmax hsmall S.a S.b S.α S.β
  S.a_ne S.b_ne S.scalar_coprime S.α_primitive S.β_primitive
 rw [gBo]
 exact S.direction
end
end czL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace czK
noncomputable section
open Polynomial K1 Aj gR
open scoped BigOperators
private def a3M:nC →+* kB[X] :=
 Vf.comp (oq (R:=K)).toRingEquiv.toRingHom
private theorem d3t:p7 a3M :=
 aC8.comp (oq (R:=K)).injective
private theorem d3u (f :K[X]) :
  a3M (jH f)=C (GC f) := by
 change (oq (f.map C)).map GC= _
 rw [LP ,TH]
private def columns (q:ℕ) (U V:nC) (i:Fin 4) :nC :=
 if i=0 then U else if i=1 then seed*U else if i=2 then V else seed^q*V
private theorem eM4 {U V:nC} (hr :Xb U V=3) :
    ∃ f :Fin 4→K[X],f≠0 ∧ ∑ i,jH (f i)*columns p U V i=0:= by
  classical
  have hdep : ¬ Ar kB (fun i=>a3M (columns p U V i)) := by
    intro h
    have hdim:Xb U V=4 := by
      change lz kB
        (t6 kB (oY fun i=>a3M (columns p U V i)))=4
      simpa only [u9] using Xp h
    omega
  obtain ⟨c,hc,j,hj⟩:=Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples_of_finite
    (Ea K[X]) c
  choose f hf using hd
  have hcoeff (i:Fin 4) :GC (f i)=GC (d:K[X])*c i:= by
    simpa only [QL,GC] using hf i
  have hdn:GC (d:K[X])≠0:= by
    intro hz
    exact zyw d.property
      (aAg (hz.trans (pC GC).symm))
  refine ⟨f,?_,?_⟩
  · intro hzero
    have hj' := hcoeff j
    rw [hzero,Pi.zero_apply,pC] at hj'
    exact hj ((mul_eq_zero.mp hj'.symm).resolve_left hdn)
  · have hscaled :
        ∑ i,a3M (jH (f i))*a3M (columns p U V i) =
          C (GC (d:K[X])) * ∑ i,c i•a3M (columns p U V i) := by
      rw [FV]
      apply zg rfl
      intro i _
      rw [d3u,hcoeff,Polynomial.C_mul,G8 ,pU]
    apply d3t
    rw [pC,t8]
    simp only [ox ,hscaled,hc,th]
private def wK (q:ℕ) (u v :K[X]) :nC :=
 jH u+seed^q*jH v
private theorem cBh (q:ℕ) :wK q 0 0=0:= by
 simp only [wK,jH,RC,th,uJ]
private theorem dtd (q:ℕ) (d u v :K[X]) :
  wK q (d*u) (d*v)=jH d*wK q u v := by
 simp only [wK,jH,vl]
 ring
private theorem cBg {q:ℕ} (hq:0<q) {u v :K[X]}
   (h:wK q u v=0) :u=0∧v=0:= by
 have hswap:C u+(lJ (R:=K[X]))^q*C v=0:= by
   simpa only [wK,seed,jH,qm,ox ,wB,pC,
     G7,LP] using oD (oq (R:=K)) h
 have hu:=oD (fun W:nC=>W.coeff 0) hswap
 have hv :=oD (fun W:nC=>W.coeff q) hswap
 have hshift: ((lJ (R:=K[X]))^q*C v).coeff q=v := by
   simpa only [Nat.zero_add,coeff_C_zero] using (coeff_X_pow_mul (C v :nC) q 0)
 constructor
 · simpa only [coeff_add,coeff_C_zero,coeff_X_pow_mul',Nat.not_le_of_lt hq,
     C9,uJ,vw] using hu
 · simpa only [coeff_add,hshift,coeff_C,hq.ne',C9,ze,vw] using hv
private theorem ekJ {q:ℕ} {U V:nC} {f :Fin 4→K[X]}
  (h : ∑ i,jH (f i)*columns q U V i=0) :
  wK 1 (f 0) (f 1)*U + wK q (f 2) (f 3)*V=0:= by
 have h0:columns q U V 0=U:=rfl
 have h1 :columns q U V 1=seed*U:=rfl
 have h2 :columns q U V 2=V:=rfl
 have h3:columns q U V 3=seed^q*V:=rfl
 rw [zmL,h0,h1,h2,h3] at h
 simpa only [wK,uW,add_mul,pU,JK,add_assoc] using h
private theorem eFa {q:ℕ} (hq:0<q) {U V:nC} (hu:U≠0) (hv :V≠0)
   {f :Fin 4→K[X]} (hf :f≠0)
   (h:wK 1 (f 0) (f 1)*U + wK q (f 2) (f 3)*V=0) :
   (![f 0,f 1] :Fin 2→K[X])≠0∧(![f 2,f 3] :Fin 2→K[X])≠0:= by
 constructor
 · intro hz
   have h0:f 0=0:=zf hz 0
   have h1 :f 1=0:=zf hz 1
   rw [h0,h1,cBh,zero_mul,ze] at h
   have hz' : wK q (f 2) (f 3)=0:=(mul_eq_zero.mp h).resolve_right hv
   obtain ⟨h2,h3⟩:=cBg hq hz'
   apply hf
   funext i
   fin_cases i <;> assumption
 · intro hz
   have h2 :f 2=0:=zf hz 0
   have h3:f 3=0:=zf hz 1
   rw [h2,h3,cBh,zero_mul,uJ] at h
   have hz' : wK 1 (f 0) (f 1)=0:=(mul_eq_zero.mp h).resolve_right hu
   obtain ⟨h0,h1⟩:=cBg Nat.zero_lt_one hz'
   apply hf
   funext i
   fin_cases i <;> assumption
private theorem b9U {u v :K[X]} (h: (![u,v] :Fin 2→K[X])≠0) :
  ∃ (d:K[X]) (w:Fin 2→K[X]),d≠0 ∧
    u=d*w 0∧v=d*w 1∧n5 (w 0) (w 1) := by
 obtain ⟨d,w,hd,hw,hprim⟩:=M4.b2i ![u,v] h
 obtain ⟨r,hr⟩:=(M4.a6R w).mp hprim
 exact ⟨d,w,hd,hw 0,hw 1,r 0,r 1,by simpa only [TZ] using hr⟩
private def din:K ≃+* K :=
 RingEquiv.ofBijective lI ⟨twist.injective,Finite.surjective_of_injective twist.injective⟩
private def bPy :K →+* K:=din.symm.toRingHom
private theorem ezj (f :K[X]) : (f.map bPy).map lI=f := by
 rw [EP]
 have h:twist.comp bPy=Mk K:= by
  apply F9
  intro x
  exact din.apply_symm_apply x
 rw [h,JQ]
private theorem ev7 {f :K[X]} (hf :f≠0) :jH f≠0:= by
 intro h
 exact hf (HZ MO z7
  (h.trans (RC _).symm))
private theorem dRC {d a b:K[X]} (hd:d≠0) {U V F G:nC}
  (h: (jH (d*b)*F)*U + (jH (d*a)*G)*V=0) :
  U * -(jH b*F)=V*(jH a*G) := by
 have hscaled:jH d*(U*(jH b*F)+V*(jH a*G))=0:= by
  rw [← h]
  simp only [jH,vl]
  ring
 have hz :=(mul_eq_zero.mp hscaled).resolve_left (ev7 hd)
 exact (_root_.mul_neg U (jH b*F)).trans (neg_eq_iff_add_eq_zero.mpr hz)
private theorem eOh {q:ℕ} (hq:0<q) {U V:nC}
   (hU:U≠0) (hV:V≠0) {f :Fin 4→K[X]} (hf :f≠0)
   (hsum : ∑ i,jH (f i)*columns q U V i=0) :
   ∃ (α β:Fin 2→K[X]) (a b:K[X]),a≠0∧b≠0∧n5 a b ∧
     n5 (α 0) (α 1)∧n5 (β 0) (β 1) ∧
     Z4 U V (NJ q a β) (J9 b α) := by
 have hrel :=ekJ (q:=q) (U:=U) (V:=V) (f :=f) hsum
 obtain ⟨hleft,hright⟩:=eFa hq hU hV hf hrel
 obtain ⟨b₀,α,hb₀,h0,h1,hα⟩:=b9U hleft
 obtain ⟨a₀,βσ,ha₀,h2,h3,hβσ⟩:=b9U hright
 have hab₀: (![a₀,b₀] :Fin 2→K[X])≠0:= fun h=>ha₀ (zf h 0)
 obtain ⟨d,ab,hd,ha,hb,hab⟩:=b9U hab₀
 let β:Fin 2→K[X] := fun i=>(βσ i).map bPy
 have ha' : ab 0≠0:= fun hz=>ha₀ (by rw [ha,hz,th])
 have hb' : ab 1≠0:= fun hz=>hb₀ (by rw [hb,hz,th])
 refine ⟨α,β,ab 0,ab 1,ha',hb',hab,hα,
   hβσ.map (wA bPy),?_⟩
 rw [h0,h1,h2,h3,ha,hb] at hrel
 simp only [dtd] at hrel
 have hcross :=dRC hd hrel
 simpa only [Z4,NJ,J9,β,ezj,wK,uW]
   using hcross
private theorem aQO:NJ p=(JO:K[X]→(Fin 2→K[X])→nC) := by
 unfold NJ JO
 rfl
theorem proof :Aj.c1 := by
 intro U V hU hV hr
 have hp:0<p:= by decide
 obtain ⟨f,hf,hsum⟩:=eM4 hr
 obtain ⟨α,β,a,b,ha,hb,hab,hα,hβ,hdir⟩ :=
  eOh (q:=p) (U:=U) (V:=V) (f :=f) hp hU hV hf hsum
 refine ⟨⟨α,β,a,b,ha,hb,hab,hα,hβ,?_⟩⟩
 simpa only [aQO] using hdir
end
end czK
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace aBc
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open scoped BigOperators
abbrev K:=K1.K
abbrev I:=K1.I
abbrev node :=qz
abbrev twist:=lI
def qW (P Q:K[X]) (z :K) :K[X] :=P+C z*Q
def fold (u:v8) (z :K) (i:I) :K:=u 0 i+z*u 1 i
theorem bfs (P:K[X]) (i:I) :
  (P.map twist).eval (node i)=twist (P.eval (node i)) :=
 kL.aC4 twist P (node i) (Native.ahU i)
theorem c3U (P Q:K[X]) (z :K) :
   (qW P Q z).natDegree≤ max P.natDegree Q.natDegree :=
 (IT _ _).trans (max_le_max qG (Yi z Q))
theorem degree_sub_lt {P Q:K[X]} {n:ℕ} (hP:P.degree<n) (hQ:Q.degree<n) :
   (P-Q).degree<n :=
 (Polynomial.degree_sub_le _ _).trans_lt (max_lt hP hQ)
theorem ajX {P Q:K[X]} {n:ℕ} (hP:P.degree<n) (hQ:Q.degree<n) (z :K) :
   (qW P Q z).degree<n:= by
 apply (Polynomial.degree_add_le _ _).trans_lt (max_lt hP ?_)
 by_cases hz :z=0
 · simp [hz]
 · simpa only [degree_C_mul hz] using hQ
theorem bpo (S:nX I) (P Q:K[X])
  (hP:P.degree<S.card) (hQ:Q.degree<S.card)
  (h : ∀ i∈S,P.eval (node i)= Q.eval (node i)) :P= Q :=
 Polynomial.eq_of_degrees_lt_of_eval_index_eq S
  (fun _ _ _ _ hxy=>node.injective hxy) hP hQ h
def Bg (P:K1.nC) (j:ℕ) :K[X] :=(oq P).coeff j
def ahu (u:v8) (a b:K[X]) (A:Fin 2→K[X])
    (i:I) (l j:Fin 2) :K :=
  a.eval (node i)*twist ((A l).eval (node i))*u j i -
    b.eval (node i)*(A j).eval (node i)*twist (u l i)
def bi7 (u:v8) (a b:K[X]) (A:Fin 2→K[X])
    (P:K1.nC) (i:I) :Prop :=
  (Bg P 0).eval (node i)=ahu u a b A i 0 0 ∧
  (Bg P 1).eval (node i)=ahu u a b A i 0 1 ∧
  (Bg P K1.p).eval (node i)=ahu u a b A i 1 0 ∧
  (Bg P (K1.p+1)).eval (node i)=ahu u a b A i 1 1
structure N6 (u:v8) where
 a :K[X]
 b:K[X]
 A:Fin 2→K[X]
 Q:K→K→K[X]
 a_ne :a≠0
 norms_ne :t5 a≠t5 b
 primitive :n5 (A 0) (A 1)
 a_bound:a.natDegree+K1.uO (A 0) (A 1)≤32685
 b_bound:b.natDegree+K1.uO (A 0) (A 1)≤32685
 Q_degree : ∀ r s,(Q r s).degree < 163757
 nodes : ∀ r s i,
   (Q r s).eval (node i) =
     a.eval (node i)*twist ((qW (A 0) (A 1) r).eval (node i))*fold u s i -
     b.eval (node i)*(qW (A 0) (A 1) s).eval (node i)*twist (fold u r i)
abbrev N6.amp {u:v8} (D:N6 u) :=qW (D.A 0) (D.A 1)
private theorem epr :t9 K K1.p 6=Mk K:= by
 apply F9
 intro x
 change x^K1.p^6=x
 have hc:v9 K=K1.p^6:=Te
 rw [← hc]
 exact Kv x
theorem cpG (P:K[X]) :t5 (P.map twist)=t5 P:= by
  unfold t5
  have h (j:Fin 6) :
      (P.map twist).map (t9 K K1.p j.val) =
        P.map (t9 K K1.p (j.val+1)) := by
    rw [EP ,SC,UY]
    rfl
  simp_rw [h]
  rw [Fin.prod_univ_castSucc (n:=5),
    Fin.prod_univ_succ (f := fun j:Fin 6=>P.map (t9 K K1.p j.val))]
  simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_last,Fin.val_zero,Nat.reduceAdd,
    epr,iterateFrobenius_zero,JQ]
  exact p9 _ _
theorem aQk (P Q:K[X]) :t5 (P*Q)=t5 P*t5 Q:= by
 simp only [t5 ,vl,Re]
theorem aQl {P:K[X]} (h:P≠0) :t5 P≠0 :=
 Finset.prod_ne_zero_iff.mpr fun j _ =>
  (zeI (t9 K K1.p j.val).injective).mpr h
end
end aBc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace aBc
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
private theorem bAV (f χ:K→K) (h:p7 χ)
  {r s :K} (hrs :r≠s) (hf : ∀ z,f z=f 0+χ z*(f 1 - f 0))
  (hr :f r=0) (hs :f s=0) (z :K) :f z=0:= by
 have h₁:=hf r
 have h₂:=hf s
 have hb: (χ r-χ s)*(f 1 - f 0)=0:= by linear_combination h₂ - h₁+hr - hs
 have hd:=(mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr (h.ne hrs))
 have hz :f z=f 0:= by simpa [hd] using hf z
 have hrr :f r=f 0:= by simpa [hd] using h₁
 exact hz.trans (hrr.symm.trans hr)
private def N6.afu {u} (D:N6 u) (r s :K) (P Q:K[X]) :K[X] :=
 D.a*(D.amp r).map twist*Q - D.b*D.amp s*P.map twist
private def residual (u:v8) (P Q:K[X]) :K1.e9 :=
 fun j i=>u j i-(if j=0 then P else Q).eval (node i)
private theorem b3K (u:v8) (P Q:K[X]) (z :K) (i:I) :
  fold (residual u P Q) z i=fold u z i-(qW P Q z).eval (node i) := by
 simp [fold,qW,residual]
 ring
end
end aBc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace aBc
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
private theorem dMy (P:K1.nC) (j m:ℕ) :
   (Bg P j).coeff m=(P.coeff m).coeff j:= by
 induction P using WY with
 | add A B hA hB=>simp only [Bg,map_add,coeff_add] at hA hB ⊢; rw [hA,hB]
 | monomial n f =>
   simp only [Bg,Bivariate.swap_monomial,coeff_mul_C,xu,
     C_mul_X_pow_eq_monomial,coeff_monomial]
   split_ifs <;> simp
private theorem d2P (P:K1.nC) (j:ℕ) (x :K) :
   (Bg P j).eval x=(P.eval (C x)).coeff j:= by
 induction P using WY with
 | add A B hA hB =>
   simp only [Bg,qm,coeff_add,eval_add] at hA hB ⊢
   rw [hA,hB]
 | monomial n f =>
   simp only [Bg,Bivariate.swap_monomial,eval_monomial,← C_pow,coeff_mul_C,
     xu,qy ,eval_C,eval_pow,eval_X]
private theorem coU (P:K1.nC) (j h:ℕ) (hp:P.degree<h) :
  (Bg P j).degree<h:= by
 apply (degree_lt_iff_coeff_zero _ _).mpr
 intro m hm
 rw [dMy,coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast hm)),vw]
private theorem ari (P:K[X]) (x :K) :
  (K1.jH P).eval (C x)=C (P.eval x) :=
 ZK MO x
theorem d2k (a :K1.K[X]) (A:Fin 2→K1.K[X]) (i:K1.I) (n:ℕ) :
    (K1.jH a*(K1.jH ((A 0).map lI) +
      K1.seed^n*K1.jH ((A 1).map lI))).eval (C (qz i)) =
      C (a.eval (qz i))*(C (lI ((A 0).eval (qz i))) +
        lJ ^n*C (lI ((A 1).eval (qz i)))) := by
  rw [qy ,ari a,eval_add,ari ((A 0).map lI),qy ,
    ari ((A 1).map lI),eval_pow,K1.seed,eval_C,bfs,bfs]
private theorem d3b (b:K[X]) (A:Fin 2→K[X]) (i:I) :
   (K1.J9 b A).eval (C (node i)) =
     -(C (b.eval (node i))*(C ((A 0).eval (node i))+(lJ (R:=K))*C ((A 1).eval (node i)))) := by
 unfold K1.J9
 rw [eval_neg,qy ,ari b,eval_add,ari (A 0),qy ,
   ari (A 1),K1.seed,eval_C]
theorem dM7
    (u:v8) (a b:K1.K[X]) (A:Fin 2→K1.K[X])
    (i:K1.I) (n:ℕ) (hn:1<n) (hσ : ∀ z :K1.K,z^n=lI z) (P U:K1.nC)
    (hU:U.eval (C (qz i)) =
      C (a.eval (qz i))*(C (lI ((A 0).eval (qz i))) +
        lJ ^n*C (lI ((A 1).eval (qz i)))))
    (h:P.eval (C (qz i)) =
      U.eval (C (qz i)) *
          (C (u 0 i)+Polynomial.X (R:=K1.K)*C (u 1 i)) +
      (K1.J9 b A).eval (C (qz i)) *
        (C (u 0 i^n)+Polynomial.X (R:=K1.K)^n*C (u 1 i^n))) :
    (Bg P 0).eval (node i)=ahu u a b A i 0 0 ∧
    (Bg P 1).eval (node i)=ahu u a b A i 0 1 ∧
    (Bg P n).eval (node i)=ahu u a b A i 1 0 ∧
    (Bg P (n+1)).eval (node i)=ahu u a b A i 1 1 := by
  let q:=ahu u a b A i
  have hexpand:P.eval (C (node i)) =
      C (q 0 0)+C (q 0 1)*lJ+C (q 1 0)*lJ ^n +
        C (q 1 1)*lJ ^(n+1) := by
    rw [h,hU,hσ (u 0 i),hσ (u 1 i),d3b,Dw (lJ (R:=K)) n]
    simp only [q,ahu,map_sub,ox]
    generalize (lJ (R:=K))^n=xp
    ring
  have h0:n≠0:= by omega
  have h1 :n≠1 := by omega
  have hs0:n+1≠0:= by omega
  have hs1 :n+1≠1 := by omega
  have hs :n+1≠n:= by omega
  simp only [d2P,hexpand,coeff_add,coeff_C,coeff_C_mul_X,coeff_C_mul_X_pow,
    h0,h0.symm,h1,h1.symm,hs0,hs0.symm,hs1,hs1.symm,hs,hs.symm,ite_true,C9,and_self,
    Nat.zero_ne_one,Nat.one_ne_zero,ze,uJ,q]
end
end aBc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace bRI
noncomputable section
open cu gT pI Polynomial
open scoped BigOperators
private def aS7 {R:Type*} [qx R] :
   u5 (u5 R) →+* mD (Fin 2) R :=
 (NI R 1).symm.toRingHom.comp
   (wA (Kp R (Fin 1)).symm.toRingHom)
private theorem cF6 {R:Type*} [qx R]
  (P:u5 (u5 R)) (d:Fin 2 →₀ ℕ) :
  (aS7 P).coeff d=(P.coeff (d 0)).coeff (d 1) := by
 let Q:=(P.map (Kp R (Fin 1)).symm.toRingHom)
 change ((NI R 1).symm Q).coeff d= _
 rw [← Finsupp.cons_tail d,← MvPolynomial.finSuccEquiv_coeff_coeff,
  AlgEquiv.apply_symm_apply]
 simp only [Q,xu]
 change ((Kp R (Fin 1)).symm (P.coeff (d 0))).coeff d.tail= _
 rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
 rfl
private theorem dy9 {R:Type*} [qx R] :
  p7 (aS7 (R:=R)) := by
 exact (NI R 1).symm.injective.comp
  (HZ _ (Kp R (Fin 1)).symm.injective)
private theorem aXY (d:Fin 2 →₀ ℕ) : (d.sum fun _ e=>e)=d 1+d 0:= by
 rw [WD _ _ (fun _=>rfl),TZ,Dz]
private theorem cDd {R:Type*} [qx R]
   (P:u5 (u5 R)) (B:ℕ) :
   (aS7 P).totalDegree≤B ↔
     ∀ j i,(P.coeff j).coeff i≠0→i+j≤B:= by
 constructor
 · intro h j i hji
   let d:Fin 2 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![j,i]
   have hd:d∈(aS7 P).support := by
     rw [zuk,cF6]
     exact hji
   have hsum:=(Zg hd).trans h
   rw [aXY] at hsum
   exact hsum
 · intro h
   unfold SW
   apply Finset.sup_le
   intro d hd
   rw [aXY]
   rw [zuk,cF6] at hd
   exact h _ _ hd
private theorem dMn (G:tK) (j i:ℕ) :
  ((Gw G).coeff j).coeff i=lV ((G.coeff j).coeff i) := by
 simp only [Gw,qQ.Ng,Polynomial.coe_mapRingHom,xu]
private theorem ecM (G:tK) : (Gw G).natDegree=G.natDegree := by
 exact KI
  (HZ _ (IU (Fin 2) FX)) G
private theorem ecL {P:Jet} {G:tK} {s :Shape}
   (hP:P≠0) (hCaps :oU P s) (hd:Gw G∣P) :
   abM G s.B s.J:= by
 have hG:G≠0:= by
   intro h
   exact hP (zero_dvd_iff.mp (by simpa only [h,pC] using hd))
 have hJ:P.natDegree≤ s.J:= by
   apply natDegree_le_iff_coeff_eq_zero.mpr
   intro j hj
   apply Polynomial.ext
   intro i
   rw [vw]
   by_contra hi
   exact (Nat.not_le_of_lt hj) (hCaps j i hi).2.1
 have hB: (aS7 P).totalDegree≤ s.B :=
   (cDd P s.B).mpr (fun j i h=>(hCaps j i h).1)
 have hfixedB: (aS7 (Gw G)).totalDegree≤ s.B:= by
   apply (MvPolynomial.totalDegree_le_of_dvd_of_isDomain (zc aS7 hd) _).trans hB
   exact fun h=>hP (dy9 (h.trans (pC aS7).symm))
 refine ⟨hG,?_,?_⟩
 · rw [← ecM G]
   exact (Ef hd hP).trans hJ
 · intro j i hji
   apply (cDd (Gw G) s.B).mp hfixedB j i
   rw [dMn]
   exact fun h=>hji ((IU (Fin 2) FX) (h.trans (pC _).symm))
private theorem extract (P:Jet) :P≠0 →
   ∃ (G:tK) (R:Jet),P=Gw G*R ∧
     ∀ D:tK,GB (Gw D) → ¬ Gw D ∣R:= by
 classical
 refine (wellFounded_dvdNotUnit (α:=Jet)).induction
   (C:= fun P=>P≠0 → ∃ (G:tK) (R:Jet),P=Gw G*R ∧
     ∀ D:tK,GB (Gw D) → ¬ Gw D ∣R) P ?_
 intro P ih hP
 by_cases h : ∃ D:tK,GB (Gw D)∧Gw D ∣P
 · obtain ⟨D,hD,Q,hQ⟩:=h
   have hQ0:Q≠0:= by
     intro hz
     exact hP (by simpa [hz] using hQ)
   have hlt:DvdNotUnit Q P:=⟨hQ0,Gw D,hD.not_isUnit,hQ.trans (p9 _ _)⟩
   obtain ⟨G,R,hR,hstrip⟩:=ih Q hlt hQ0
   refine ⟨D *G,R,?_,hstrip⟩
   rw [ox ,pU,← hR,← hQ]
 · refine ⟨1,P,by rw [map_one,one_mul],?_⟩
   exact fun D hD hdiv=>h ⟨D,hD,hdiv⟩
theorem proof :pI.c1 := by
 intro P s hP hCaps
 obtain ⟨G,R,hfac,hstrip⟩:=extract P hP
 exact ⟨⟨G,ecL hP hCaps ⟨R,hfac⟩,R,hfac,hstrip⟩⟩
end
end bRI
end
