import ProximityPrize.SubmissionLower.S
import ProximityPrize.SubmissionLower.AC
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
open _root_ renaming Algebra→lV,Algebra.IsAlgebraic→C5,Algebra.IsAlgebraic.isAlgebraic→zgs,Algebra.IsIntegral→Rm,Algebra.TensorProduct.comm→zOQ,Algebra.TensorProduct.map→zv2,Algebra.TensorProduct.tensorQuotientEquiv→zTd,Algebra.adjoin→yB,Algebra.algebraMap→c9,Algebra.algebraMap_self_apply→Pk,Algebra.linearMap→zdh,Algebra.ofId→Qx,Algebra.self_mem_adjoin_singleton→G9,Algebra.smul_def→xI,Algebra.trdeg→t4,Cardinal→Df,CommRing→ oq,DFunLike.congr_fun→Lf,Derivation→G4,DirectSum.decompose→z9,ExpChar→y5,False.elim→NY,Field→lz,Fin.sum_univ_eq_sum_range→Kl,Finite→ oy,Finset→p9,Finset.filter_subset→zT0,Finset.le_sup→Gk,Finset.mem_filter→zO0,Finset.mem_image_of_mem→zPV,Finset.mem_range→Y4,Finset.mem_univ→uW,Finset.mul_sum→G6,Finset.prod_mul_distrib→GB,Finset.prod_pow_eq_pow_sum→Gi,Finset.range→Eg,Finset.single_le_sum→zfK,Finset.sum_congr→t6,Finset.sum_eq_single→S1,Finset.sum_eq_zero→J4,Finset.sum_ite_eq→RD,Finset.sum_le_sum→zQk,Finset.sum_mul→KH,Finset.sup_eq_bot_iff→Kv,Finset.sup_le→C4,Finset.univ→zi,Finsupp.degree_apply→zqc,Finsupp.degree_eq_sum→PA
open _root_ renaming Fintype→p7,Fintype.card→zm,Fintype.equivFin→NW,Fintype.ofFinite→JK,FractionRing→pC,FractionRing.algEquiv→zwr,Function.Bijective→VO,Function.Injective→ oY,Function.Surjective→v8,Function.iterate_succ_apply'→ZJ,Function.mem_support→Zg,Function.support→yQ,Ideal→cy,Ideal.IsPrime.comap→EK,Ideal.Quotient.eq→Et,Ideal.Quotient.eq_zero_iff_mem→vw,Ideal.Quotient.liftₐ→Re,Ideal.Quotient.mk→lI,Ideal.Quotient.mk_surjective→sH,Ideal.Quotient.mkₐ→G3,Ideal.Quotient.mkₐ_eq_mk→Zt,Ideal.homogeneous_span→zqZ,Ideal.le_comap_map→zzQ,Ideal.map_span→KI,Ideal.mem_map_of_mem→WY,Ideal.mem_span_singleton_self→NX,Ideal.mem_sup_right→Up,Ideal.mul_mem_right→UY,Ideal.pow_le_pow_right→zdr,Ideal.quotientEquivAlg→Un,Ideal.quotientMap→NI,Ideal.quotientMap_injective→zR,Ideal.quotientMapₐ→Mz,Ideal.quotient_map_mkₐ→zhw,Ideal.span→nq,Ideal.subset_span→Aa,IntermediateField→Cy,IntermediateField.adjoin→nI,IntermediateField.adjoin_le_iff→zmT,IntermediateField.inclusion→KA,IntermediateField.isAlgebraic_adjoin_simple→Xg,IntermediateField.mem_adjoin_of_mem→LQ,IntermediateField.mem_adjoin_simple_self→TI,IntermediateField.topEquiv→zYd,Irreducible→N0,IsAlgClosed→qJ,IsAlgClosed.algebraMap_bijective_of_isIntegral→Z0,IsAlgebraic→Vq
open _root_ renaming IsCoprime→G1,IsDedekindDomain→ IT,IsDomain→yo,IsFractionRing→ze,IsFractionRing.div_surjective→P7,IsFractionRing.injective→wB,IsFractionRing.integerNormalization_eq_zero_iff→zQC,IsFractionRing.lift→PM,IsFractionRing.lift_algebraMap→zoc,IsFractionRing.map→zf,IsFractionRing.ringHom_ext→Nr,IsIntegral→x7,IsLeftRegular→JW,IsLocalHom→R9,IsLocalRing.maximalIdeal→zrY,IsLocalization.integerNormalization→Gn,IsLocalization.map→zZC,IsLocalization.map_algebraMap_ne_top_iff_disjoint→WW,IsLocalization.map_eq→S2,IsLocalization.mk'_mem_map_algebraMap_iff→zNj,IsNoetherianRing→th,IsPrincipalIdealRing→Hw,IsScalarTower→vk,IsScalarTower.algebraMap_apply→Au,IsScalarTower.algebraMap_eq→RP,IsScalarTower.of_algebraMap_eq→G2,IsScalarTower.toAlgHom→Yi,LinearEquiv.ofBijective→Yc,LinearMap.ker→wY,LinearMap.ker_eq_bot'→zmb,LinearMap.mem_ker→Gr,LinearMap.range→FV,LinearMap.toSpanSingleton_apply→ztR,LinearOrder→G8,Localization.AtPrime→qG,Localization.Away→zUG,Localization.isLocalHom_localRingHom→RC,Localization.localRingHom→Ml,Module.Finite→ oZ,Module.Finite.of_injective→zfv,Module.Finite.of_surjective→ II,Module.Finite.trans→zWg,Module.Free.ChooseBasisIndex→Zi,Module.Free.chooseBasis→Ts,Module.IsTorsionFree→zYp,Module.coe_length→WK,Module.finrank→ oj,Module.finrank_eq_card_basis→zdK
open _root_ renaming Module.finrank_eq_nat_card_basis→zUF,Module.finrank_pos→zRt,Module.length→t3,MvPolynomial→aU,MvPolynomial.C→p5,MvPolynomial.X→mD,MvPolynomial.aeval→qU,MvPolynomial.aeval_C→zXr,MvPolynomial.aeval_X→xu,MvPolynomial.affineDegree→qz,MvPolynomial.affineDegree_nonneg→SC,MvPolynomial.affineHilbertFunction→vl,MvPolynomial.affineHilbertFunction_eq_standard_count→zU2,MvPolynomial.affineHilbertPolynomial→qy,MvPolynomial.affineHilbertPolynomial_eq_C_finrank→ztK,MvPolynomial.algebraTensorAlgEquiv→LP,MvPolynomial.algebraTensorAlgEquiv_tmul→zVJ,MvPolynomial.coeff_homogeneousComponent→ IU,MvPolynomial.decomposition.decompose'_apply→Sd,MvPolynomial.eq_affineHilbertPolynomial_of_eval_eq→LR,MvPolynomial.eval→zY9,MvPolynomial.eval₂→yL,MvPolynomial.eval₂Hom→vH,MvPolynomial.eval₂Hom_C→JQ,MvPolynomial.eval₂Hom_X'→xW,MvPolynomial.eventually_eval_affineHilbertPolynomial→Kc,MvPolynomial.eventually_eval_affineHilbertPolynomial_nonneg→zwW,MvPolynomial.exists_eval_affineHilbertPolynomial→FR,MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus→zwb,MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree→VS,MvPolynomial.homogeneousComponent→lJ,MvPolynomial.homogeneousComponent_eq_self→z7,MvPolynomial.homogeneousComponent_eq_zero→zS,MvPolynomial.homogeneousComponent_isHomogeneous→qm,MvPolynomial.homogeneousComponent_mem→ Il,MvPolynomial.homogeneousComponent_mem_of_mem→zfi,MvPolynomial.homogeneousComponent_of_mem→Ar,MvPolynomial.homogeneousSubmodule→pG,MvPolynomial.induction_on→WD,MvPolynomial.induction_on'→zNP,MvPolynomial.isHomogeneous_X→G0,MvPolynomial.isHomogeneous_monomial→HZ,MvPolynomial.map→pz,MvPolynomial.map_X→WX,MvPolynomial.mem_iff_homogeneousComponent_mem→Nq,MvPolynomial.mem_restrictTotalDegree→uJ,MvPolynomial.mk_mem_quotientDegreeLE→t8,MvPolynomial.monomial→wA
open _root_ renaming MvPolynomial.natDegree_affineHilbertPolynomial_eq_of_finite_of_injective→zMe,MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le→zy5,MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one→SD,MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime→XB,MvPolynomial.quotientDegreeLE→ oD,MvPolynomial.quotientDegreeLE_mono→GR,MvPolynomial.restrictTotalDegree→Dz,MvPolynomial.ringHom_ext→zh,MvPolynomial.sum_homogeneousComponent→Kp,MvPolynomial.totalDegree_add→Kh,MvPolynomial.totalDegree_mul→zk,MvPolynomial.totalDegree_sub→Ea,MvPolynomial.vanishingIdeal_zeroLocus_eq_radical→TH,MvPolynomial.zeroLocus→pL,Nat.add_comm→SM,Nat.add_le_add→Ok,Nat.add_sub_cancel→Wm,Nat.cast_one→Ef,Nat.choose_zero_right→X4,Nat.le_of_lt_succ→SL,Nat.lt_succ_of_le→OJ,Nat.sub_add_cancel→zxt,Nat.sub_le_sub_right→Ze,Nat.succ_le_of_lt→Vl,Option→yJ,Pi.single→LO,Polynomial→xm,Polynomial.C→p6,Polynomial.C_mul→Qy,Polynomial.C_mul_X_pow_eq_monomial→TZ,Polynomial.X→ ov,Polynomial.aeval→EP,Polynomial.algEquivOfTranscendental→Kz,Polynomial.algebraMap_apply→zpj,Polynomial.algebraMap_eq→zrE,Polynomial.coe_eval₂RingHom→Ee,Polynomial.coe_mapRingHom→Zf,Polynomial.coeff_C_mul_X_pow→zds,Polynomial.coeff_add→Xo,Polynomial.coeff_map→Np,Polynomial.coeff_zero→Bf,Polynomial.eval₂RingHom→vj,Polynomial.eval₂_C→Qw,Polynomial.eval₂_X→XJ,Polynomial.eval₂_monomial→Pv,Polynomial.finsetSum_coeff→zaW,Polynomial.hasseDeriv→wR,Polynomial.hasseDeriv_monomial→Zh
open _root_ renaming Polynomial.hom_eval₂→zly,Polynomial.induction_on'→X8,Polynomial.mapRingHom→zE,Polynomial.map_C→Mj,Polynomial.map_map→zoi,Polynomial.map_mul→zNl,Polynomial.map_ne_zero_iff→zeI,Polynomial.monomial→yU,Polynomial.natDegree_le_of_eventually_eval_natCast_le→VH,Polynomial.natDegree_map_eq_of_injective→zt8,Polynomial.ringHom_ext→Xp,RatFunc→nX,RatFunc.C→uh,RatFunc.X→Dw,Ring.ord→G7,RingHom.comp_apply→vZ,RingHom.congr_fun→FK,RingHom.ext→Vz,RingHom.id→VC,RingHom.injective→zyB,RingHom.ker→sI,RingHom.ker_comp_of_injective→Yo,RingHom.ker_isPrime→SU,RingHomInvPair.of_ringEquiv→zaI,Set.InjOn→MK,Set.finite_iUnion→UZ,Set.image_singleton→Vs,Set.mem_iUnion→Ob,Set.mem_range_self→FU,Set.mem_singleton→zT1,Set.ncard_le_ncard→Ye,Set.range→vh,Subalgebra→JM,Subalgebra.inclusion→Pj,Submodule→z8,Submodule.comapSubtypeEquivOfLe→zTz,Submodule.map_mono→zzl,Submodule.mem_colon_singleton→Mw,Submodule.mem_inf→zqd,Submodule.mem_top→Xu,Submodule.smul_mem→Sv,Submodule.span→Fa,Submodule.span_induction→zt0,Submodule.subset_span→XG,Submodule.sum_mem→C9,Subtype.ext→u8,Subtype.val→Nj,Subtype.val_injective→MO
open _root_ renaming TensorProduct.equivFinsuppOfBasisLeft→znv,TensorProduct.inductionOn→Wl,Transcendental→pU,UniqueFactorizationMonoid.normalizedFactors→Av,Valuation→xL,WellFoundedGT→ In,congrArg→ oK,dN.GeoField→ ox,dN.GeoJets→pQ,dN.separant→qx,dite_eq_left→Fz,faithfulSMul_iff_algebraMap_injective→zSO,finsum_eq_finsetSum_of_support_subset→ZK,inferInstance→u9,integralClosure→Dv,integralClosure.isFractionRing_of_finite_extension→zij,inv_mul_cancel₀→QL,isIntegral_algebraMap→Oc,ite_eq_left→u5,ite_eq_right→vG,iterateFrobenius→SW,iterateFrobenius_inj→zPu,le_antisymm→vi,le_max_left→Xx,le_max_right→UP,le_rfl→zc,le_sup_left→zg,lt_of_le_of_lt→PD,lt_of_le_of_ne→RJ,map_add→qM,map_div₀→Mk,map_mul→n5,map_natCast→ Iw,map_ne_zero_iff→G5,map_one→Gj,map_pow→t9,map_smul→FQ,map_sub→sS,map_sum→ oz,map_zero→t7,max_le→zd,minpoly→F9,mul_assoc→yl,mul_comm→t5,mul_div_cancel_right₀→Ww,mul_ne_zero→Pc,mul_one→GY,mul_pow→Du
open _root_ renaming nonZeroDivisors→GF,nonZeroDivisors.ne_zero→MS,not_le_of_gt→Te,one_mul→uz,smul_eq_mul→v9,sub_eq_zero→Pr,trdeg_add_eq→NZ,trdeg_eq_zero→Pf
set_option autoImplicit true
section
namespace czI
noncomputable section
open cu qQ Polynomial
open scoped Polynomial
set_option maxSynthPendingDepth 8
private abbrev apH :aZ →+* aQ:=c9 _ _
private abbrev aJP:aQ →+* HR:=c9 _ _
private theorem bxN :oY apH :=
 wB aZ aQ
private theorem god:oY aif :=
 aJP.injective.comp bxN
private theorem eJI {S:Type*} [oq S] (I J:cy S) (n j:ℕ) :
   (I ⊔ J)^(n+j)≤I ^n ⊔ J^(j+1) := by
 rw [← Ideal.add_eq_sup,add_pow,Ideal.sum_eq_sup]
 apply C4
 intro i hi
 by_cases hn:n≤ i
 · exact Ideal.mul_le_left.trans
     (Ideal.mul_le_left.trans ((zdr hn).trans zg))
 · refine Ideal.mul_le_left.trans
     (Ideal.mul_le_right.trans ((zdr ?_).trans le_sup_right))
   omega
private theorem eu8 {S:Type*} [oq S]
    (a b:S) (G:xm S) (k :ℕ)
    (h:G∈(nq ({C a,ov - C b} : Set S[X]))^k) :
    a^(k-G.natDegree)∣G.leadingCoeff := by
  let j:=G.natDegree
  change a^(k-j)∣G.coeff j
  by_cases hj:k≤j
  · simp [Nat.sub_eq_zero_of_le hj]
  let B:S[X] :=ov - C b
  have hpair :nq ({C a,B} : Set S[X]) =
      nq {C a} ⊔ nq {B} := by
    rw [← Ideal.span_union,Set.singleton_union]
  change G∈nq ({C a,B} : Set S[X])^k at h
  rw [hpair] at h
  have hle :=eJI (nq ({C a} : Set S[X])) (nq {B}) (k-j) j
  rw [zxt (by omega :j≤k)] at hle
  have hsum:G∈nq ({C (a^(k-j))} : Set S[X]) ⊔
      nq {B^(j+1)} := by
    simpa only [Ideal.span_singleton_pow,← C_pow] using hle h
  obtain ⟨r,hr,s,hs,hrs⟩:=Submodule.mem_sup.mp hsum
  obtain ⟨e,he⟩:=Ideal.mem_span_singleton.mp hr
  obtain ⟨d,hd⟩:=Ideal.mem_span_singleton.mp hs
  let I:cy S:=nq {a^(k-j)}
  let π:=lI I
  let φ:=zE π
  have hπ:π (a^(k-j))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (NX _)
  let B' : (S ⧸ I)[X] :=ov - C (π b)
  have hφC:φ (C (a^(k-j)))=0:= by
    change (C (a^(k-j))).map π=0
    rw [Mj,hπ,C_0]
  have hφB:φ B=B' := by
    change B.map π=B'
    simp only [B,B',Polynomial.map_sub,Polynomial.map_X,Mj]
  have hmap :φ G=B' ^ (j+1)*φ d:= by
    rw [← hrs,he,hd,qM,n5 ,hφC,zero_mul,zero_add,n5 ,t9,hφB]
  have hzero :φ G=0:= by
    by_contra hn
    have :Nontrivial (S ⧸ I) := by
      rcases subsingleton_or_nontrivial (S ⧸ I) with hsub | hnon
      · have :=hsub
        exact NY (hn (Subsingleton.elim _ _))
      · exact hnon
    have hm:B'.Monic:=monic_X_sub_C _
    have hdeg: (B' ^ (j+1)).natDegree=j+1 := by
      rw [hm.natDegree_pow,show B'.natDegree=1 from natDegree_X_sub_C _,GY]
    have hlt: (φ G).natDegree<(B' ^ (j+1)).natDegree := by
      rw [hdeg]
      exact OJ (natDegree_map_le (p:=G) (f :=π))
    exact (hm.pow _).not_dvd_of_natDegree_lt hn hlt ⟨φ d,hmap⟩
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (G.coeff j)=0
  rw [← Np,show G.map π=0 from hzero,Bf]
private theorem eai {q:zI} {y v :HR}
  (hq:aF5 q y v) {P:Jet} {k :ℕ} (h:wU q P k) :
  (ov - C y)^(k-P.natDegree)∣P.leadingCoeff.map aif := by
 have hi:oY (zE aif) :=
  Polynomial.map_injective _ god
 have hc:=eu8 (ov - C y) (C v) (aUO P) k (h y v hq)
 unfold aUO at hc
 rw [zt8 hi,leadingCoeff_map_of_injective hi] at hc
 exact hc
private theorem eAz {y :HR} (hy :IsSeparable aQ y)
   {n:ℕ} {g:aQ[X]} (h: (ov - C y)^n∣g.map aJP) :
   F9 aQ y ^n∣g:= by
 induction n generalizing g with
 | zero=>simp
 | succ n ih =>
   by_cases hg:g=0
   · simp [hg]
   have hgmap :g.map aJP≠0 :=
     (zeI aJP.injective).mpr hg
   have hlin:ov - C y∣g.map aJP :=
     (dvd_pow_self _ (by omega :n+1≠0)).trans h
   have hroot : (g.map aJP).IsRoot y :=dvd_iff_isRoot.mp hlin
   have hmin:F9 aQ y∣g:= by
     apply minpoly.dvd
     simpa only [IsRoot.def,eval_map,aeval_def] using hroot
   obtain ⟨g',rfl⟩:=hmin
   have hsep: ((F9 aQ y).map aJP).Separable :=
     Polynomial.Separable.map hy
   have hle :=rootMultiplicity_le_one_of_separable hsep y
   rw [zNl] at hgmap h
   have hmul :=(le_rootMultiplicity_iff (a :=y) hgmap).mpr h
   rw [rootMultiplicity_mul hgmap] at hmul
   have hg'map :g'.map aJP≠0:=right_ne_zero_of_mul hgmap
   have hrest: (ov - C y)^n∣g'.map aJP :=
     (le_rootMultiplicity_iff (a :=y) hg'map).mp (by omega)
   rw [pow_succ']
   exact mul_dvd_mul_left _ (ih hrest)
@[instance_reducible] private def dcL:NormalizedGCDMonoid aZ:= by
  let:UniqueFactorizationMonoid aZ:=MvPolynomial.uniqueFactorizationMonoid (σ:=Fin 2)
  let:=UniqueFactorizationMonoid.strongNormalizationMonoid (α:=aZ)
  exact UniqueFactorizationMonoid.toNormalizedGCDMonoid aZ
private theorem eOk (g:aQ[X]) (hg:g≠0) :
    ∃ f :Equation,f.IsPrimitive∧Associated (f.map apH) g:= by
  classical
  let:=dcL
  let D:Equation :=Gn (GF aZ) g
  obtain ⟨a,ha,hD⟩:=IsLocalization.integerNormalization_spec (GF aZ) g
  have hD0:D ≠0 :=
    (zQC (A:=aZ) (p:=g)).not.mpr hg
  have hcontent:IsUnit (C (apH D.content)) := by
    apply isUnit_C.mpr
    exact ((G5 apH bxN).mpr (content_eq_zero_iff.not.mpr hD0)).isUnit
  have ha' : IsUnit (C (apH a)) :=
    isUnit_C.mpr ((G5 apH bxN).mpr (MS ha)).isUnit
  have hscale :C (apH D.content)*D.primPart.map apH=C (apH a)*g:= by
    calc
      _=D.map apH := by
        rw [← Mj,← zNl,← D.eq_C_content_mul_primPart]
      _ = _:= by
        simpa only [xI,zpj] using hD
  refine ⟨D.primPart,D.isPrimitive_primPart,?_⟩
  have hunit :Associated (C (apH a)*g) g:=associated_unit_mul_left _ _ ha'
  rw [← hscale] at hunit
  exact (associated_unit_mul_right _ _ hcontent).trans hunit
private theorem d1S (f :Equation) (y v :HR) :
  aXz y v (C f)=EP y (f.map apH) := by
 change (vj (vj aif y) v) (C f)= _
 rw [Ee,Qw ,Ee,aeval_def,eval₂_map]
 rfl
theorem proof :qQ.c7:= by
  classical
  intro qs hqs hparents
  choose y v hpoint hy _hv using fun q : ↥qs=>(hparents q q.property).seed_side
  let m (q : ↥qs) :=F9 aQ (y q)
  let factors :p9 (aQ[X]) :=qs.attach.image m
  have hmem (q : ↥qs) :m q∈factors :=
    Finset.mem_image.mpr ⟨q,Finset.mem_attach _ _,rfl⟩
  have hpre {u:aQ[X]} (hu:u∈factors) : ∃ q : ↥qs,m q=u:= by
    obtain ⟨q,_,hq⟩:=Finset.mem_image.mp hu
    exact ⟨q,hq⟩
  have hmonic (u:aQ[X]) (hu:u∈factors) :u.Monic:= by
    obtain ⟨q,rfl⟩:=hpre hu
    exact minpoly.monic (hy q).isIntegral
  have hirr (u:aQ[X]) (hu:u∈factors) :N0 u:= by
    obtain ⟨q,rfl⟩:=hpre hu
    exact minpoly.irreducible (hy q).isIntegral
  have hpair (u:aQ[X]) (hu:u∈factors) (w:aQ[X]) (hw:w∈factors)
      (hne :u≠w) :G1 u w:= by
    apply (hirr u hu).coprime_iff_not_dvd.mpr
    intro hd
    exact hne (eq_of_monic_of_associated (hmonic u hu) (hmonic w hw)
      (associated_of_dvd_dvd hd ((hirr u hu).dvd_symm (hirr w hw) hd)))
  let g:aQ[X] := ∏ u∈factors,u
  have hg:g≠0:=(monic_prod_of_monic _ _ hmonic).ne_zero
  have hsep:g.Separable := by
    apply separable_prod' hpair
    intro u hu
    obtain ⟨q,rfl⟩:=hpre hu
    exact hy q
  have hm_dvd (q : ↥qs) :m q∣g:=Finset.dvd_prod_of_mem id (hmem q)
  obtain ⟨f,hprim,hassoc⟩:=eOk g hg
  have hfmap :f.map apH≠0 :=
    (zeI bxN).mpr hprim.ne_zero
  refine ⟨f,⟨?_,hprim,hsep.of_dvd hassoc.dvd,?_,?_⟩⟩
  · obtain ⟨q,hq⟩:=hqs
    have hdeg:=natDegree_le_of_dvd ((hm_dvd ⟨q,hq⟩).trans hassoc.dvd') hfmap
    rw [zt8 bxN] at hdeg
    exact (hirr _ (hmem ⟨q,hq⟩)).natDegree_pos.trans_le hdeg
  · intro q hq
    let q' : ↥qs :=⟨q,hq⟩
    rw [← hpoint q',RingHom.mem_ker,d1S]
    exact minpoly.dvd_iff.mp ((hm_dvd q').trans hassoc.dvd')
  · intro P k _ horder
    let n:=k-P.natDegree
    have hdiv :g^n∣P.leadingCoeff.map apH := by
      rw [show g^n = ∏ u∈factors,u^n from (Finset.prod_pow factors n id).symm]
      apply Finset.prod_dvd_of_coprime
      · intro u hu w hw hne
        exact (hpair u hu w hw hne).pow
      · intro u hu
        obtain ⟨q,rfl⟩:=hpre hu
        have hc:=eai (hpoint q) (horder q q.property)
        rw [show aif=aJP.comp apH from rfl,← zoi] at hc
        exact eAz (hy q) hc
    let:=dcL
    have hpow (e :ℕ) : (f^e).IsPrimitive := by
      induction e with
      | zero=>simpa only [pow_zero] using (isPrimitive_one : (1 :Equation).IsPrimitive)
      | succ e ih=>rw [pow_succ]; exact ih.mul hprim
    apply (hpow n).dvd_of_fraction_map_dvd_fraction_map (K:=aQ)
    rw [Polynomial.map_pow]
    exact hassoc.pow_pow.dvd.trans hdiv
end
end czI
end
section
namespace rW
noncomputable section
open aR dN Polynomial
open scoped BigOperators
abbrev jo:=aU (Fin bf) ao
abbrev mK:=aU (Fin bf) ox
abbrev kT:=cy jo
abbrev n8:=cy pQ
abbrev dimension {k σ:Type*} [lz k] [oy σ] (P:cy (aU σ k)) :=
 (qy P).natDegree
def ni:ao →+* GeoField:=j8.comp p6
def rI:GeoField:=j8 ov
def Gp (S:ao[X]) (i:Fin bf) :ao:=S.coeff i
def J1 {k :Type*} [lz k] (a :k) (i:ℕ) :
    aU (Fin bf) k :=
  ∑ j:Fin bf,
    p5 ((j.val.choose i:k)*a^(j.val - i))*mD j
def gN (A:kT) :cy mK :=
 A.map (pz ni)
def mS:pQ →+* mK :=
 vH p5 (fun i=>J1 rI i.val)
def lA (A:kT) :n8 :=
 (gN A).comap mS
def bQ1 (f :af 4) (A:kT) :Prop :=
  ∃ r :ℕ,bC ((qx^[r]) f)∈lA A ∧
    bC (qx ((qx^[r]) f))∉lA A
def asY (A:kT) :Prop :=
  ∀ h:mK,∃ u v :pQ,
    mS v∉gN A ∧
    h*mS v - mS u∈gN A
abbrev tJ (P:n8) :=pC (pQ ⧸ P)
def K4 (P:n8) :pQ →+* tJ P :=
 (c9 (pQ ⧸ P) (tJ P)).comp (lI P)
def CX (P:n8) :ao →+* tJ P :=
 ((K4 P).comp p5).comp ni
def Zv {F:Type*} [lz F] (k :ao →+* F) (U:F[X]) :kT :=
 sI (vH k (fun i=>U.coeff i.val))
def jW {F:Type*} [lz F] (k :ao →+* F) (P:af 4) (U:F[X]) :F[X] :=
 yL (zE k) (fun i=>wR i.val U) P
structure anF (g:af 4) (aI P:n8) :Prop where
 proper :bC (vU g)∉aI
 minimal: (AX aI (vU g)).IsMinimalPrime P
 one :oA (AX aI (vU g)) P minimal.isPrime=1
 next:bC (ZV g)∈P
structure bjr (f Q g:af 4) (P:n8) [P.IsPrime]
  (U: (tJ P)[X]) :Prop where
 degree :U.natDegree<bf
 initial : ∀ i:Fin 4,
  (wR i.val U).eval (K4 P (p5 rI)) =
    K4 P (mD i)
 factor :jW (CX P) f U=0
 an1 :jW (CX P) Q U=0
 bY:jW (CX P) g U=0
 specializes : ∀ S:ao[X],S.natDegree<bf→P≤Ch S →
  cK (qx g) S≠0 →
  Gp S∈pL ao (Zv (CX P) U)
structure aYK (f :af 4) (A:kT) :Prop where
 prime :A.IsPrime
 extended_prime : (gN A).IsPrime
 regular :bQ1 f A
 birational:asY A
def Yg (J P:n8) :ℕ:= by
 classical
 exact if hp:P.IsPrime then (oA J P hp).toNat else 0
end
end rW
end
section
namespace rW
noncomputable section
open K1 aR dN Polynomial MvPolynomial
open scoped BigOperators
def rV (s :K→K[X]) (γ:K) :Fin bf→ao :=
 Gp (extend (s γ))
def VA (x a :K) :jo:=J1 (embed x) 0-MvPolynomial.C (embed a)
theorem aQ5 (x a :K) : (VA x a).totalDegree≤1 := by
 unfold VA J1
 apply (Ea _ _).trans
 simp only [totalDegree_C,Nat.max_zero]
 exact totalDegree_finsetSum_le (fun j _ =>
  (zk _ _).trans (by rw [totalDegree_C,totalDegree_X,zero_add]))
theorem aFp {s :K→K[X]} {γ x a :K} (h: (s γ).natDegree<bf) :
   qU (rV s γ) (VA x a)=0↔(s γ).eval x=a := by
 have heval :qU (rV s γ) (J1 (embed x) 0)=embed ((s γ).eval x) := by
   rw [Polynomial.eval_eq_sum_range' h,← Kl,oz]
   simp only [J1,oz ,n5 ,t9,zXr,xu,Pk,X4 ,
     Ef ,Nat.sub_zero,uz ,rV,Gp,Np,t5]
 rw [VA,sS ,heval,zXr,Pk,Pr,embed.injective.eq_iff]
def aaL (A:kT) :ℕ := ⌊qz A⌋₊
theorem dVb (A:kT) : (aaL A:ℚ)≤qz A :=
 Nat.floor_le (SC A)
private theorem bZ8 {A:kT} (hp:A.IsPrime)
    {x :Fin bf→ao} (hx :x∈pL ao A) :1≤qz A:= by
  classical
  generalize hd:dimension A=d
  induction d using Nat.strong_induction_on generalizing A with
  | h d ih =>
    by_cases hd0:d=0
    · obtain ⟨hf,hdeg⟩:=VS
        (K:=ao) A (hd.trans hd0)
      have hcard:1≤(pL ao A).ncard:= by
        simpa using Ye (Set.singleton_subset_iff.mpr hx) hf
      exact (by exact_mod_cast hcard: (1 :ℚ)≤_).trans hdeg
    have hcut : ∃ i,mD i-MvPolynomial.C (x i)∉A:= by
      by_contra! hall
      let φ:=lI A
      have hmaps :φ=φ.comp (MvPolynomial.C.comp (zY9 x)) := by
        apply zh
        · intro c
          simp [φ]
        · intro i
          simp only [vZ,MvPolynomial.eval_X]
          exact sub_eq_zero.mp (by
            rw [← sS]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i))
      have hsurj:v8 (c9 ao (jo ⧸ A)) := by
        intro q
        obtain ⟨g,rfl⟩:=sH q
        refine ⟨zY9 x g,?_⟩
        exact (FK hmaps g).symm
      let _:oZ ao (jo ⧸ A) :=
        II (zdh ao (jo ⧸ A)) hsurj
      exact hd0 (hd.symm.trans (by simp [dimension,ztK]))
    obtain ⟨i,hi⟩:=hcut
    let cut:jo:=mD i-MvPolynomial.C (x i)
    have hdeg:cut.totalDegree≤1 :=(Ea _ _).trans (by simp)
    have hzero :x∈pL ao (A ⊔ nq {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx,by simp [cut]⟩
    obtain ⟨B,hB,hxB⟩:=zwb
      _ (1 :jo) _ hzero (by simp)
    have hm:=(Ideal.mem_retainedMinimalPrimes.mp hB).1
    let _:=hp
    have hdim:=SD hi hm
    change dimension B+1=dimension A at hdim
    have hBdeg:=ih (dimension B) (by omega) hm.isPrime hxB rfl
    have hsum:=principalCut_sum_affineDegree_retainedMinimalPrimes_le
      (1 :jo) hi hdeg
    have hle :=zfK (f :=qz) (fun B _=>SC B) hB
    simpa only [Ef ,uz] using hBdeg.trans (hle.trans hsum)
def JI (Γ:p9 K) (s :K→K[X]) (A:kT) :p9 K:= by
 classical
 exact Γ.filter fun γ=>rV s γ∈pL ao A
theorem P6 {Γ:p9 K} {s :K→K[X]} {A:kT} {γ:K} :
  γ∈JI Γ s A↔γ∈Γ∧rV s γ∈pL ao A:= by
 classical
 simp [JI]
theorem aT4 {Γ:p9 K} {s :K→K[X]} {A:kT}
  (hp:A.IsPrime) (h: (JI Γ s A).Nonempty) :0<aaL A:= by
 obtain ⟨γ,hγ⟩:=h
 exact Nat.floor_pos.mpr (bZ8 hp (P6.mp hγ).2)
def aa9 {Γ:p9 K} (T:p9 kT) (part:kT→p9 K)
    (hpart : ∀ A∈T,part A⊆Γ) :DA Γ :=
  ⟨T.card,fun i=>part (T.equivFin.symm i),
    fun i=>hpart _ (T.equivFin.symm i).property,fun i=>aaL (T.equivFin.symm i)⟩
theorem a5M {Γ:p9 K} {T:p9 kT} {part:kT→p9 K}
   {hpart : ∀ A∈T,part A⊆Γ} {γ:K} :
   γ∈(aa9 T part hpart).union ↔ ∃ A∈T,γ∈part A:= by
 classical
 constructor
 · intro h
   obtain ⟨i,-,hi⟩:=Finset.mem_biUnion.mp h
   exact ⟨T.equivFin.symm i,(T.equivFin.symm i).property,hi⟩
 · rintro ⟨A,hA,hγ⟩
   apply Finset.mem_biUnion.mpr
   refine ⟨T.equivFin ⟨A,hA⟩,uW _,?_⟩
   simpa [aa9] using hγ
theorem eLi {Γ:p9 K} {T:p9 kT} {part:kT→p9 K}
  {hpart : ∀ A∈T,part A⊆Γ} :
  (aa9 T part hpart).total = ∑ A∈T,aaL A:= by
 change ∑ i:Fin T.card,aaL (T.equivFin.symm i)= _
 calc
  _ = ∑ A:T,aaL A:=Fintype.sum_equiv T.equivFin.symm _ _ (fun _=>rfl)
  _ = _:=Finset.sum_attach T aaL
theorem a6x {Γ:p9 K} {T:p9 kT} {part:kT→p9 K}
  {hpart : ∀ A∈T,part A⊆Γ} :
  ((aa9 T part hpart).total:ℚ) ≤ ∑ A∈T,affineDegree A:= by
 rw [eLi,Nat.cast_sum]
 exact zQk fun A _=>dVb A
private theorem bKS {Γ:p9 K} {s :K→K[X]} {A:kT} {x a :K}
  (hdegree : ∀ γ∈Γ,(s γ).natDegree<bf)
  (hpoints : ∀ γ∈Γ,rV s γ∈pL ao A)
  (hmiss : ∃ γ∈Γ,(s γ).eval x≠a) :VA x a∉A:= by
 obtain ⟨γ,hγ,hmiss⟩:=hmiss
 exact fun hmem=>hmiss (aFp (hdegree γ hγ) |>.mp (hpoints γ hγ _ hmem))
private theorem bIZ {s :K→K[X]} {A:kT} {x a γ:K}
  (hdegree : (s γ).natDegree<bf) (hpoint :rV s γ∈pL ao A)
  (hvalue : (s γ).eval x=a) :
  rV s γ∈pL ao (A ⊔ nq {VA x a}) :=
 mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoint,(aFp hdegree).mpr hvalue⟩
theorem cIN {Γ:p9 K} {s :K→K[X]} {A:kT}
   (hp:A.IsPrime) (hdim:dimension A=1)
   (hdegree : ∀ γ∈Γ,(s γ).natDegree<bf)
   (hdistinct :MK (rV s) (Γ:Set K))
   (hpoints : ∀ γ∈Γ,rV s γ∈pL ao A) :
   agC Γ s (aaL A) := by
 classical
 let _:=hp
 intro x a hmiss
 let cut:=VA x a
 let J:=A ⊔ nq {cut}
 let H :=Γ.filter fun γ=>(s γ).eval x=a
 have hproper :=bKS hdegree hpoints hmiss
 have hJdim:dimension J=0:= by
   have hd:=(XB
     hp hproper (aQ5 x a)).1
   change dimension J≤dimension A - 1 at hd
   omega
 have hJdeg:qz J≤qz A:= by
   have h:=(XB
     hp hproper (aQ5 x a)).2
   have ha : (qy A).natDegree=1 :=hdim
   have hj: (qy J).natDegree=0:=hJdim
   simpa [qz ,ha,hj,J,cut,Polynomial.leadingCoeff] using h
 obtain ⟨hfinite,hcard⟩:=VS (K:=ao) J hJdim
 have hsub: (H.image (rV s) :Set _)⊆pL ao J:= by
   intro p hp
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hp
   obtain ⟨hΓ,hv⟩:=Finset.mem_filter.mp hγ
   exact bIZ (hdegree γ hΓ) (hpoints γ hΓ) hv
 have hcount:=Ye hsub hfinite
 rw [Set.ncard_coe_finset,Finset.card_image_of_injOn
   (hdistinct.mono (zT0 _ _))] at hcount
 exact Nat.le_floor ((Nat.cast_le.mpr hcount).trans (hcard.trans hJdeg))
theorem bxh {Γ:p9 K} {s :K→K[X]} {A:kT}
   (hp:A.IsPrime) (hdim:dimension A=2)
   (hdegree : ∀ γ∈Γ,(s γ).natDegree<bf)
   (hdistinct :MK (rV s) (Γ:Set K))
   (hpoints : ∀ γ∈Γ,rV s γ∈pL ao A) :
   aB7 Γ s (aaL A) := by
 classical
 let _:=hp
 intro x a hmiss H
 let J:=A ⊔ nq {VA x a}
 let T:=J.minimalPrimesFinset.filter (fun B=>(JI H s B).Nonempty)
 have hproper :=bKS hdegree hpoints hmiss
 have hsubset (B:kT) (_:B∈T) :JI H s B⊆H :=
   fun _ h=>(P6.mp h).1
 have hprime (B:kT) (hB:B∈T) :J.IsMinimalPrime B :=
   Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hB).1
 refine ⟨aa9 T (JI H s) hsubset,?_,?_,?_,?_⟩
 · intro γ hγ
   obtain ⟨hΓ,hvalue⟩:=Finset.mem_filter.mp hγ
   have hzero :rV s γ∈pL ao J :=
     bIZ (hdegree γ hΓ) (hpoints γ hΓ) hvalue
   obtain ⟨B,hB,hxB⟩:=zwb
     J (1 :jo) _ hzero (by simp)
   have hmarks :γ∈JI H s B:=P6.mpr ⟨hγ,hxB⟩
   exact a5M.mpr ⟨B,Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr
     (Ideal.mem_retainedMinimalPrimes.mp hB).1,⟨γ,hmarks⟩⟩,hmarks⟩
 · intro i
   let B:=T.equivFin.symm i
   have hm:=hprime B B.property
   have hd:=SD hproper hm
   change dimension (B:kT)+1=dimension A at hd
   have hdimB:dimension (B:kT)=1 := by omega
   apply cIN hm.isPrime hdimB
   · exact fun γ hγ=>hdegree γ (Finset.mem_filter.mp (P6.mp hγ).1).1
   · exact hdistinct.mono (fun γ hγ=>(Finset.mem_filter.mp (P6.mp hγ).1).1)
   · exact fun _ hγ=>(P6.mp hγ).2
 · intro i
   let B:=T.equivFin.symm i
   exact aT4 (hprime B B.property).isPrime
     (Finset.mem_filter.mp B.property).2
 · apply Nat.le_floor
   have hsum:=principalCut_sum_affineDegree_minimalPrimes_le hproper (aQ5 x a)
   exact a6x.trans ((Finset.sum_le_sum_of_subset_of_nonneg
     (zT0 _ _) (fun B _ _=>SC B)).trans
     (by simpa only [Ef ,uz] using hsum))
end
end rW
end
section
namespace rW
noncomputable section
open K1 aR dN Polynomial MvPolynomial
open scoped BigOperators
def c3:Prop :=
  (∀ (f Q:af 4) (aI:n8) (r :ℕ) (P:n8) (hp:P.IsPrime)
      (U: (tJ P)[X]),
    (kC f Q).IsMinimalPrime aI →
    (∀ T,(kC f Q).IsMinimalPrime T→dimension T=2) →
    let g:=(qx^[r]) f
    bC (qx g)∉P→(P=aI∨anF g aI P) →
    @bjr f Q g P hp U →
    let A:=Zv (CX P) U
    aYK f A ∧
      ((dimension A=1∧lA A=P∧anF g aI P) ∨
        (dimension A=2∧(kC f Q).IsMinimalPrime (lA A)))) ∧
  (∀ f :af 4,MK lA {A | A.IsPrime∧bQ1 f A})
def c4 :Prop :=
  ∀ A:kT,A.IsPrime→(gN A).IsPrime→dimension A=1 →
    asY A→qz A=qz (lA A)
private theorem cDS {f :af 4} {aI:n8} {r t:ℕ}
   (hr :YR f aI r) (ht:YR f aI t) :r=t:= by
 rcases lt_trichotomy r t with h | h | h
 · have hm:=ht.2.1 (r+1) (Vl h)
   rw [ZJ] at hm
   exact NY (hr.2.2 hm)
 · exact h
 · have hm:=hr.2.1 (t+1) (Vl h)
   rw [ZJ] at hm
   exact NY (ht.2.2 hm)
end
end rW
end
section
namespace MJ
noncomputable section
open MvPolynomial dN rW
variable {k σ τ:Type*} [lz k]
def lW (A:cy (aU σ k)) :cy (aU σ k) :=
 nq {g | ∃ f∈A,lJ f.totalDegree f=g}
def ado (J P:cy (aU σ k)) :ℕ:= by
  classical
  exact if hp:P.IsPrime then
    letI:=hp
    let L:=qG P
    (t3 L (L ⧸ J.map (c9 (aU σ k) L))).toNat
  else 0
def QZ (φ:aU τ k →+* aU σ k)
    (P:cy (aU σ k)) :ℕ:= by
  classical
  exact if hp:P.IsPrime then
    letI:=hp
    letI: (P.comap φ).IsPrime :=EK φ
    let f :pC (aU τ k ⧸ P.comap φ) →+*
        pC (aU σ k ⧸ P) :=
      zf (zR (I:=P) (f :=φ))
    letI:=f.toAlgebra
    oj (pC (aU τ k ⧸ P.comap φ))
      (pC (aU σ k ⧸ P))
  else 0
def agH (φ:aU τ k →ₐ[k] aU σ k) :Prop :=
 ∀ i,(φ (mD i)).IsHomogeneous 1
def aRK (φ:aU τ k →ₐ[k] aU σ k)
    (A:cy (aU σ k)) :Prop :=
  ∀ h:aU σ k,∃ u v :aU τ k,φ v∉A∧h*φ v-φ u∈A
def tO:pQ →ₐ[ox] mK :=
 qU (fun i:Fin 4=>J1 rI i.val)
theorem cTa :agH tO:= by
 intro i
 rw [tO,xu,J1]
 apply IsHomogeneous.sum
 intro j _
 exact (isHomogeneous_C _ _).mul (G0 _ j)
end
end MJ
end
section
namespace WI
noncomputable section
open dN rW
open scoped BigOperators
section Quotients
variable {R:Type} [oq R]
def Vp (I:cy R) (g:R) :
    (R ⧸ I.colon {g}) →ₗ[R] (R ⧸ I) :=
  (I.colon {g}).liftQ (LinearMap.toSpanSingleton R (R ⧸ I) (lI I g))
    fun a ha=> by
      rw [Gr,ztR]
      change lI I a* lI I g=0
      rw [← n5]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_colon_singleton.mp ha)
@[simp]
theorem azY (I:cy R) (g a :R) :
  Vp I g (lI (I.colon {g}) a)=lI I (a*g) := by
 change Vp I g (Submodule.Quotient.mk a)= _
 rw [Vp,Submodule.liftQ_apply,ztR]
 exact (n5 (lI I) a g).symm
theorem aPy (I:cy R) (g:R) :oY (Vp I g) := by
 rw [← LinearMap.ker_eq_bot,zmb]
 intro a ha
 obtain ⟨x,rfl⟩:=sH a
 rw [azY,vw] at ha
 exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_colon_singleton.mpr ha)
theorem a7c (I:cy R) (g:R) :
   Function.Exact (Vp I g)
     (Submodule.factor (zg:I≤I ⊔ nq {g})) := by
 rw [LinearMap.exact_iff]
 ext y
 obtain ⟨b,rfl⟩:=sH y
 rw [Gr,LinearMap.mem_range]
 change (lI (I ⊔ nq {g}) b=0↔_)
 rw [vw]
 constructor
 · intro hb
   obtain ⟨i,hi,j,hj,hsum⟩:=Submodule.mem_sup.mp hb
   obtain ⟨x,rfl⟩:=Ideal.mem_span_singleton.mp hj
   refine ⟨lI (I.colon {g}) x,?_⟩
   rw [azY,Et,← hsum]
   convert I.neg_mem hi using 1
   ring
 · rintro ⟨a,ha⟩
   obtain ⟨x,rfl⟩:=sH a
   rw [azY,Et] at ha
   have hx :x*g∈I ⊔ nq {g} :=
     Up (Ideal.mem_span_singleton.mpr ⟨x,t5 x g⟩)
   simpa using (I ⊔ nq {g}).sub_mem hx (Ideal.mem_sup_left ha)
private theorem bYd {S:Type} [oq S] [lV R S]
  (T:Submonoid R) [IsLocalization T S] (I:cy R) (g:R) :
  (I.colon {g}).map (c9 R S)=(I.map (c9 R S)).colon {c9 R S g} := by
 ext z
 obtain ⟨a,s,rfl⟩:=IsLocalization.exists_mk'_eq T z
 rw [Mw ,v9,
  t5 _ (c9 R S g),IsLocalization.mul_mk'_eq_mk'_of_mul,
  zNj,zNj]
 simp only [Mw ,v9,yl,t5 g]
end Quotients
theorem be6 (I P:n8) (hp:P.IsPrime) (g:pQ) :
   oA I P hp =
     oA (I.colon {g}) P hp+oA (I ⊔ nq {g}) P hp:= by
 have :=hp
 let L:=qG P
 let r :=c9 pQ L
 let J:=I.map r
 let a :=r g
 have h:=Module.length_eq_add_of_exact (Vp J a)
   (Submodule.factor (zg:J≤J ⊔ nq {a}))
   (aPy J a) (Submodule.factor_surjective zg)
   (a7c J a)
 change t3 L (L ⧸ I.map r) =
   t3 L (L ⧸ (I.colon {g}).map r)+Module.length L (L ⧸ (I ⊔ nq {g}).map r)
 rw [bYd P.primeCompl,Ideal.map_sup,KI,Vs]
 exact h
theorem aIs {I P:n8} (hp:P.IsPrime) (h : ¬ I≤P) :
   oA I P hp=0:= by
 have :=hp
 let L:=qG P
 have htop:I.map (c9 pQ L) = ⊤ := by
   by_contra ht
   exact h (Set.disjoint_compl_left_iff_subset.mp
     ((WW P.primeCompl L I).mp ht))
 change t3 L (L ⧸ I.map (c9 pQ L))=0
 simp [htop,Module.length_eq_zero]
theorem brM (P:n8) (hp:P.IsPrime) :oA P P hp=1 := by
 have :=hp
 let L:=qG P
 change t3 L (L ⧸ P.map (c9 pQ L))=1
 rw [Localization.AtPrime.map_eq_maximalIdeal]
 have h:IsSimpleModule L (L ⧸ zrY L) :=
  isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal L).1
 exact Module.length_eq_one _ _
theorem b2k (I:n8) (hI:I ≠ ⊤) :
  ∃ g:pQ,g∉I∧(I.colon {g}).IsPrime := by
 let _:=Ideal.Quotient.nontrivial_iff.mpr hI
 obtain ⟨A,hA,_⟩:=exists_le_isAssociatedPrime_of_isNoetherianRing
  pQ (1 :pQ ⧸ I) one_ne_zero
 obtain ⟨hp,x,hx⟩:=isAssociatedPrime_iff.mp hA
 obtain ⟨g,rfl⟩:=sH x
 have heq :A=I.colon {g} := by
  ext a
  rw [hx,Mw ,Mw ,Submodule.mem_bot]
  change lI I a* lI I g=0↔a*g∈I
  rw [← n5]
  exact vw
 rw [heq] at hp
 refine ⟨g,fun hg=>hp.ne_top ?_,hp⟩
 simpa only [Submodule.colon_eq_top_iff_subset,Set.singleton_subset_iff,SetLike.mem_coe] using hg
end
end WI
end
section
namespace MJ
noncomputable section
open MvPolynomial dN rW
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 :Prop :=
  ∀ (k σ:Type) [lz k] [oy σ] (A:cy (aU σ k)),
    A.IsPrime→dimension A=2 →
    (∀ P,(lW A).IsMinimalPrime P →
      dimension P=2∧P.IsHomogeneous (pG σ k)) ∧
    qz A = ∑ P∈(lW A).minimalPrimesFinset,
      (ado (lW A) P:ℚ)*qz P
def c2 :Prop :=
  ∀ A:kT,A.IsPrime →
    qy (gN A)=qy A ∧
    ∀ P,(lW (gN A)).IsMinimalPrime P →
      ∃ R,(lW A).IsMinimalPrime R∧gN R=P
def c4 :Prop :=
  ∀ (k σ τ:Type) [lz k] [oy σ] [oy τ]
    (φ:aU τ k →ₐ[k] aU σ k),agH φ →
    ∀ A:cy (aU σ k),A.IsPrime→dimension A=2→aRK φ A →
      dimension (A.comap φ)=2 ∧
      ∀ P,(lW A).IsMinimalPrime P→dimension (P.comap φ)=2 →
        (lW (A.comap φ)).IsMinimalPrime (P.comap φ)
def c5:Prop := by
  classical
  exact ∀ (k σ τ:Type) [lz k] [oy σ] [oy τ]
    (φ:aU τ k →ₐ[k] aU σ k),agH φ →
    ∀ A:cy (aU σ k),A.IsPrime→aRK φ A →
    ∀ Q:cy (aU τ k),(lW (A.comap φ)).IsMinimalPrime Q →
      (∑ P∈(lW A).minimalPrimesFinset.filter (fun P=>P.comap φ= Q),
        ado (lW A) P*QZ φ.toRingHom P) ≤
      ado (lW (A.comap φ)) Q
end
end MJ
end
section
namespace NS
noncomputable section
open rW MvPolynomial
def lW {k σ:Type*} [lz k] (I:cy (aU σ k)) :
    cy (aU σ k) :=
  nq {q | ∃ (p:aU σ k) (n:ℕ),
    p∈I∧p.totalDegree≤n∧q=lJ n p}
def KL {k σ:Type*} [lz k] (I:cy (aU σ k)) (i:σ) :
    cy (aU σ k) :=
  lW I ⊔ nq {mD i - 1}
def bjR {k σ:Type*} [lz k] (I:cy (aU σ k))
    (ℓ:aU σ k) :Prop :=
  ∀ b:σ→k,b∈pL k (lW I)→eval b ℓ=0→b=0
def ahc {k σ:Type*} [lz k] (I:cy (aU σ k))
    (ℓ:aU σ k) :Prop :=
  ∃ N :ℕ,∀ n≥N,∀ z∈oD I (n+1),
    ∃ a∈oD I n,∃ b∈oD I n,
      z=a+Ideal.Quotient.mk I ℓ*b
end
end NS
end
section
namespace YT
noncomputable section
open MvPolynomial NS
open scoped MonomialOrder
variable {k σ:Type*} [lz k]
theorem a2Q {p q:aU σ k} {d:ℕ}
    (hq:q.IsHomogeneous d) (n:ℕ) :
    lJ n (p*q) =
      if d≤n then lJ (n - d) p*q else 0:= by
  classical
  conv_lhs=>rw [← Kp p,KH,oz]
  simp only [Ar ((qm _ _).mul hq)]
  by_cases hd:d≤n
  · rw [u5 hd]
    by_cases hr :n - d∈Eg (p.totalDegree+1)
    · rw [Finset.sum_eq_single_of_mem (n - d) hr]
      · simp [zxt hd]
      · intro b _ hb
        rw [vG (by omega)]
    · have hlt:p.totalDegree<n - d:= by
        rw [Y4] at hr
        omega
      rw [zS _ _ hlt,zero_mul]
      exact J4 fun b hb=>vG (by
        have :=Finset.mem_range.mp hb
        omega)
  · rw [vG hd]
    exact J4 fun b _=>vG (by omega)
theorem a5m (I:cy (aU σ k)) {q:aU σ k}
    (hq:q∈lW I) (n:ℕ) :
    ∃ p∈I,p.totalDegree≤n∧lJ n p=lJ n q:= by
  revert n
  induction hq using zt0 with
  | mem q hq =>
    obtain ⟨p,d,hp,hd,rfl⟩:=hq
    intro n
    by_cases h:n=d
    · subst n
      exact ⟨p,hp,hd,(z7 (qm d p)).symm⟩
    · exact ⟨0,I.zero_mem,by simp,by
        rw [Ar  (qm  d p),vG  h,t7 ]⟩
  | zero=>exact fun _=>⟨0,I.zero_mem,by simp,rfl⟩
  | add q r _ _ hq hr =>
    intro n
    obtain ⟨p,hp,hn,he⟩:=hq n
    obtain ⟨s,hs,hm,hf⟩:=hr n
    exact ⟨p+s,I.add_mem hp hs,(Kh _ _).trans (zd hn hm),by
      rw [qM,qM,he,hf]⟩
  | smul a q _ hq =>
    intro n
    change ∃ p∈I,p.totalDegree≤n∧lJ n p=lJ n (a*q)
    induction a using zNP with
    | monomial e c =>
      rw [t5 ,a2Q (HZ c rfl)]
      split_ifs with h
      · obtain ⟨p,hp,hn,he⟩:=hq (n-e.degree)
        refine ⟨p*wA e c,I.mul_mem_right _ hp,
          (zk _ _).trans ?_,?_⟩
        · have hmono:=(HZ c (rfl :e.degree=e.degree)).totalDegree_le
          omega
        · rw [a2Q (HZ c rfl),u5 h,he]
      · exact ⟨0,I.zero_mem,by simp,t7 _⟩
    | add a b ha hb =>
      obtain ⟨p,hp,hn,he⟩:=ha
      obtain ⟨s,hs,hm,hf⟩:=hb
      exact ⟨p+s,I.add_mem hp hs,(Kh _ _).trans (zd hn hm),by
        rw [add_mul,qM,qM,he,hf]⟩
theorem cDo (I:cy (aU σ k)) {q:aU σ k}
  (hq:q∈lW I) (n:ℕ) :lJ n q∈lW I:= by
 obtain ⟨p,hp,hd,he⟩:=a5m I hq n
 exact Aa ⟨p,n,hp,hd,he.symm⟩
private theorem b7o [G8 σ] [In σ]
    {p:aU σ k} (hp:p≠0) :
    (lJ p.totalDegree p)≠0 ∧
      MonomialOrder.degLex.degree (lJ p.totalDegree p) =
        MonomialOrder.degLex.degree p:= by
  let m:=MonomialOrder.degLex (σ:=σ)
  have hmem:=m.degree_mem_support hp
  have htop:m.degree p∈(lJ p.totalDegree p).support := by
    rw [support_homogeneousComponent,zO0]
    exact ⟨hmem,degree_degLexDegree⟩
  have hne : (lJ p.totalDegree p)≠0:= by
    intro h
    simp [h] at htop
  refine ⟨hne,m.toSyn.injective (vi ?_ (m.le_degree htop))⟩
  apply m.le_degree
  have h:=m.degree_mem_support hne
  rw [support_homogeneousComponent,zO0] at h
  exact h.1
theorem bqR [G8 σ] [In σ] [oy σ]
    (I:cy (aU σ k)) :
    qy (lW I)=qy I:= by
  have he :MonomialOrder.degLex.standardExponents (lW I) =
      MonomialOrder.degLex.standardExponents I:= by
    ext e
    constructor
    · intro h p hp hp₀ hle
      obtain ⟨hq,hd⟩:=b7o hp₀
      exact h _ (Aa ⟨p,p.totalDegree,hp,zc,rfl⟩) hq (hd.symm ▸ hle)
    · intro h q hq hq₀ hle
      obtain ⟨p,hp,hn,htop⟩:=a5m I hq q.totalDegree
      obtain ⟨hne,hd⟩:=b7o hq₀
      have heq :p.totalDegree=q.totalDegree := by
        by_contra h
        rw [zS _ _ (RJ hn h)] at htop
        exact hne htop.symm
      have hp₀:p≠0:= fun h=>hne (by simpa [h] using htop.symm)
      have hd' := (b7o hp₀).2
      rw [heq,htop,hd] at hd'
      exact h p hp hp₀ (hd'.symm ▸ hle)
  obtain ⟨N,hN⟩:=FR I
  symm
  apply LR (N₀:=N)
  intro n hn
  rw [zU2,he,← zU2]
  exact hN n hn
end
end YT
end
section
namespace YT
noncomputable section
open MvPolynomial NS
variable {k K σ:Type*} [lz k] [lz K] [lV k K]
private theorem ew5 (I:cy (aU σ k)) (i:σ) :
    JW (lI (lW I) (mD i - 1)) := by
  rw [isLeftRegular_iff_right_eq_zero_of_mul]
  intro z hz
  obtain ⟨p,rfl⟩:=sH z
  rw [← n5 ,vw] at hz
  have h (n:ℕ) :lJ n p∈lW I:= by
    induction n with
    | zero =>
      have h₀:=cDo I hz 0
      rw [sub_mul,uz ,sS ,t5 (mD i),
        a2Q (G0 k i),vG (by omega),zero_sub] at h₀
      exact neg_mem_iff.mp h₀
    | succ n ih =>
      have hn:=cDo I hz (n+1)
      rw [sub_mul,uz ,sS ,t5 (mD i),
        a2Q (G0 k i),u5 (by omega),
        Wm] at hn
      exact (Submodule.sub_mem_iff_right (lW I) (UY _ _ ih)).mp hn
  rw [vw ,← Kp p]
  exact (lW I).sum_mem fun n _=>h n
theorem bmo [oy σ] [G8 σ] [In σ]
  (I:cy (aU σ k)) (hI: (qy I).natDegree=1) (i:σ) :
  (qy (KL I i)).natDegree=0:= by
 have hdeg: (mD i - 1 :aU σ k).totalDegree≤1 :=
  (Ea _ _).trans (zd (totalDegree_X i).le (by simp))
 have h:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
  (ew5 I i) hdeg).1
 rw [bqR I,hI] at h
 exact Nat.eq_zero_of_le_zero h
private theorem dYA {p:aU σ k} {n:ℕ} (h:p.totalDegree≤n+1) :
   (p - lJ (n+1) p).totalDegree≤n:= by
 refine C4 fun d hd => ?_
 change d.degree≤n
 rw [MvPolynomial.mem_support_iff,coeff_sub,IU] at hd
 by_contra! hnd
 have hs :n+1≤d.degree :=Vl hnd
 rcases eq_or_lt_of_le hs with he | hlt
 · simp [← he] at hd
 · have hp:=coeff_eq_zero_of_totalDegree_lt (PD h hlt)
   simp [hp] at hd
theorem bPG [oy σ] [qJ K] (I:cy (aU σ k))
    {l:aU σ k} (hl:l.IsHomogeneous 1)
    (hfree : ∀ x :σ→K,x∈pL K (lW I)→qU x l=0→x=0) :
    ahc I l:= by
  let J:=lW I ⊔ nq {l}
  have hrad:idealOfVars σ k≤J.radical:= by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rw [← TH (K:=K)]
    intro x hx
    rw [xu,hfree x (zeroLocus_anti_mono (zg:lW I≤J) hx)
      (hx l (Up (NX l)))]
    rfl
  obtain ⟨N,hN⟩:=Ideal.exists_pow_le_of_le_radical_of_fg hrad (idealOfVars_fg σ k)
  refine ⟨N,fun n hn z hz => ?_⟩
  obtain ⟨p,hp,rfl⟩:=mem_quotientDegreeLE.mp hz
  have hm:lJ (n+1) p∈J:= by
    apply hN
    apply (mem_pow_idealOfVars_iff N _).2
    intro e he
    have heq :e.degree=n+1 := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp he) ((qm (n+1) p).coeff_eq_zero hne)
    omega
  obtain ⟨q,hq,r,hr,he⟩:=Submodule.mem_sup.mp hm
  obtain ⟨s,rfl⟩:=Ideal.mem_span_singleton'.mp hr
  obtain ⟨u,hu,hdu,huc⟩:=a5m I hq (n+1)
  have hc:lJ (n+1) (p - u-l*lJ n s)=0:= by
    have ht:=oK (lJ (n+1)) he
    rw [z7 (qm _ _),
      qM,a2Q hl,u5 (by omega),Wm] at ht
    rw [sS ,sS ,huc,← ht,add_sub_cancel_left,t5 l,
      z7 ((qm _ _).mul hl),sub_self]
  let a :=p - u-l*lJ n s
  have ha :a.totalDegree≤n+1 :=
    (Ea _ _).trans (zd ((Ea _ _).trans (zd hp hdu))
      ((zk _ _).trans (by
        have hs :=(qm n s).totalDegree_le
        have hld:=hl.totalDegree_le
        omega)))
  have ha' : a.totalDegree≤n:= by simpa [a,hc] using dYA ha
  refine ⟨lI I a,t8 ha',
    lI I (lJ n s),
    t8 ((qm _ _).totalDegree_le),?_⟩
  rw [← n5 ,← qM]
  dsimp only [a]
  rw [sub_add_cancel,sS ,Ideal.Quotient.eq_zero_iff_mem.mpr hu,sub_zero]
end
end YT
end
section
namespace E7
noncomputable section
open aR dN rW MvPolynomial
open scoped Polynomial WithZero
variable (k L:Type) [lz k] [lz L] [lV k L]
def CurveField:Prop :=
 ∃ t:L,pU k t∧oZ (nI k {t}) L
structure CurvePlace where
 value :xL L ℤᵐ⁰
 normalized:v8 value
 on_constants : ∀ c:k,c≠0→value (c9 k L c)=1
variable {L} in
def poleOrder (v :xL L ℤᵐ⁰) (x :L) :ℕ :=
 (WithZero.log (v x)).toNat
variable {L} in
def KB (v :xL L ℤᵐ⁰) (x :L) :ℕ :=
 (-WithZero.log (v x)).toNat
variable {L} in
def Tq {σ:Type} [p7 σ] (v :xL L ℤᵐ⁰) (u:σ→L) :ℕ :=
 Finset.univ.sup (fun i=>poleOrder v (u i))
def Gb {σ:Type} [p7 σ] (u:σ→L) :ℕ :=
 ∑ᶠ v :CurvePlace k L,Tq v.value u
def axV:Prop :=
  ∀ x :L,
    (fun v :CurvePlace k L=>poleOrder v.value x).HasFiniteSupport ∧
    (fun v :CurvePlace k L=>KB v.value x).HasFiniteSupport ∧
    (∑ᶠ v :CurvePlace k L,poleOrder v.value x) =
      (∑ᶠ v :CurvePlace k L,KB v.value x) ∧
    (pU k x →
      (∑ᶠ v :CurvePlace k L,poleOrder v.value x) =
        oj (nI k {x}) L)
variable {L} in
def wL {σ:Type} (u:σ→L) :aU σ k →+* L[X] :=
  vH (Polynomial.C.comp (c9 k L))
    (fun i=>p6 (u i)*ov)
variable {L} in
def SQ {σ:Type} (u:σ→L) :cy (aU σ k) :=
 sI (wL k u)
variable {L} in
def F8 {σ:Type} (u:σ→L) (i₀:σ) (i:σ) :L:=u i/u i₀
variable {L} in
def YC {σ:Type} (u:σ→L) (i₀:σ) :Cy k L :=
 nI k (vh (F8 u i₀))
variable {L} in
def OX {F:Type} [lz F] {N :ℕ} (j:F →+* L) (f :F[X])
    (i:Fin N) :L:=j (f.coeff i.val)
variable {L} in
def avg {F:Type} [lz F] {n:ℕ} (j:F →+* L) (a :L) (f :F[X])
    (i:Fin n) :L:=(wR i.val f).eval₂ j a
structure KD (R:kT) where
 Old:Type
 Fresh:Type
 [oldField:lz Old]
 [freshField:lz Fresh]
 [oldAlgebra :lV ao Old]
 [freshAlgebra :lV ox Fresh]
 oldCurve :CurveField ao Old
 aDk :CurveField ox Fresh
 Fl:Old →+* Fresh
 constants :Fl.comp (c9 ao Old) =
   (c9 ox Fresh).comp ni
 independent:oY
   (vj Fl (c9 ox Fresh rI))
 polynomial:Old[X]
 monic:polynomial.Monic
 degree_le :polynomial.natDegree≤133671
 equation :gN R =
   SQ ox (OX (N :=bf) Fl polynomial)
 generates :nI ox
   (vh (OX (N :=bf) Fl polynomial)) = ⊤
 nonconstant : ∃ i:Fin bf,
   pU ox (OX Fl polynomial i)
attribute [instance] KD.oldField KD.freshField
 KD.oldAlgebra KD.freshAlgebra
variable {L} in
def KD.center {R:kT} (D:KD R) :D.Fresh :=
 c9 ox D.Fresh rI
variable {L} in
def KD.coefficients {R:kT} (D:KD R) :
    Fin bf→D.Fresh :=
  OX D.Fl D.polynomial
variable {L} in
def KD.Bo {R:kT} (D:KD R) {n:ℕ} :
    Fin n→D.Fresh :=
  avg D.Fl D.center D.polynomial
variable {L} in
def a97 {F:Type} [lz F] (j:F →+* L) (a :L)
    (v :xL L ℤᵐ⁰) :Prop :=
  (∀ x :F,x≠0→v (j x)=1) ∨
  (∀ g:F[X],v (g.eval₂ j a)=g.support.sup (fun i=>v (j (g.coeff i))))
structure bjs {F:Type} [lz F] (f :F[X]) where
 count:ℕ
 factor :Fin count→F[X]
 multiplicity :Fin count→ℕ
 monic : ∀ i,(factor i).Monic
 separable : ∀ i,(factor i).Separable
 coprime : ∀ i j,i≠j→ G1 (factor i) (factor j)
 positive : ∀ i,0< multiplicity i
 le_degree : ∀ i,multiplicity i≤f.natDegree
 first_scalar : ∀ i,(multiplicity i:F)≠0
 second_scalar : ∀ i,2≤ multiplicity i→((multiplicity i).choose 2 :F)≠0
 product_eq :f = ∏ i,factor i^multiplicity i
end
end E7
end
section
namespace E7
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped Polynomial
private theorem bCm {F:Type} [lz F] {p n:ℕ} [CharP F p]
  (hpos :0<n) (hlt:n<p) : (n:F)≠0:= by
 intro h
 exact (Te hlt) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff F p n).mp h))
private theorem gpC {F:Type} [lz F] {p:ℕ} [CharP F p]
  {q:F[X]} (hirr :N0 q) (hdeg:q.natDegree<p) :q.Separable := by
 apply (Polynomial.separable_iff_derivative_ne_zero hirr).mpr
 have hstep:q.natDegree - 1+1=q.natDegree := by have :=hirr.natDegree_pos; omega
 intro hz
 have hc:=oK (fun x :F[X]=>x.coeff (q.natDegree - 1)) hz
 rw [coeff_derivative,← Nat.cast_succ,hstep,coeff_natDegree,Bf] at hc
 apply Pc (leadingCoeff_ne_zero.mpr hirr.ne_zero)
  (bCm hirr.natDegree_pos hdeg)
 simpa only [Nat.succ_eq_add_one,hstep] using hc
def bFT {F:Type} [lz F] {p:ℕ} [CharP F p] {f :F[X]}
    (hf :f.Monic) (hdeg:f.natDegree<p) (htwo:2<p) :bjs f := by
  classical
  let S:=(Av f).toFinset
  let e :=(NW S).symm
  let q:= fun i=>(e i).val
  let m:= fun i=>(Av f).count (q i)
  have hmem (i:Fin (zm S)) :q i∈Av f :=
    Multiset.mem_toFinset.mp (e i).property
  have hdata (i:Fin (zm S)) :
      N0 (q i)∧(q i).Monic∧q i∣f :=
    (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp (hmem i)
  have hprod: (∏ i,q i^m i)=f := calc
    _ = ∏ x :S,x.val^(Av f).count x.val :=
      Fintype.prod_equiv e _ _ (fun _=>rfl)
    _=(Av f).prod:= by
      exact (Finset.prod_coe_sort S (fun x=>x^(Av f).count x)).trans
        (Finset.prod_multiset_count _).symm
    _=f := by
      simpa only [hf.leadingCoeff,Polynomial.C_1,uz]
        using Polynomial.leadingCoeff_mul_prod_normalizedFactors f
  have hsum:f.natDegree = ∑ i,m i*(q i).natDegree := by
    rw [← hprod,Polynomial.natDegree_prod_of_monic zi (fun i=>q i^m i)
      (fun i _=>(hdata i).2.1.pow _)]
    exact t6 rfl fun i _=>(hdata i).2.1.natDegree_pow _
  have hm_pos (i:Fin (zm S)) :0< m i:=Multiset.count_pos.mpr (hmem i)
  have hm_le (i:Fin (zm S)) :m i≤f.natDegree := calc
    m i=m i*1 :=(Nat.mul_one _).symm
    _≤ m i*(q i).natDegree :=Nat.mul_le_mul_left _ (hdata i).1.natDegree_pos
    _≤f.natDegree := by
      rw [hsum]
      exact zfK (f := fun j=>m j*(q j).natDegree)
        (fun _ _=>Nat.zero_le _) (uW i)
  have hm_cast (i:Fin (zm S)) : (m i:F)≠0 :=
    bCm (hm_pos i) ((hm_le i).trans_lt hdeg)
  refine ⟨_,q,m,fun i=>(hdata i).2.1,?_,?_,hm_pos,hm_le,hm_cast,?_,hprod.symm⟩
  · intro i
    exact gpC (hdata i).1
      ((natDegree_le_of_dvd (hdata i).2.2 hf.ne_zero).trans_lt hdeg)
  · intro i j hij
    apply (hdata i).1.coprime_iff_not_dvd.mpr
    intro hdiv
    have heq :=eq_of_monic_of_associated (hdata i).2.1 (hdata j).2.1
      ((hdata i).1.associated_of_dvd (hdata j).1 hdiv)
    exact hij (e.injective (u8 heq))
  · intro i hi
    have :NeZero (2 :F) :=⟨by
      exact_mod_cast (bCm (F:=F) (by decide :0<2) htwo)⟩
    have hm₁: ((m i - 1 :ℕ) :F)≠0 :=
      bCm (by omega) ((Nat.sub_le _ _).trans_lt ((hm_le i).trans_lt hdeg))
    have hm₁' : (m i:F) - 1≠0:= by
      simpa only [Nat.cast_sub (by omega :1≤ m i),Ef] using hm₁
    rw [Nat.cast_choose_two]
    exact div_ne_zero (Pc (hm_cast i) hm₁') (NeZero.ne _)
end
end E7
end
section
namespace E7
noncomputable section
open aR dN rW MJ MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 :Prop :=
  ∀ R:kT,R.IsPrime→(gN R).IsPrime →
    R.IsHomogeneous (pG (Fin bf) ao) →
    dimension R=2→Nonempty (KD R)
def c2 :Prop :=
  ∀ (k L:Type) [lz k] [qJ k] [lz L] [lV k L],
    CurveField k L→axV k L
def c3:Prop :=
  ∀ (k L σ:Type) [lz k] [qJ k] [lz L] [lV k L] [p7 σ],
    CurveField k L→axV k L →
    ∀ (u:σ→L) (i:σ),u i≠0 →
      ((∃ j,pU k (F8 u i j))↔0<Gb k L (F8 u i)) ∧
      (0<Gb k L (F8 u i) →
        dimension (SQ k u)=2 ∧
        (Gb k L (F8 u i) :ℚ) =
          (oj (YC k u i) L:ℚ)*qz (SQ k u))
def c4 :Prop :=
  ∀ (k L σ τ:Type) [lz k] [lz L] [lV k L],
    ∀ (u:σ→L) (i:σ) (v :τ→L) (j:τ)
      (φ:aU τ k →+* aU σ k),
      u i≠0→v j≠0→YC k u i = ⊤ →
      (wL k u).comp φ=wL k v →
      QZ φ (SQ k u)=oj (YC k v j) L
def c5:Prop :=
  ∀ (R:kT) (D:KD R) (v :CurvePlace ox D.Fresh),
    a97 D.Fl D.center v.value
def c6:Prop :=
  ∀ (F L:Type) [lz F] [lz L]
    (j:F →+* L) (a :L) (f :F[X]) (B:bjs f)
    (v :xL L ℤᵐ⁰) (N :ℕ),
    f.natDegree<N→v a=1 →
    oY (vj j a) →
    a97 j a v →
      Tq v (OX (N :=N) j f) =
        ∑ r,B.multiplicity r*poleOrder v ((B.factor r).eval₂ j a) ∧
      Tq v (F8 (avg (n:=3) j a f) 0) =
        ∑ r,min (B.multiplicity r) 2*KB v ((B.factor r).eval₂ j a)
private theorem bqP {k L σ:Type}
  [lz k] [lz L] [lV k L] [p7 σ]
  (h:axV k L) (u:σ→L) :
  (fun v :CurvePlace k L=>Tq v.value u).HasFiniteSupport:= by
 have hf : (⋃ i:σ,yQ (fun v :CurvePlace k L =>
    poleOrder v.value (u i))).Finite :=UZ fun i=>(h (u i)).1
 apply hf.subset
 intro v hv
 simp only [Ob ,Zg] at hv ⊢
 by_contra! hz
 exact hv (Kv _ _ |>.mpr fun i _=>hz i)
private theorem bya {k L σ τ:Type}
  [lz k] [lz L] [lV k L] [p7 σ] [p7 τ]
  (h:axV k L) (u:σ→L) (w:τ→L) (e :σ→τ)
  (he : ∀ i,u i=w (e i)) :
  Gb k L u≤Gb k L w:= by
 apply finsum_le_finsum (bqP h u) (bqP h w)
 intro v
 unfold Tq
 apply C4
 intro i _
 rw [he i]
 exact Gk (s :=zi) (f := fun j=>poleOrder v.value (w j))
  (uW (e i))
private theorem a4c {α σ:Type} [p7 σ] (c:σ→ℕ) (f :σ→α→ℕ)
    (hf : ∀ i,(f i).HasFiniteSupport) :
    (∑ᶠ v,∑ i,c i*f i v) = ∑ i,c i * ∑ᶠ v,f i v := by
  classical
  let s :Set α := ⋃ i,yQ (f i)
  have hs :s.Finite :=UZ hf
  have hi (i:σ) :yQ (f i)⊆(hs.toFinset :Set α) := by
    rw [Set.Finite.coe_toFinset]
    exact Set.subset_iUnion (fun j=>yQ (f j)) i
  have ha :yQ (fun v => ∑ i,c i*f i v)⊆(hs.toFinset :Set α) := by
    intro v hv
    by_contra h
    exact hv (J4 fun i _=> by
      have hz :f i v=0:= by
        by_contra hn
        exact h (hi i hn)
      simp [hz])
  rw [ZK _ ha,Finset.sum_comm]
  apply t6 rfl
  intro i _
  rw [ZK _ (hi i),G6]
private theorem b6Q {F L:Type} [lz F] [lz L]
   (j:F →+* L) (a :L) (f :F[X]) {N :ℕ} (hn:f.natDegree<N) (i:ℕ) :
   (wR i f).eval₂ j a =
     ∑ x :Fin N,((x.val.choose i:L)*a^(x.val - i))*j (f.coeff x.val) := by
 rw [Polynomial.hasseDeriv_apply,f.sum_over_range' (fun _=> by simp) _ hn,
   Polynomial.eval₂_finsetSum,Kl  (fun x =>
     ((x.choose i:L)*a^(x - i))*j (f.coeff x))]
 apply t6 rfl
 intro x _
 simp only [Pv,n5 ,Iw]
 ring
private theorem bDe {k F L:Type} [lz k] [lz F] [lz L] [lV k L]
    (j:F →+* L) (a :k) (f :F[X]) {N n:ℕ} (hdeg:f.natDegree<N) :
    (wL k (OX (N :=N) j f)).comp
      (vH p5 (fun i:Fin n =>
        ∑ r :Fin N,p5 ((r.val.choose i.val :k)*a^(r.val - i.val)) *
          mD r)) =
      wL k (avg (n:=n) j (c9 k L a) f) := by
  let u:Fin N→L:=OX j f
  let v :Fin n→L:=avg j (c9 k L a) f
  apply zh
  · intro c
    simp [wL]
  · intro i
    rw [vZ,xW]
    have he (r :Fin N) :
        (wL k u)
          (p5 ((r.val.choose i.val :k)*a^(r.val - i.val)) *
            mD r) =
          p6 (((r.val.choose i.val :L)*(c9 k L a)^(r.val - i.val)) *
            u r)*Polynomial.X:= by
      simp [wL,yl]
    rw [show (wL k v) (mD i) =
      p6 (v i)*ov from xW _ _ _]
    rw [show v i =
      ∑ r :Fin N,((r.val.choose i.val :L)*(c9 k L a)^(r.val - i.val)) *
        u r from b6Q j _ f hdeg i.val]
    rw [oz ,oz ,KH]
    exact t6 rfl fun r _=>he r
end
end E7
end
section
namespace aFU
open E7
variable (k L:Type) [lz k] [lz L] [lV k L]
abbrev DT (x :L) :=yB k ({x} : Set L)
abbrev DR (x :L) :=Dv (DT k L x) L
def origin (x :L) :cy (DT k L x) :=
 nq {⟨x,G9 k x⟩}
abbrev ax5 (x :L) :=
 {v :CurvePlace k L // KB v.value x≠0}
end aFU
end
section
namespace aFU
noncomputable section
open E7 IntermediateField
open scoped WithZero Polynomial algebraAdjoinAdjoin nonZeroDivisors
def c1 :Prop :=
  ∀ (k L:Type) [lz k] [qJ k] [lz L] [lV k L]
    (x :L),pU k x→ oZ (nI k {x}) L →
      oZ (DT k L x) (DR k L x)
def c2 :Prop :=
  ∀ (k L:Type) [lz k] [lz L] [lV k L] (x :L),
    pU k x→ IT (DR k L x) →
    ze (DR k L x) L →
    ∃ e :ax5 k L x ≃ (origin k L x).primesOver (DR k L x),
      ∀ v,KB v.val.value x=(e v).val.ramificationIdx (DT k L x)
variable {k L:Type} [lz k] [lz L] [lV k L]
private theorem eaZ (h:CurveField k L) {x :L}
   (hx :pU k x) :oZ (nI k {x}) L:= by
 obtain ⟨t,ht,hfin⟩:=h
 have ht' : Vq (nI k {x}) t :=
   isAlgebraic_adjoin_iff.mpr (.adjoin_singleton ht hx
     (isAlgebraic_adjoin_iff.mp (zgs x)))
 let Kxt:=restrictScalars k (nI (nI k {x}) {t})
 let Ktx :=restrictScalars k (nI (nI k {t}) {x})
 let:lV (nI k {x}) Kxt :=
   (nI (nI k {x}) {t}).algebra
 let:Module (nI k {x}) Kxt:=Algebra.toModule
 let:SMul (nI k {x}) Kxt:=Algebra.toSMul
 let:lV (nI k {t}) Ktx :=
   (nI (nI k {t}) {x}).algebra
 let:Module (nI k {t}) Ktx :=Algebra.toModule
 let:SMul (nI k {t}) Ktx :=Algebra.toSMul
 have :oZ (nI k {x}) Kxt :=
   IntermediateField.adjoin.finiteDimensional ht'.isIntegral
 have :oZ Kxt L:= by
   unfold Kxt
   rw [adjoin_simple_comm]
   have :vk (nI k {t}) Ktx L:=isScalarTower_mid' _
   exact .right (nI k {t}) Ktx L
 have :vk (nI k {x}) Kxt L:=isScalarTower_mid' _
 exact zWg Kxt L
theorem bKh {x :L} (hx :pU k x) :
  Hw (DT k L x) :=
 IsPrincipalIdealRing.of_surjective (Kz k x hx).toRingHom
  (Kz k x hx).surjective
private def bJ5 {x :L} (hx :pU k x) :
    (DT k L x ⧸ origin k L x) ≃ₐ[k] k := by
  let e :=Kz k x hx
  refine (Un (nq {ov}) (origin k L x) e ?_).symm.trans ?_
  · rw [KI,Vs]
    unfold origin
    change nq {⟨x,G9 k x⟩} = nq {e ov}
    simp only [e,Polynomial.algEquivOfTranscendental_apply_X]
  · rw [show (nq {ov} : cy k[X]) =
        nq {ov-Polynomial.C (0:k)} by rw [t7,sub_zero]]
    exact Polynomial.quotientSpanXSubCAlgEquiv (0:k)
theorem a6k {x :L} (hx :pU k x) :
  (origin k L x).IsMaximal :=
 Ideal.Quotient.maximal_of_isField _ ((bJ5 hx).toRingEquiv.isField (Field.toIsField k))
private theorem bJK {x :L} (hx :pU k x)
   [oZ (nI k {x}) L]
   [oZ (DT k L x) (DR k L x)] :
   IT (DR k L x) := by
 let A:=DT k L x
 let B:=DR k L x
 let K:=nI k {x}
 have :Hw A:=bKh hx
 have :th B :=
   isNoetherianRing_iff.mpr (isNoetherian_of_tower A (show IsNoetherian A B from u9))
 exact
   { (u9 :th B),
     Ring.DimensionLEOne.of_isIntegral A B,
     integralClosure.isIntegrallyClosedOfFiniteExtension K with }
private theorem gwZ [qJ k] {x :L} (hx :pU k x)
    [oZ (nI k {x}) L]
    [oZ (DT k L x) (DR k L x)] :
    (∑ᶠ P: (origin k L x).primesOver (DR k L x),
      P.val.ramificationIdx (DT k L x)) =
      oj (nI k {x}) L:= by
  classical
  let A:=DT k L x
  let B:=DR k L x
  let K:=nI k {x}
  let p:=origin k L x
  have :Hw A:=bKh hx
  have :IT B:=bJK hx
  have :ze B L:=zij K L
  have :p.IsMaximal:=a6k hx
  have :p.IsPrime :=Ideal.IsMaximal.isPrime u9
  have :zYp A L := .trans_faithfulSMul A K L
  have :zYp A B:=IsIntegralClosure.isTorsionFree A L
  have :Module.Free A B:= by infer_instance
  have hdeg (P:p.primesOver B) :P.val.inertiaDeg A=1 := by
    have :P.val.IsPrime :=P.property.1
    have :P.val.LiesOver p:=P.property.2
    have :P.val.IsMaximal:=Ideal.IsMaximal.of_liesOver_isMaximal P.val p
    have hp:v8 (c9 k (A ⧸ p)) := by
      intro y
      let e :=bJ5 hx
      exact ⟨e y,by rw [← e.symm.commutes,Pk,e.symm_apply_apply]⟩
    have :Rm k (A ⧸ p) :=
      ⟨fun y=> by obtain ⟨z,rfl⟩:=hp y; exact Oc⟩
    let:lz (A ⧸ p) :=Ideal.Quotient.field p
    have :Rm k (B ⧸ P.val) := .trans (A ⧸ p)
    have hsurj:v8 (c9 (A ⧸ p) (B ⧸ P.val)) := by
      intro y
      obtain ⟨z,hz⟩:=(Z0
        (k :=k) (K:=B ⧸ P.val)).surjective y
      exact ⟨c9 k (A ⧸ p) z,(Au _ _ _ _).symm.trans hz⟩
    rw [Ideal.inertiaDeg_eq_of_isMaximal p P.val,Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨zyB _,hsurj⟩
  have hrank :oj A B=oj K L:= by
    have :IsLocalization (Algebra.algebraMapSubmonoid B (GF A)) L :=
      IsIntegralClosure.isLocalization A K L B
    let b:=Module.Basis.localizationLocalization K (GF A) L (Ts A B)
    rw [Module.finrank_eq_card_chooseBasisIndex,zdK b]
  change (∑ᶠ P:p.primesOver B,P.val.ramificationIdx A)=oj K L
  rw [finsum_eq_sum_of_fintype,← hrank,← Ideal.sum_ramification_inertia_eq_finrank p B]
  exact t6 rfl fun P _=> by rw [hdeg,GY]
private theorem dms [qJ k] (h1 :c1) (h2 :c2) (h:CurveField k L)
    {x :L} (hx :pU k x) :
    (fun v :CurvePlace k L=>KB v.value x).HasFiniteSupport ∧
      (∑ᶠ v :CurvePlace k L,KB v.value x) =
        oj (nI k {x}) L:= by
  classical
  have :oZ (nI k {x}) L:=eaZ h hx
  have :oZ (DT k L x) (DR k L x) :=h1 k L x hx u9
  have :IT (DR k L x) :=bJK hx
  have :ze (DR k L x) L :=
    zij (nI k {x}) L
  have : (origin k L x).IsMaximal:=a6k hx
  obtain ⟨e,he⟩:=h2 k L x hx u9 u9
  have :p7 (ax5 k L x) :=Fintype.ofEquiv _ e.symm
  let f := fun v :CurvePlace k L=>KB v.value x
  have hf :oy (yQ f) := by
    change oy (ax5 k L x)
    infer_instance
  refine ⟨Set.finite_coe_iff.mp hf,?_⟩
  change finsum f= _
  calc
    finsum f = ∑ᶠ v :ax5 k L x,f v.val := by
      change finsum f = ∑ᶠ v :yQ f,f v.val
      rw [finsum_set_coe_eq_finsum_mem (f :=f),finsum_mem_support]
    _ = ∑ᶠ P: (origin k L x).primesOver (DR k L x),
          P.val.ramificationIdx (DT k L x) :=
      finsum_eq_of_bijective e e.bijective he
    _ = _:=gwZ hx
private theorem adjoin_inv (x :L) :
   nI k ({x⁻¹} : Set L)=nI k {x} := by
 apply vi <;> apply IntermediateField.adjoin_le_iff.mpr
 · exact Set.singleton_subset_iff.mpr (IntermediateField.inv_mem _ (TI k x))
 · apply Set.singleton_subset_iff.mpr
   change x∈nI k ({x⁻¹} : Set L)
   simpa only [inv_inv] using
    (nI k ({x⁻¹} : Set L)).inv_mem (TI k x⁻¹)
private theorem gM9 (v :xL L ℤᵐ⁰) (x :L) :
  KB v x⁻¹=poleOrder v x := by
 simp [KB,poleOrder,map_inv₀,WithZero.log_inv]
theorem of_children (h1 :c1) (h2 :c2) :E7.c2 := by
 intro k L _ _ _ _ h x
 by_cases hx :pU k x
 · have hxi:pU k x⁻¹:= fun hi=>hx (IsAlgebraic.inv_iff.mp hi)
   obtain ⟨hz,hsz⟩:=dms h1 h2 h hx
   obtain ⟨hp,hsp⟩:=dms h1 h2 h hxi
   simp_rw [gM9] at hp hsp
   rw [adjoin_inv] at hsp
   exact ⟨hp,hz,hsp.trans hsz.symm,fun _=>hsp⟩
 · have ha :Vq k x :=not_not.mp hx
   have :C5 k (nI k {x}) :=
    Xg ha.isIntegral
   have :Rm k (nI k {x}) :=u9
   obtain ⟨c,hc⟩:=(Z0
    (k :=k) (K:=nI k {x})).surjective (AdjoinSimple.gen k x)
   have hcx :c9 k L c=x :=
    oK (c9 (nI k {x}) L) hc
   have hzero (v :CurvePlace k L) :v.value x=0∨v.value x=1 := by
    rw [← hcx]
    by_cases h0:c=0
    · simp [h0]
    · exact Or.inr (v.on_constants c h0)
   have hp: (fun v :CurvePlace k L=>poleOrder v.value x)=0:= by
    funext v
    rcases hzero v with hv | hv <;> simp [poleOrder,hv]
   have hz : (fun v :CurvePlace k L=>KB v.value x)=0:= by
    funext v
    rcases hzero v with hv | hv <;> simp [KB,hv]
   simp [hp,hz,Function.HasFiniteSupport,hx]
end
end aFU
end
section
namespace aeD
noncomputable section
open MvPolynomial
variable {k σ:Type*} [lz k]
def anT (A:cy (aU σ k)) :
    aU (yJ σ) k →ₐ[k] xm (aU σ k ⧸ A) :=
  qU fun i=>p6 (lI A (i.elim 1 mD))*ov
def JA (A:cy (aU σ k)) :cy (aU (yJ σ) k) :=
 sI (anT A).toRingHom
def Zq:aU (yJ σ) k →ₐ[k] aU σ k :=
 qU fun i=>i.elim 0 mD
end
end aeD
end
section
namespace aeD
noncomputable section
open MvPolynomial rW MJ
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type*} [lz k]
theorem dLT (A:cy (aU σ k)) (hA:A.IsPrime) :
  (JA A).IsPrime := by
 let _:A.IsPrime :=hA
 exact SU (anT A).toRingHom
theorem eFx (A:cy (aU σ k)) (hA:A.IsPrime) :
  mD none∉JA A:= by
 let _:A.IsPrime :=hA
 change anT A (mD none)≠0
 simp [anT]
theorem bcy (A:cy (aU σ k))
    (f :aU (yJ σ) k) (n:ℕ) :
    (anT A f).coeff n =
      lI A ((qU fun i:yJ σ=>i.elim 1 mD)
        (lJ n f)) := by
  let e :aU (yJ σ) k →ₐ[k] aU σ k :=
    qU fun i=>i.elim 1 mD
  change (anT A f).coeff n=lI A (e (lJ n f))
  induction f using zNP with
  | add f g hf hg =>
    simp [qM,Xo ,hf,hg]
  | monomial d r =>
    have hm:anT A (wA d r) =
        p6 (lI A (e (wA d r))) *
          ov ^d.degree := by
      classical
      simp only [anT,e,aeval_monomial,zpj,
        Finsupp.prod,zqc]
      simp only [Ideal.Quotient.mk_algebraMap,n5 ,map_prod,t9]
      have hprod :
          (∏ i∈d.support,
            (p6 (lI A (i.elim 1 mD))*ov)^d i) =
          ∏ i∈d.support,
            p6 (lI A (i.elim 1 mD))^d i *
              ov ^d i:= by
        exact Finset.prod_congr rfl fun i _ =>
          Du (p6 (lI A (i.elim 1 mD)))
            (ov :xm (aU σ k ⧸ A)) (d i)
      rw [hprod,GB,Gi]
      ac_rfl
    rw [hm,zds,
      Ar (HZ r rfl)]
    split_ifs <;> simp_all
theorem ayA (f :aU σ k) (n:ℕ) :
  (z9 (pG σ k) f n:aU σ k) =
    homogeneousComponent n f := by
 simpa only [DirectSum.Decomposition.decompose'_eq] using Sd f n
theorem cFL (A:cy (aU σ k)) :
   (JA A).IsHomogeneous (pG (yJ σ) k) := by
 intro n f hf
 rw [ayA]
 change anT A f=0 at hf
 change anT A (lJ n f)=0
 ext m
 rw [bcy,Ar (Il n f)]
 split_ifs with hmn
 · subst m
   rw [← bcy,hf,Bf]
 · simp
private theorem cBp (f :aU σ k) :
  Zq (rename some f)=f := by
 have h: (Zq (k :=k) (σ:=σ)).comp (rename some)=AlgHom.id k _:= by
  ext i
  simp [Zq]
 exact Lf h f
theorem cBq :
  v8 (Zq (k :=k) (σ:=σ)) :=
 fun f=>⟨rename some f,cBp f⟩
theorem bUp (f :aU (yJ σ) k) :
  Zq f=(optionEquivLeft k σ f).coeff 0:= by
 let e :xm (aU σ k) →ₐ[k] aU σ k :=
  (EP 0).restrictScalars k
 have h: (Zq (k :=k) (σ:=σ))=e.comp (optionEquivLeft k σ).toAlgHom:= by
  ext i
  cases i <;> simp [e,Zq,optionEquivLeft_X_none,optionEquivLeft_X_some]
 rw [h]
 change EP (0:aU σ k) (optionEquivLeft k σ f)= _
 rw [Polynomial.coe_aeval_eq_eval,Polynomial.coeff_zero_eq_eval_zero]
theorem emT [oy σ] (I:cy (aU σ k)) (n:ℕ) :
    vl (I.comap (Zq (k :=k) (σ:=σ))) n =
      affineHilbertFunction I n:= by
  let q:=Mz I (Zq (k :=k) (σ:=σ)) zc
  let g:oD (I.comap (Zq (k :=k) (σ:=σ))) n →ₗ[k]
      quotientDegreeLE I n :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun x=> by
      obtain ⟨f,hf,hfx⟩:=mem_quotientDegreeLE.mp x.property
      change q x.val∈_
      rw [← hfx]
      refine t8 (p:=Zq f) ?_
      rw [bUp]
      exact (totalDegree_coeff_optionEquivLeft_le k σ f 0).trans hf
  have he :VO g:= by
    constructor
    · intro x y hxy
      exact u8 (zR (oK Nj hxy))
    · intro y
      obtain ⟨f,hf,hfy⟩:=mem_quotientDegreeLE.mp y.property
      refine ⟨⟨lI _ (rename some f),
        t8 ((totalDegree_rename_le some f).trans hf)⟩,
        u8 ?_⟩
      change lI I (Zq (rename some f))=y.val
      rw [cBp,hfy]
  exact (Yc g he).finrank_eq
theorem cUJ [oy σ] (I:cy (aU σ k)) :
  qy (I.comap (Zq (k :=k) (σ:=σ))) =
    affineHilbertPolynomial I:= by
 symm
 obtain ⟨N,hN⟩:=FR I
 exact LR (N₀:=N)
  (fun n hn=> by rw [hN n hn,emT])
theorem dzO (A:cy (aU σ k)) :
  (lW A).IsHomogeneous (pG σ k) := by
 apply zqZ
 rintro _ ⟨f,_,rfl⟩
 exact ⟨f.totalDegree,Il _ _⟩
theorem eAp {I P:cy (aU σ k)}
  (hI:I.IsHomogeneous (pG σ k)) (hP:I.IsMinimalPrime P) :
  P.IsHomogeneous (pG σ k) := by
 let Q:=(P.homogeneousCore (pG σ k)).toIdeal
 have hQP:Q≤P:=Ideal.toIdeal_homogeneousCore_le _ _
 have hIQ:I≤Q :=
  (Ideal.homogeneousCore.gc (𝒜:=homogeneousSubmodule σ k) ⟨I,hI⟩ P).mp hP.le
 have he :Q=P:=vi hQP (hP.2 ⟨hP.isPrime.homogeneousCore,hIQ⟩ hQP)
 exact he ▸ (P.homogeneousCore (pG σ k)).isHomogeneous
end
end aeD
end
section
namespace agN
noncomputable section
open MJ E7 MvPolynomial
variable {k L σ:Type} [lz k] [lz L] [lV k L] [p7 σ]
def O7 (a :σ→k) (r :σ→L) :L :=
 ∑ j,a j•r j
def ahO (i:σ) (a :σ→k) :
    aU (Fin 2) k →ₐ[k] aU σ k :=
  qU ![mD i,∑ j,p5 (a j)*mD j]
def cxg (r :σ→L) (z :L) :Prop :=
 (∀ j,x7 (yB k {z}) (r j)) ∧
 (∀ j,x7 (yB k {z⁻¹}) (r j/z))
def aWb (P:cy (aU σ k))
    (φ:aU (Fin 2) k →ₐ[k] aU σ k) :
    (aU (Fin 2) k ⧸ P.comap φ.toRingHom) →ₐ[k] (aU σ k ⧸ P) :=
  Mz P φ zc
theorem bTZ (u:σ→L) (i:σ) (a :σ→k) :
  nI k {O7 a (F8 u i)} ≤ YC k u i:= by
 apply zmT.2
 intro z hz
 rw [Set.mem_singleton_iff.mp hz]
 exact (YC k u i).sum_mem fun j _ =>
  (YC k u i).smul_mem (LQ k (FU j))
def ccY (u:σ→L) (i:σ) (a :σ→k) :ℕ :=
  letI:=(KA (bTZ u i a)).toAlgebra
  oj (nI k {O7 a (F8 u i)})
    (YC k u i)
end
end agN
end
section
namespace agN
noncomputable section
open E7
open scoped WithZero
variable {k L σ:Type} [lz k] [lz L] [lV k L] [p7 σ]
theorem bGE (h:CurveField k L) {z :L} (hz :pU k z) :
   oZ (nI k {z}) L:= by
 obtain ⟨t,ht,hfin⟩:=h
 let E :=nI k {t}
 let e :nX k ≃ₐ[k] E :=RatFunc.algEquivOfTranscendental t ht
 let g:nX k →ₐ[k] L:=E.val.comp e.toAlgHom
 let:lV (nX k) L:=g.toRingHom.toAlgebra
 have :vk k (nX k) L:=G2
   fun x=>(g.commutes x).symm
 have :oZ E L:=hfin
 have :FunctionField k L :=
   ((Module.finBasis E L).mapCoeffs e.symm fun c x=> by
     rw [xI,xI]
     change (e (e.symm c) :L)*x=(c:L)*x
     rw [e.apply_symm_apply]).finiteDimensional_of_finite
 exact FunctionField.finiteDimensional_of_adjoin_transcendental hz
theorem b27 (h:axV k L) (r :σ→L) :
  (fun v :CurvePlace k L=>Tq v.value r).HasFiniteSupport:= by
 have hf : (⋃ j:σ,yQ (fun v :CurvePlace k L =>
    poleOrder v.value (r j))).Finite :=UZ fun j=>(h (r j)).1
 apply hf.subset
 intro v hv
 simp only [Ob ,Zg] at hv ⊢
 by_contra! hz
 exact hv (Kv _ _ |>.mpr fun j _=>hz j)
theorem a6F (v :xL L ℤᵐ⁰) (x :L) :
   poleOrder v x=0↔v x≤1 := by
 by_cases hx :x=0
 · simp [hx,poleOrder]
 have hv :=(v.ne_zero_iff).2 hx
 rw [poleOrder,Int.toNat_eq_zero]
 simpa only [WithZero.exp_zero] using (WithZero.log_le_iff_le_exp (a :=0) hv)
private theorem c4x (v :xL L ℤᵐ⁰) {x y :L} (h:v x≤v y) :
   poleOrder v x≤poleOrder v y := by
 by_cases hx :x=0
 · simp [poleOrder,hx]
 have hvx :=(v.ne_zero_iff).2 hx
 have hvy :v y≠0:=ne_of_gt ((zero_lt_iff.mpr hvx).trans_le h)
 exact Int.toNat_le_toNat ((WithZero.log_le_log hvx hvy).2 h)
private theorem c4v (v :CurvePlace k L) (c:k) :
   poleOrder v.value (c9 k L c)=0:= by
 apply (a6F _ _).2
 by_cases hc:c=0
 · simp [hc]
 · exact (v.on_constants c hc).le
private theorem cNx [qJ k] {x :L} (hx : ¬ pU k x) :
  ∃ c:k,c9 k L c=x := by
 have halg:Vq k x :=not_not.mp hx
 have :=Xg halg.isIntegral
 have he :=IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
  (nI k {x})
 exact IntermediateField.mem_bot.mp (he ▸ TI k x)
theorem gDD [qJ k] {z :L}
  (hp:0 < ∑ᶠ v :CurvePlace k L,poleOrder v.value z) :pU k z := by
 by_contra hc
 obtain ⟨c,rfl⟩:=cNx hc
 simp [c4v] at hp
theorem emC [qJ k] (hf :CurveField k L) (h:axV k L)
    (r :σ→L) : (∃ j,pU k (r j))↔0<Gb k L r := by
  constructor
  · rintro ⟨j,hj⟩
    have :=bGE hf hj
    have hle : (∑ᶠ v :CurvePlace k L,poleOrder v.value (r j))≤Gb k L r :=
      finsum_le_finsum (h (r j)).1 (b27 h r) fun v =>
        Gk (s :=zi) (f := fun l=>poleOrder v.value (r l))
          (uW j)
    rw [(h (r j)).2.2.2 hj] at hle
    exact (zRt (R:=nI k {r j}) (M:=L)).trans_le hle
  · intro hp
    by_contra! hn
    have hzero (v :CurvePlace k L) :Tq v.value r=0:= by
      apply (Kv _ _).2
      intro j _
      obtain ⟨c,hc⟩:=cNx (hn j)
      rw [← hc]
      exact c4v v c
    simp [Gb,hzero] at hp
private def maxValue (v :CurvePlace k L) (r :σ→L) :ℤᵐ⁰ :=
 max 1 (Finset.univ.sup fun j=>v.value (r j))
private theorem cu9 (v :CurvePlace k L) (r :σ→L) (j:σ) :
   v.value (r j)≤ maxValue v r :=
 (Gk (s :=zi) (f := fun j=>v.value (r j))
   (uW j)).trans (UP _ _)
private theorem cvc (v :CurvePlace k L) (c:k) (x :L) :
   v.value (c•x)≤v.value x := by
 by_cases hc:c=0
 · simp [hc]
 rw [xI,n5 ,v.on_constants c hc,uz]
private theorem ew3 (v :CurvePlace k L) (r :σ→L) (a :σ→k) :
  v.value (O7 a r)≤ maxValue v r := by
 apply v.value.map_sum_le
 intro j _
 exact (cvc v (a j) (r j)).trans (cu9 v r j)
private def bca (v :CurvePlace k L) (r :σ→L) :z8 k (σ→k) where
 carrier := {a | v.value (O7 a r)< maxValue v r}
 zero_mem' := by
  change v.value (O7 (0:σ→k) r)< maxValue v r
  rw [show O7 (0:σ→k) r=0 by simp [O7],t7]
  exact zero_lt_one.trans_le (Xx _ _)
 add_mem' := by
  intro a b ha hb
  change v.value (O7 (a+b) r)< maxValue v r
  have he :O7 (a+b) r=O7 a r+O7 b r := by
   simp [O7,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  rw [he]
  exact v.value.map_add_lt ha hb
 smul_mem' := by
  intro c a ha
  change v.value (O7 (c•a) r)< maxValue v r
  have he :O7 (c•a) r=c•O7 a r := by
   simp [O7,Pi.smul_apply,smul_smul,Finset.smul_sum,v9]
  rw [he]
  exact (cvc v c (O7 a r)).trans_lt ha
theorem d4p [qJ k] (h:axV k L) (r :σ→L) :
    ∃ a :σ→k,(∀ v :CurvePlace k L,
      poleOrder v.value (O7 a r)=Tq v.value r) ∧
      ∀ (v :CurvePlace k L) j,v.value (r j)≤ max 1 (v.value (O7 a r)) := by
  classical
  let s :=(b27 h r).toFinset
  have hs (v :CurvePlace k L) :v∈s↔Tq v.value r≠0:= by
    exact (b27 h r).mem_toFinset
  have hmax (v :CurvePlace k L) (hv :v∈s) :
      ∃ j,maxValue v r=v.value (r j) := by
    have hsup:1<Finset.univ.sup (fun j=>v.value (r j)) := by
      by_contra! hl
      apply (hs v).mp hv
      apply (Kv _ _).2
      intro j _
      exact (a6F _ _).2
        ((Gk (s :=zi) (f := fun j=>v.value (r j))
          (uW j)).trans hl)
    have hne : (zi :p9 σ).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sup_empty] at hsup
      exact (not_lt_of_ge zero_le) hsup
    obtain ⟨j,_,hj⟩:=Finset.sup_mem_of_nonempty (f := fun j=>v.value (r j)) hne
    exact ⟨j,(max_eq_right hsup.le).trans hj.symm⟩
  have hproper (v :s) :bca v.val r ≠ ⊤ := by
    obtain ⟨j,hj⟩:=hmax v.val v.prop
    intro ht
    have hm: (LO j (1 :k))∈bca v.val r := by rw [ht]; trivial
    change v.val.value (O7 (LO j (1 :k)) r)< maxValue v.val r at hm
    simp [hj,O7] at hm
  have hcover : (⋃ v :s,(bca v.val r :Set (σ→k)))≠Set.univ := by
    intro he
    obtain ⟨v,hv⟩:=Subspace.exists_eq_top_of_iUnion_eq_univ he
    exact hproper v hv
  obtain ⟨a,ha⟩:=Set.nonempty_compl.2 hcover
  simp only [Set.mem_compl_iff,Ob ,not_exists] at ha
  refine ⟨a,?_,?_⟩
  · intro v
    by_cases hv :v∈s
    · have hnot:=ha ⟨v,hv⟩
      change ¬ v.value (O7 a r)< maxValue v r at hnot
      have he :=(ew3 v r a).antisymm (le_of_not_gt hnot)
      refine vi ?_ ?_
      · obtain ⟨j,hj⟩:=hmax v hv
        exact (c4x _ (he.trans hj).le).trans
          (Gk (s :=zi) (f := fun j=>poleOrder v.value (r j))
            (uW j))
      · apply C4
        intro j _
        exact c4x _ ((cu9 v r j).trans he.ge)
    · have hz :Tq v.value r=0:= by simpa only [hs,not_ne_iff] using hv
      have hle (j:σ) :v.value (r j)≤1 :=
        (a6F _ _).1 ((Kv  _ _).1 hz _ (uW  j))
      rw [hz]
      apply (a6F _ _).2
      exact v.value.map_sum_le fun j _=>(cvc v (a j) (r j)).trans (hle j)
  · intro v j
    by_cases hv :v∈s
    · have hnot:=ha ⟨v,hv⟩
      change ¬ v.value (O7 a r)< maxValue v r at hnot
      exact (cu9 v r j).trans ((le_of_not_gt hnot).trans (UP _ _))
    · have hz :Tq v.value r=0:= by simpa only [hs,not_ne_iff] using hv
      exact ((a6F _ _).1
        ((Kv  _ _).1 hz _ (uW  j))).trans (Xx  _ _)
end
end agN
end
section
namespace agN
noncomputable section
open MJ E7 MvPolynomial
open scoped Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L σ:Type} [lz k] [lz L] [lV k L] [p7 σ]
theorem ewO (i:σ) (a :σ→k) :
   agH (ahO i a) := by
 intro j
 rw [ahO,xu]
 fin_cases j
 · exact G0 k i
 · apply IsHomogeneous.sum
   intro l _
   exact (isHomogeneous_C _ _).mul (G0 _ l)
omit [p7 σ] in
private theorem dOM (u:σ→L) (d:σ →₀ ℕ) (c:k) :
  wL k u (wA d c)=yU d.degree (qU u (wA d c)) := by
 rw [wL,coe_eval₂Hom,eval₂_monomial,aeval_monomial]
 simp only [vZ,Finsupp.prod,zqc]
 rw [← TZ]
 simp only [Du,GB,← t9]
 rw [← map_prod,Gi ,← yl,← n5]
omit [p7 σ] in
theorem dOO (u:σ→L) :
    (SQ k u).IsHomogeneous (pG σ k) := by
  classical
  rw [Ideal.isHomogeneous_iff_forall_subset]
  intro n p hp
  change p∈sI (wL k u) at hp
  change GradedRing.proj (pG σ k) n p∈sI (wL k u)
  rw [GradedRing.proj_apply]
  have hproj: (z9 (pG σ k) p n:aU σ k) =
      homogeneousComponent n p:=Sd p n
  rw [hproj,RingHom.mem_ker]
  have hs (f :aU σ k) {m:ℕ} (hf :f.IsHomogeneous m) :
      wL k u f=yU m (qU u f) := by
    conv_lhs=>rw [f.as_sum,oz]
    conv_rhs=>rw [f.as_sum,oz ,oz]
    apply t6 rfl
    intro d hd
    have hd' : d.degree=m:= by
      by_contra hne
      exact (mem_support_iff.mp hd) (hf.coeff_eq_zero hne)
    rw [dOM,hd']
  have hcoeff : (wL k u p).coeff n=qU u (lJ n p) := by
    nth_rewrite 1 [← p.sum_homogeneousComponent]
    rw [oz ,zaW]
    simp_rw [hs _ (qm _ _),Polynomial.coeff_monomial]
    by_cases hn:n∈Eg (p.totalDegree+1)
    · simp [hn]
    · have hdeg:p.totalDegree<n:= by
        simpa only [Y4 ,not_lt,Nat.succ_le_iff] using hn
      simp [hn,zS n p hdeg]
  rw [hs _ (qm _ _),← hcoeff,RingHom.mem_ker.mp hp]
  simp
private theorem dOQ (E F:Cy k L) (h:E≤F) :
  letI:=(KA h).toAlgebra
  oj E F*oj F L=oj E L:= by
 let:lV E F:=(KA h).toAlgebra
 have :vk E F L:=G2 fun _=>rfl
 exact Module.finrank_mul_finrank E F L
theorem fWK (u:σ→L) (i:σ) (a :σ→k) :
  ccY u i a*oj (YC k u i) L =
   oj (nI k {O7 a (F8 u i)}) L :=
 dOQ _ _ (bTZ u i a)
end
end agN
end
section
namespace aeD
noncomputable section
open MvPolynomial WI
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type} [lz k]
theorem Zy {g:aU σ k} {b:ℕ}
  (hg:g.IsHomogeneous b) (p:aU σ k) (i:ℕ) :
  lJ i (p*g) =
    if b≤ i then lJ (i - b) p*g else 0:= by
 simpa only [ayA] using
  DirectSum.coe_decompose_mul_of_right_mem (pG σ k) i (a :=p) hg
private def truncate (n:ℕ) (p:aU σ k) :aU σ k :=
 ∑ i∈Eg (n+1),lJ i p
private theorem dhI (n:ℕ) (p:aU σ k) :
  (truncate n p).totalDegree≤n:= by
 rw [← uJ]
 apply C9
 intro i hi
 rw [uJ]
 exact (qm i p).totalDegree_le.trans
  (SL (Finset.mem_range.mp hi))
private theorem dOC (n:ℕ) (p:aU σ k) (i:ℕ) :
  lJ i (truncate n p)=if i≤n then lJ i p else 0:= by
 classical
 simp only [truncate,oz ,
  fun j=>Ar (m:=i) (Il j p)]
 simp [RD]
private theorem gEC {I:cy (aU σ k)}
    (hI:I.IsHomogeneous (pG σ k))
    {p f g:aU σ k} {b n:ℕ}
    (hp:p.totalDegree≤n) (hg:g.IsHomogeneous b) (hbn:b≤n)
    (hm:p - f * g∈I) :p - truncate (n - b) f * g∈I:= by
  rw [Nq hI]
  intro i
  rw [sS]
  by_cases hi:i≤n
  · have hh:=zfi hI hm i
    rw [sS ,Zy hg] at hh
    rw [Zy hg]
    by_cases hbi:b≤ i
    · have hle :i - b≤n - b:=Ze hi b
      simpa only [u5 hbi,dOC,u5 hle] using hh
    · simpa only [vG hbi] using hh
  · have ht: (truncate (n - b) f * g).totalDegree≤n :=
      (zk _ _).trans (by
        have ht₀:=dhI (n - b) f
        have hg₀:=hg.totalDegree_le
        omega)
    rw [homogeneousComponent_eq_zero i p (by omega),
      zS  i (truncate (n - b) f * g) (by omega),
      sub_zero]
    exact I.zero_mem
theorem emW [oy σ] {I:cy (aU σ k)}
    (hI:I.IsHomogeneous (pG σ k)) {g:aU σ k} {b n:ℕ}
    (hg:g.IsHomogeneous b) (hbn:b≤n) :
    vl (I ⊔ nq {g}) n +
      vl (I.colon {g}) (n - b)=vl I n:= by
  let J:cy (aU σ k) :=I ⊔ nq {g}
  let A:cy (aU σ k) :=I.colon {g}
  let q:=Ideal.Quotient.factorₐ k (show I≤J from zg)
  let cut:oD I n →ₗ[k] oD J n :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y=> by
      obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
      change q y.val∈_
      rw [← hpy]
      exact t8 hp
  have hcut:v8 cut:= by
    intro y
    obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
    exact ⟨⟨lI I p,t8 hp⟩,u8 hpy⟩
  let mul :=(Vp I g).restrictScalars k
  let emb:oD A (n - b) →ₗ[k] oD I n :=
    (mul.domRestrict _).codRestrict _ fun y=> by
      obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
      change Vp I g y.val∈_
      rw [← hpy,azY]
      have hd:=hg.totalDegree_le
      exact t8 ((zk p g).trans (by omega))
  have hemb (y :oD A (n - b)) :emb y∈wY cut:= by
    rw [Gr]
    apply u8
    change q (Vp I g y.val)=0
    have hex :=(LinearMap.exact_iff.mp (a7c I g))
    have hm:Vp I g y.val ∈
        FV (Vp I g) :=LinearMap.mem_range_self _ _
    rw [← hex] at hm
    exact hm
  let e :=emb.codRestrict (wY cut) hemb
  have he :VO e := by
    constructor
    · intro x y he
      exact u8 (aPy I g
        (oK (fun z=>z.val.val) he))
    · intro y
      obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.val.property
      have hy :q y.val.val=0:=oK Nj y.property
      rw [← hpy] at hy
      have hm:p∈J:=Ideal.Quotient.eq_zero_iff_mem.mp hy
      obtain ⟨a,ha,x,hx,hax⟩:=Submodule.mem_sup.mp hm
      obtain ⟨f,rfl⟩:=Ideal.mem_span_singleton.mp hx
      have hd:p - f * g∈I:= by
        rwa [← hax,t5 g f,add_sub_cancel_right]
      refine ⟨⟨lI A (truncate (n - b) f),
        t8 (dhI _ _)⟩,?_⟩
      apply u8
      apply u8
      change Vp I g (lI A (truncate (n - b) f))=y.val.val
      rw [azY,← hpy,Et]
      simpa only [neg_sub] using I.neg_mem (gEC hI hp hg hbn hd)
  have hrank :=cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hcut,finrank_top,
    ← (Yc e he).finrank_eq] at hrank
  exact hrank
theorem b5W [oy σ] {I:cy (aU σ k)}
   (hI:I.IsHomogeneous (pG σ k)) {g:aU σ k} {b:ℕ}
   (hg:g.IsHomogeneous b) :
   qy (I ⊔ nq {g}) +
     Polynomial.taylor (-(b:ℚ)) (qy (I.colon {g})) =
     affineHilbertPolynomial I:= by
 obtain ⟨N₀,h₀⟩:=FR (I.colon {g})
 obtain ⟨N₁,h₁⟩:=FR (I ⊔ nq {g})
 apply LR (N₀:=max (N₀+b) N₁)
 intro N h
 have hN :=(Xx (N₀+b) N₁).trans h
 have hb:b≤N := by omega
 rw [Polynomial.eval_add,Polynomial.taylor_eval,
   h₁ N ((UP (N₀+b) N₁).trans h),← sub_eq_add_neg,← Nat.cast_sub hb,
   h₀ (N - b) (by omega)]
 exact_mod_cast emW hI hg hb
theorem dMj [oy σ] {I:cy (aU σ k)}
    (hI:I.IsHomogeneous (pG σ k)) {g:aU σ k} {b:ℕ}
    (hg:g.IsHomogeneous b) {d:ℕ} (hd: (qy I).natDegree≤d) :
    (qy (I ⊔ nq {g})).coeff d +
      (qy (I.colon {g})).coeff d =
        (qy I).coeff d:= by
  have hA:=(zy5
    (Ideal.le_colon :I≤I.colon {g})).trans hd
  simpa only [ Xo ,Polynomial.coeff_taylor_of_natDegree_le _ hA] using
    oK (fun p:xm ℚ=>p.coeff d) (b5W hI hg)
end
end aeD
end
section
set_option backward.isDefEq.respectTransparency false
namespace aKt
noncomputable section
open MvPolynomial rW E7
open scoped Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type} [lz k]
abbrev MG (I:cy (aU σ k)) :=aU σ k ⧸ I
abbrev JP (I:cy (aU σ k)) :=pC (MG I)
def SR (I:cy (aU σ k)) (i:σ) :JP I :=
 c9 (MG I) (JP I) (lI I (mD i))
def FO (I:cy (aU σ k)) [I.IsPrime] (a :σ) :
    Cy k (JP I) :=
  YC k (SR I) a
def BQ (I:cy (aU σ k)) [I.IsPrime] (a i:σ) :FO I a :=
 ⟨F8 (SR I) a i,IntermediateField.subset_adjoin _ _ (FU i)⟩
theorem bnL {I:cy (aU σ k)} [I.IsPrime] {a :σ}
   (ha :mD a∉I) :SR I a≠0 :=
 fun h=>ha (Ideal.Quotient.eq_zero_iff_mem.mp
   ((wB (MG I) (JP I)).eq_iff.mp
     (h.trans (t7 (c9 (MG I) (JP I))).symm)))
@[simp] theorem cFa (I:cy (aU σ k)) [I.IsPrime] (a i:σ) :
   (BQ I a i:JP I)=SR I i/SR I a :=rfl
theorem bWY {I:cy (aU σ k)} [I.IsPrime] {a :σ}
  (ha :mD a∉I) :BQ I a a=1 := by
 apply u8
 simp [bnL ha]
theorem bcs (I:cy (aU σ k)) [I.IsPrime] (a :σ) :
  nI k (vh (BQ I a)) = ⊤ := by
 apply (FO I a).lift_injective
 rw [IntermediateField.lift_adjoin,IntermediateField.lift_top]
 rw [← Set.range_comp]
 rfl
private theorem cNj {A:Type} [oq A] (f :k →+* A)
  (u:σ→A) (z :A) {p:aU σ k} {d:ℕ} (hp:p.IsHomogeneous d) :
  p.eval₂ f (fun i=>u i*z)=p.eval₂ f u*z^d:= by
 classical
 simp only [eval₂_eq,KH]
 apply t6 rfl
 intro m hm
 simp only [Du,GB,Gi ,yl]
 congr 2
 have hd:m.degree=d:= by
  by_contra h
  exact (mem_support_iff.mp hm) (hp.coeff_eq_zero h)
 exact oK (fun n=>z^n) hd
private theorem dOL {L:Type} [lz L] [lV k L]
  (u:σ→L) {p:aU σ k} {d:ℕ} (hp:p.IsHomogeneous d) :
  wL k u p=p6 (p.eval₂ (c9 k L) u)*ov ^d:= by
 rw [wL,coe_eval₂Hom,cNj _ _ _ hp]
 congr 1
 exact (hom_eval₂ p _ (p6:L →+* L[X]) u).symm
private theorem dOK {L:Type} [lz L] [lV k L]
   (u:σ→L) (p:aU σ k) (d:ℕ) :
   (wL k u p).coeff d =
     (lJ d p).eval₂ (c9 k L) u:= by
 classical
 conv_lhs=>rw [← Kp (φ:=p)]
 simp only [oz ,zaW,
   dOL u (qm _ _),
   zds]
 by_cases hd:d<p.totalDegree+1
 · rw [S1 d]
   · simp
   · intro j _ hj
     simp [Ne.symm hj]
   · simp [hd]
 · rw [homogeneousComponent_eq_zero d p (by omega),eval₂_zero]
   apply J4
   intro j hj
   have hne :j≠d:= by
     rw [Y4 ] at hj
     omega
   simp [Ne.symm hne]
private theorem epe {I:cy (aU σ k)} [I.IsPrime] {a :σ}
   (ha :mD a∉I) {p:aU σ k} {d:ℕ} (hp:p.IsHomogeneous d) :
   p∈I↔p.eval₂ (c9 k (FO I a)) (BQ I a)=0:= by
 let j:=(FO I a).val
 let q:aU σ k →+* JP I :=
   (c9 (MG I) (JP I)).comp (lI I)
 have hq:q=vH (c9 k (JP I)) (SR I) := by
   apply zh
   · intro c
     rw [JQ]
     rfl
   · intro i
     rw [xW]
     rfl
 have he :q p =
     j (p.eval₂ (c9 k (FO I a)) (BQ I a))*SR I a^d:= by
   have hx (i:σ) :j.toRingHom (BQ I a i)*SR I a=SR I i:= by
     change (SR I i/SR I a)*SR I a= _
     exact div_mul_cancel₀ _ (bnL ha)
   have hj:j.toRingHom.comp (c9 k (FO I a))=c9 k (JP I) :=
     RP k (FO I a) (JP I) |>.symm
   rw [hq,coe_eval₂Hom]
   change _=j.toRingHom _ *_
   rw [hom_eval₂,hj,← cNj _ _ _ hp,funext hx]
 have hk :p∈I↔q p=0:= by
   change p∈I↔c9 (MG I) (JP I) (lI I p)=0
   rw [← t7 (c9 (MG I) (JP I)),
     (wB (MG I) (JP I)).eq_iff,
     vw]
 rw [hk,he,mul_eq_zero,or_iff_left (pow_ne_zero _ (bnL ha)),
   map_eq_zero_iff j j.injective]
theorem bYw {I:cy (aU σ k)} [I.IsPrime] {a :σ}
  (hI:I.IsHomogeneous (pG σ k)) (ha :mD a∉I) :
  SQ k (BQ I a)=I:= by
 classical
 ext p
 change wL k (BQ I a) p=0↔p∈I
 rw [Polynomial.ext_iff]
 simp only [Bf ,dOK,← epe ha
  (qm _ _)]
 exact (Nq hI p).symm
theorem cUQ {E :Type} [lz E] (f :k →+* E)
   {I:cy (aU σ k)} (hI:I.IsHomogeneous (pG σ k)) :
   (I.map (pz f)).IsHomogeneous (pG σ E) := by
 obtain ⟨S,hS⟩:=(Ideal.IsHomogeneous.iff_exists _ _).mp hI
 rw [hS,KI,Set.image_image]
 apply zqZ
 rintro _ ⟨v,_,rfl⟩
 obtain ⟨d,hd⟩:SetLike.IsHomogeneousElem (pG σ k)
     (v :aU σ k) :=v.property
 exact ⟨d,IsHomogeneous.map hd f⟩
end
end aKt
end
section
namespace agN
noncomputable section
open rW MJ E7 MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 :Prop :=
  ∀ (k L:Type) [lz k] [qJ k] [lz L] [lV k L],
    CurveField k L → ∀ V:ValuationSubring L,V ≠ ⊤ →
    (∀ c:k,c9 k L c∈V) →
    ∃ w:CurvePlace k L,w.value.valuationSubring=V
def c2 :Prop :=
  ∀ (k L σ:Type) [lz k] [lz L] [lV k L] [p7 σ]
    (u:σ→L) (i:σ) (a :σ→k),u i≠0 →
    let z :=O7 a (F8 u i)
    pU k z→cxg (k :=k) (F8 u i) z →
      (SQ k u).comap (ahO i a).toRingHom = ⊥ ∧
        (aWb (SQ k u) (ahO i a)).Finite
def c3:Prop :=
  ∀ (k σ:Type) [lz k] [p7 σ]
    (P:cy (aU σ k))
    (φ:aU (Fin 2) k →ₐ[k] aU σ k),
    P.IsPrime→P.IsHomogeneous (pG σ k) →
    agH φ→P.comap φ.toRingHom = ⊥ →
    (aWb P φ).Finite →
    qz P=(QZ φ.toRingHom P:ℚ)
def c4 :Prop :=
  ∀ (k L σ:Type) [lz k] [lz L] [lV k L] [p7 σ]
    (u:σ→L) (i:σ) (a :σ→k),u i≠0 →
    pU k (O7 a (F8 u i)) →
    oZ (nI k {O7 a (F8 u i)}) L →
    (SQ k u).comap (ahO i a).toRingHom = ⊥ →
    QZ (ahO i a).toRingHom (SQ k u)=ccY u i a
private theorem cVs (h:c1) {k L:Type} [lz k] [qJ k]
  [lz L] [lV k L] (hL:CurveField k L) {x t:L}
  (hx : ∀ w:CurvePlace k L,w.value t≤1→w.value x≤1) :
  x7 (yB k {t}) x := by
 let A:=yB k {t}
 let B:=(Dv A L).toSubring
 by_contra hni
 obtain ⟨V,hBV,hxV⟩:=Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
  (R:=B) (show x∉B from hni)
 have hne :V ≠ ⊤ := by
  intro ht
  apply hxV
  rw [ht]
  trivial
 have hmem (y :L) (hy :y∈A) :y∈V :=
  hBV (show y∈B from Oc (x :=(⟨y,hy⟩:A)))
 obtain ⟨w,hw⟩:=h k L hL V hne fun c=>hmem _ (A.algebraMap_mem c)
 have htV:=hmem t (Algebra.subset_adjoin (zT1 t))
 apply hxV
 rw [← hw] at htV ⊢
 exact hx w htV
private theorem eoG (h:c1) {k L σ:Type} [lz k] [qJ k]
   [lz L] [lV k L] [p7 σ] (hL:CurveField k L) {r :σ→L} {z :L}
   (hz :z≠0)
   (hbound : ∀ (w:CurvePlace k L) j,w.value (r j)≤ max 1 (w.value z)) :
   cxg (k :=k) r z := by
 constructor
 · intro j
   exact cVs h hL fun w hw =>
     (hbound w j).trans (max_eq_left hw).le
 · intro j
   apply cVs h hL
   intro w hw
   have hval :1≤w.value z :=(w.value.one_le_val_iff hz).2 hw
   rw [Mk,div_le_iff₀ ((w.value.pos_iff).2 hz),uz]
   exact (hbound w j).trans (max_eq_right hval).le
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :
   E7.c3:= by
 intro k L σ _ _ _ _ _ hL hdiv u i hi
 refine ⟨emC hL hdiv _,?_⟩
 intro hp
 obtain ⟨a,ha,hbound⟩:=d4p hdiv (F8 u i)
 let z :=O7 a (F8 u i)
 have hheight: (∑ᶠ v :CurvePlace k L,poleOrder v.value z) =
     Gb k L (F8 u i) :=finsum_congr ha
 have hz :pU k z :=gDD (hheight.symm ▸ hp)
 have hcharts :=eoG h1 hL hz.ne_zero hbound
 obtain ⟨hker,hfin⟩:=h2 k L σ u i a hi hz hcharts
 let P:=SQ k u
 let φ:=ahO i a
 have hdeg:=h3 k σ P φ (SU _) (dOO u)
   (ewO i a) hker hfin
 have hr :=h4 k L σ u i a hi hz (bGE hL hz) hker
 constructor
 · have hinj:oY (aWb P φ) :=zR
   have hh:=zMe
     (aWb P φ) hfin hinj
   rw [hker,natDegree_affineHilbertPolynomial_bot,Nat.card_fin] at hh
   exact hh
 · rw [hdeg,hr,← Nat.cast_mul,t5 (oj _ L) (ccY u i a),
     fWK,← (hdiv z).2.2.2 hz,hheight]
end
end agN
end
section
set_option backward.isDefEq.respectTransparency false
namespace as6
noncomputable section
open aR dN rW Polynomial
def Zx (P:n8) :af 4 →+* tJ P :=
 (K4 P).comp (pz j8)
abbrev bQA (P:n8) := ↥(Zx P).range
abbrev am4 (P:n8) :=pC (bQA P)
def ee (P:n8) :af 4 →+* am4 P :=
 (c9 (bQA P) (am4 P)).comp (Zx P).rangeRestrict
def dPd (P:n8) :ao →+* am4 P :=
 (ee P).comp (MvPolynomial.C.comp p6)
instance gPz (P:n8) :lV ao (am4 P) :=
 (dPd P).toAlgebra
def aQP (P:n8) [P.IsPrime] :am4 P →+* tJ P :=
 PM (g:=(Zx P).range.subtype) MO
def KK {F:Type} [oq F] (e :af 4 →+* F) :F :=
 e (p5 ov)
def ajH {F:Type} [oq F] (e :af 4 →+* F) (i:Fin 4) :F :=
 e (mD i)
def ahG {F:Type} [oq F] {M:ℕ} (x :F) (Bo:Fin M→F) :F[X] :=
 ∑ i:Fin M,p6 (Bo i)*(ov (R:=F)-Polynomial.C x)^i.val
def ZD {F:Type} [lz F] [lV ao F]
    (D:G4 ao F F) (y :F) (n:ℕ) :F :=
  ((D:F→F)^[n]) y/(n.factorial:F)
def aHA {F:Type} [lz F] [lV ao F]
    (D:G4 ao F F) (x y :F) :F[X] :=
  ahG x (fun i:Fin bf=>ZD D y i.val)
def ab2 {F:Type} [lz F] (e :af 4 →+* F) (g:af 4) :F[X] :=
  ahG (KK e)
    (fun i:Fin bf=>e (su g i.val)/e (qx g)^(2*i.val)/(i.val.factorial:F))
end
end as6
end
section
namespace aY4
noncomputable section
open MvPolynomial MJ agN
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type} [lz k]
variable (P:cy (aU σ k))
variable (φ:aU (Fin 2) k →ₐ[k] aU σ k)
abbrev bKv :cy (aU (Fin 2) k) :=P.comap φ.toRingHom
private def truncate {τ:Type} (n:ℕ) (p:aU τ k) :aU τ k :=
 ∑ i∈Eg (n+1),lJ i p
private theorem dif {τ:Type} {p:aU τ k} {n:ℕ}
  (hp:p.totalDegree≤n) :truncate n p=p:= by
 symm
 calc
  p = ∑ i∈Eg (p.totalDegree+1),homogeneousComponent i p :=
    (Kp p).symm
  _=truncate n p := ?_
 unfold truncate
 apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hp))
 intro i _ hi
 exact zS i p (by simpa using hi)
private theorem gEB {τ:Type} (n:ℕ) (p:aU τ k) :
  (truncate n p).totalDegree≤n:= by
 rw [← uJ]
 apply C9
 intro i hi
 rw [uJ]
 exact (qm i p).totalDegree_le.trans
  (SL (Finset.mem_range.mp hi))
private theorem die {τ:Type} (n i:ℕ) (p:aU τ k) :
  lJ i (truncate n p)=if i≤n then lJ i p else 0:= by
 classical
 simp only [truncate,oz ,
  fun j=>Ar (m:=i) (Il j p)]
 simp [RD]
private theorem ccX (hφ:agH φ)
  {p:aU (Fin 2) k} {i:ℕ} (hp:p.IsHomogeneous i) :
  (φ p).IsHomogeneous i:= by
 rw [Lf (aeval_unique φ) p,aeval_def,algebraMap_eq]
 simpa only [uz] using hp.eval₂ C (φ ∘ mD) (isHomogeneous_C _) hφ
private theorem c5E (hφ:agH φ)
   (p:aU (Fin 2) k) (i:ℕ) :
   lJ i (φ p)=φ (lJ i p) := by
 classical
 conv_lhs=>rw [← dif (p:=p) zc]
 simp only [truncate,oz ,fun j=>Ar (m:=i)
   (ccX φ hφ (qm j p))]
 by_cases hi:i≤p.totalDegree
 · simp [RD,hi]
 · rw [homogeneousComponent_eq_zero i p (by omega),map_zero]
   simp [RD ,hi]
private theorem eax
    (hP:P.IsHomogeneous (pG σ k)) (hφ:agH φ)
    {ι:Type} [p7 ι] (b:ι→aU σ k) (d:ι→ℕ)
    (hb : ∀ j,(b j).IsHomogeneous (d j))
    (hgen : ∀ y :aU σ k ⧸ P,
      ∃ a :ι→aU (Fin 2) k,
        ∑ j,lI P (φ (a j)*b j)=y)
    (n:ℕ) {y :aU σ k ⧸ P} (hy :y∈oD P n) :
    ∃ a :ι→aU (Fin 2) k,(∀ j,(a j).totalDegree≤n) ∧
      ∑ j,lI P (φ (a j)*b j)=y := by
  obtain ⟨p,hp,rfl⟩:=mem_quotientDegreeLE.mp hy
  obtain ⟨a,ha⟩:=hgen (lI P p)
  rw [← oz ,Et] at ha
  let a' := fun j=>if d j≤n then truncate (n - d j) (a j) else 0
  have ha' (j:ι) : (a' j).totalDegree≤n:= by
    by_cases hd:d j≤n
    · simpa only [a',u5 hd] using (gEB (n - d j) (a j)).trans (Nat.sub_le ..)
    · simp [a',hd]
  refine ⟨a',ha',?_⟩
  rw [← oz ,Et,Nq hP]
  intro i
  rw [sS ,oz]
  by_cases hi:i≤n
  · have he (j:ι) :lJ i (φ (a' j)*b j) =
        lJ i (φ (a j)*b j) := by
      rw [aeD.Zy (hb j),aeD.Zy (hb j)]
      by_cases hd:d j≤ i
      · simp only [u5 hd,a',u5 (hd.trans hi),c5E φ hφ,
          die,u5 (Ze hi _)]
      · rw [vG hd,vG hd]
    simpa only [sS ,oz ,he] using zfi hP ha i
  · have he (j:ι) :
        lJ i (φ (a' j)*b j)=0:= by
      rw [aeD.Zy (hb j)]
      by_cases hd:d j≤ i
      · rw [u5 hd]
        by_cases hj:d j≤n
        · simp only [a',u5 hj,c5E φ hφ,die,
            vG (by omega : ¬ i - d j≤n - d j),t7,zero_mul]
        · simp [a',hj]
      · rw [vG hd]
    simp [he,zS i p (by omega :p.totalDegree< i)]
theorem d4c
    (hP:P.IsHomogeneous (pG σ k)) (hφ:agH φ)
    (hf : (aWb P φ).Finite) :
    ∃ (m:ℕ) (b:Fin m→aU σ k),
      ∀ (n:ℕ) (y :aU σ k ⧸ P),y∈oD P n →
        ∃ a :Fin m→aU (Fin 2) k,(∀ j,(a j).totalDegree≤n) ∧
          ∑ j,lI P (φ (a j)*b j)=y := by
  classical
  let g:=aWb P φ
  let:=g.toRingHom.toAlgebra
  have hfin:oZ (aU (Fin 2) k ⧸ bKv P φ)
      (aU σ k ⧸ P) :=hf
  obtain ⟨s,hs⟩:=hfin.fg_top
  choose f hf using fun i:s=>sH (I:=P) (i:aU σ k ⧸ P)
  obtain ⟨D,hD⟩:=Finite.exists_le (fun j=>(f j).totalDegree)
  let ι:=s×Fin (D + 1)
  let b:ι→aU σ k := fun j=>lJ j.2 (f j.1)
  let e :Fin (zm ι) ≃ ι:=(NW ι).symm
  refine ⟨_,b ∘ e,eax P φ hP hφ _ (fun j=>(e j).2)
    (fun j=>qm _ _) ?_⟩
  intro y
  have hy :y∈Fa (aU (Fin 2) k ⧸ bKv P φ)
      (vh (fun i:s=>(i:aU σ k ⧸ P))) := by
    rw [Subtype.range_coe_subtype,Finset.setOfPred_mem,hs]
    trivial
  obtain ⟨c,hc⟩:=(Submodule.mem_span_range_iff_exists_fun _).mp hy
  choose a ha using fun j=>sH (I:=bKv P φ) (c j)
  refine ⟨fun j=>a (e j).1,?_⟩
  change (∑ j,lI P (φ (a (e j).1)*b (e j)))=y
  rw [Equiv.sum_comp e (fun j:ι=>lI P (φ (a j.1)*b j))]
  rw [Fintype.sum_prod_type]
  convert hc using 1
  apply t6 rfl
  intro j _
  have hsum : ∑ l:Fin (D + 1),lJ l (f j)=f j:= by
    rw [Kl (fun l:ℕ=>lJ l (f j))]
    exact dif (hD j)
  simp only [b,← oz ,← G6,hsum,n5 ,hf]
  rw [xI,← ha j]
  rfl
end
end aY4
end
section
namespace bRx
noncomputable section
open MJ E7 agN
open scoped Polynomial RatFunc
attribute [local instance] Polynomial.algebra
private def scale {L:Type} [lz L] (b:L) (hb:b≠0) :
  L[X] ≃ₐ[L] L[X] :=
 Polynomial.algEquivOfCompEqX (p6 b⁻¹*ov)
  (p6 b*ov)
  (by simp [← Qy ,← yl,hb])
  (by simp [← Qy ,← yl,hb])
private theorem bnK {k L σ:Type} [lz k] [lz L] [lV k L]
   (w:σ→L) (b:L) (hb:b≠0) :
   wL k (fun i=>w i/b)=(scale b hb).toRingHom.comp (wL k w) := by
 apply zh
 · intro c
   simp [wL,scale,zrE]
 · intro i
   simp only [vZ,wL,xW]
   change p6 (w i/b)*ov =
     EP (p6 b⁻¹*ov) (p6 (w i)*ov)
   rw [n5 ,Polynomial.aeval_C,zrE,Polynomial.aeval_X,← yl,
     ← Qy ,div_eq_mul_inv]
private def Fh {k L σ:Type} [lz k] [lz L] [lV k L] (w:σ→L) :
   aU σ k →+* nX L :=
 (c9 L[X] (nX L)).comp (wL k w)
private theorem a2S {k L σ:Type} [lz k] [lz L] [lV k L]
  (w:σ→L) (c:k) :
  Fh w (p5 c)=uh (c9 k L c) := by
 simp [Fh,wL]
private theorem aHd {k L σ:Type} [lz k] [lz L] [lV k L]
  (w:σ→L) (i:σ) :
  Fh (k :=k) w (mD i)=uh (w i)*RatFunc.X:= by
 simp [Fh,wL]
private theorem bYx {k L σ:Type} [lz k] [lz L] [lV k L]
  (w:σ→L) (b:L) (hb:b≠0) :
  sI (Fh (k :=k) (fun i=>w i/b))=SQ k w:= by
 rw [Fh,Yo _ (RatFunc.algebraMap_injective L),
  bnK w b hb]
 exact Yo (wL k w)
  (f :=(scale b hb).toRingHom) (scale b hb).injective
private def ace {A K:Type} [oq A] [lz K]
  (P:cy A) [P.IsPrime] (e :A →+* K) (h:sI e=P) :
  pC (A ⧸ P) →+* K :=
 PM (RingHom.lift_injective_of_ker_le_ideal P
  (fun _ ha=>RingHom.mem_ker.mp (h.symm ▸ ha)) h.le)
private theorem ay4 {A K:Type} [oq A] [lz K]
   (P:cy A) [P.IsPrime] (e :A →+* K) (h:sI e=P) (a :A) :
   ace P e h
     (c9 (A ⧸ P) (pC (A ⧸ P)) (lI P a))=e a := by
 rw [ace,zoc,Ideal.Quotient.lift_mk]
private theorem b3S {A K:Type} [oq A] [lz K]
  (P:cy A) [P.IsPrime] (e :A →+* K) (h:sI e=P)
  (S:Subfield K) (he : ∀ a,e a∈S) :
  (ace P e h).fieldRange≤S:= by
 rintro _ ⟨z,rfl⟩
 obtain ⟨x,y,_,rfl⟩:=P7 (A ⧸ P) z
 obtain ⟨a,rfl⟩:=sH x
 obtain ⟨b,rfl⟩:=sH y
 rw [Mk,ay4,ay4]
 exact S.div_mem (he a) (he b)
private theorem bgs {F K:Type} [lz F] [lz K]
    (g:nX F →+* K) (S:Subfield K)
    (hC : ∀ a,g (uh a)∈S) (hX:g Dw∈S) (z :nX F) :g z∈S:= by
  have hp (p:F[X]) :g (c9 F[X] (nX F) p)∈S:= by
    induction p using X8 with
    | add p q hp hq =>
        rw [qM,qM]
        exact S.add_mem hp hq
    | monomial n a =>
        rw [RatFunc.algebraMap_monomial,n5 ,t9]
        exact S.mul_mem (hC a) (S.pow_mem hX n)
  induction z using RatFunc.induction_on with
  | f p q hq =>
      rw [Mk]
      exact S.div_mem (hp p) (hp q)
private theorem aWK {F L:Type} [lz F] [lz L] [lV F L]
   (p:F[X]) :
   c9 (nX F) (nX L) (c9 F[X] (nX F) p) =
     c9 L[X] (nX L) (p.map (c9 F L)) := by
 rw [← Au F[X] (nX F) (nX L),
   Au F[X] L[X] (nX L)]
 rfl
private theorem a7t {F L:Type} [lz F] [lz L] [lV F L] (c:F) :
  c9 (nX F) (nX L) (uh c)=uh (c9 F L c) := by
 simpa only [RatFunc.algebraMap_C,Mj] using
  aWK (L:=L) (p6 c)
private theorem buI {F L:Type} [lz F] [lz L] [lV F L] :
  c9 (nX F) (nX L) Dw=RatFunc.X:= by
 simpa only [RatFunc.algebraMap_X,Polynomial.map_X] using
  aWK (L:=L) (ov :F[X])
private theorem fTv {E F L:Type} [lz E] [lz F] [lz L]
   [lV E F] [lV F L] [lV E L] [vk E F L] :
   (c9 (nX F) (nX L)).comp (c9 (nX E) (nX F)) =
     c9 (nX E) (nX L) := by
 apply Nr (A:=E[X])
 intro p
 rw [vZ,aWK,aWK,aWK,
   zoi,← RP E F L]
private theorem cSY {k L σ:Type} [lz k] [lz L] [lV k L]
    (w:σ→L) (i:σ) (hi:w i=1) (F:Cy k L)
    (hF:nI k (vh w)=F)
    (P:cy (aU σ k)) [P.IsPrime] (hP:sI (Fh w)=P) :
    ∃ e :pC (aU σ k ⧸ P) ≃+* nX F,
      (c9 (nX F) (nX L)).comp e.toRingHom=ace P (Fh w) hP:= by
  let f :=ace P (Fh w) hP
  let g:=c9 (nX F) (nX L)
  have he (p:aU σ k) :Fh w p∈f.fieldRange :=
    ⟨_,ay4 P (Fh w) hP p⟩
  have hcoord (j:σ) :uh (w j)*Dw∈f.fieldRange := by
    simpa only [aHd] using he (mD j)
  have hX:Dw∈f.fieldRange := by
    simpa only [hi,Gj,uz] using hcoord i
  have hconstants (c:F) :uh (c:L)∈f.fieldRange := by
    let S:Cy k L :=
      (f.fieldRange.comap uh).toIntermediateField (fun b=> by
        change uh (c9 k L b)∈f.fieldRange
        simpa only [a2S] using he (p5 b))
    have hle :F≤S:= by
      rw [← hF,zmT]
      rintro _ ⟨j,rfl⟩
      change uh (w j)∈f.fieldRange
      have h:=f.fieldRange.div_mem (hcoord j) hX
      rwa [Ww _ RatFunc.X_ne_zero] at h
    exact hle c.property
  have hg:g.fieldRange=f.fieldRange := by
    apply vi
    · rintro _ ⟨z,rfl⟩
      refine bgs g f.fieldRange (fun c => ?_) ?_ z
      · rw [show g (uh c)=uh (c:L) from a7t c]
        exact hconstants c
      · exact buI (F:=F) (L:=L) ▸ hX
    · apply b3S
      intro p
      induction p using WD with
      | C b =>
          rw [a2S]
          exact ⟨uh (c9 k F b),a7t _⟩
      | add p q hp hq =>
          rw [qM]
          exact g.fieldRange.add_mem hp hq
      | mul_X p j hp =>
          rw [n5 ,aHd]
          refine g.fieldRange.mul_mem hp (g.fieldRange.mul_mem ?_ ⟨Dw ,buI⟩)
          have hj:w j∈F:=hF ▸ LQ k (FU j)
          exact ⟨uh ⟨w j,hj⟩,a7t _⟩
  refine ⟨f.rangeRestrictFieldEquiv.trans
    ((RingEquiv.subfieldCongr hg.symm).trans g.rangeRestrictFieldEquiv.symm),?_⟩
  ext1 x
  change g (g.rangeRestrictFieldEquiv.symm _)=f x
  exact RingHom.rangeRestrictFieldEquiv_apply_symm_apply _ _
private theorem ea8 {E F L KU KV:Type}
   [lz E] [lz F] [lz L] [lz KU] [lz KV]
   [lV E F] [lV F L] [lV E L] [vk E F L]
   (f :KV →+* KU) (eV:KV ≃+* nX E) (eU:KU ≃+* nX F)
   (h: ((c9 (nX F) (nX L)).comp eU.toRingHom).comp f =
     (c9 (nX E) (nX L)).comp eV.toRingHom) :
   letI:=f.toAlgebra
   oj KV KU=oj E F:= by
 let _:lV KV KU:=f.toAlgebra
 have hcomm: (c9 (nX E) (nX F)).comp eV.toRingHom =
     eU.toRingHom.comp f := by
   ext1 x
   apply (c9 (nX F) (nX L)).injective
   change ((c9 (nX F) (nX L)).comp (c9 (nX E) (nX F)))
     (eV x)=(c9 (nX F) (nX L)) (eU (f x))
   rw [fTv]
   exact (FK h x).symm
 calc
   _=oj (nX E) (nX F) :=Algebra.finrank_eq_of_equiv_equiv eV eU hcomm
   _=oj E[X] F[X] :=IsFractionRing.finrank_eq E[X] (nX E) F[X] (nX F)
   _=oj E F:=oK Cardinal.toNat (rank_polynomial_polynomial E F)
theorem proof :agN.c4 := by
  classical
  intro k L σ _ _ _ _ u i a hi _hz _hfinite _hcomap
  let U:=F8 u i
  let z :=O7 a U
  let V:Fin 2→L := ![1,z]
  let E :=nI k {z}
  let F:=YC k u i
  let φ:=(ahO i a).toRingHom
  let P:=SQ k u
  let Q:=P.comap φ
  let _:P.IsPrime :=SU (wL k u)
  let _:Q.IsPrime :=EK φ
  have hU:U i=1 :=div_self hi
  have hV:V 0=1 :=rfl
  have hE :nI k (vh V)=E := by
    apply vi
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨j,rfl⟩
      fin_cases j
      · exact E.one_mem
      · exact LQ k (zT1 z)
    · apply IntermediateField.adjoin_le_iff.mpr
      intro b hb
      rw [Set.mem_singleton_iff.mp hb]
      exact LQ k ⟨1,rfl⟩
  have hnorm: (Fh (k :=k) U).comp φ=Fh V:= by
    apply zh
    · intro b
      change Fh U (ahO i a (p5 b))=Fh V (p5 b)
      simp [a2S]
    · intro j
      change Fh U (ahO i a (mD j))=Fh V (mD j)
      rw [ahO,xu]
      fin_cases j
      · change Fh U (mD i)=Fh V (mD 0)
        rw [aHd,aHd,hU,hV]
      · change Fh U (∑ l,p5 (a l)*mD l) =
          Fh V (mD 1)
        rw [aHd]
        change Fh U (∑ l,p5 (a l)*mD l) =
          uh (∑ l,a l•U l)*Dw
        rw [oz ,oz ,KH]
        apply t6 rfl
        intro l _
        rw [n5 ,a2S,aHd,xI,n5 ,yl]
  have hP:sI (Fh (k :=k) U)=P:=bYx u (u i) hi
  have hQ:sI (Fh (k :=k) V)= Q:= by
    rw [← hnorm,← RingHom.comap_ker,hP]
  let KU:=pC (aU σ k ⧸ P)
  let KV:=pC (aU (Fin 2) k ⧸ Q)
  let fU:KU →+* nX L:=ace P (Fh U) hP
  let fV:KV →+* nX L:=ace Q (Fh V) hQ
  let f :KV →+* KU :=
    zf (zR (I:=P) (f :=φ))
  let _:lV KV KU:=f.toAlgebra
  have hsquare :fU.comp f=fV:= by
    apply Nr (A:=aU (Fin 2) k ⧸ Q)
    intro b
    obtain ⟨p,rfl⟩:=sH b
    have hf :f (c9 (aU (Fin 2) k ⧸ Q) KV (lI Q p)) =
        c9 (aU σ k ⧸ P) KU (lI P (φ p)) := by
      change zZC _ (NI P φ zc) _ _ = _
      rw [S2]
      rfl
    rw [vZ,hf]
    exact (ay4 P (Fh U) hP (φ p)).trans
      ((FK hnorm p).trans (ay4 Q (Fh V) hQ p).symm)
  obtain ⟨eU,heU⟩:=cSY U i hU F rfl P hP
  obtain ⟨eV,heV⟩:=cSY V 0 hV E hE Q hQ
  let _:lV E F:=(KA (bTZ u i a)).toAlgebra
  let _:vk E F L:=G2 fun _=>rfl
  unfold QZ
  rw [Fz (show P.IsPrime from u9)]
  change oj KV KU=oj E F
  apply ea8 (L:=L) f eV eU
  rw [heU,heV]
  exact hsquare
end
end bRx
end
section
set_option synthInstance.maxHeartbeats 80000
namespace aKt
noncomputable section
open MvPolynomial rW E7
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type} [lz k]
private theorem aFj (A F:Type) [oq A] [yo A] [lz F]
  [lV k A] [lV k F] [lV A F] [vk k A F] [ze A F] :
  t4 k F=t4 k A:= by
 have :C5 A F:=IsLocalization.isAlgebraic _ A⁰
 rw [← NZ k A (A:=F),Pf (R:=A) (A:=F),add_zero]
private theorem gEd {A B:Type} [oq A] [yo A] [oq B]
  [yo B] [lV k A] [lV k B] (g:B →ₐ[k] A) (hg:oY g)
  (hfinite :g.Finite) :t4 k A=t4 k B:= by
 let algebra :=g.toRingHom.toAlgebra
 let:=algebra
 let:vk k B A:=IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
 let:FaithfulSMul B A:=(zSO B A).mpr hg
 let:oZ B A:=hfinite
 have :C5 B A:=Algebra.IsIntegral.isAlgebraic
 simpa only [Pf (R:=B) (A:=A),add_zero] using
  (NZ k B (A:=A)).symm
private theorem gD6 [oy σ] (I:cy (aU σ k)) [I.IsPrime] :
  t4 k (JP I)=(dimension I:Df) := by
 obtain ⟨d,g,hg,hfinite⟩:=exists_finite_inj_algHom_of_fg k (MG I)
 have hdim:=natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfinite hg
 rw [Nat.card_fin] at hdim
 calc
  t4 k (JP I)=t4 k (MG I) :=aFj _ _
  _=t4 k (aU (Fin d) k) :=gEd g hg hfinite
  _=(d:Df) := by simp [MvPolynomial.trdeg_of_isDomain]
  _=(dimension I:Df) :=oK (fun n:ℕ=>(n:Df)) hdim.symm
private theorem gD7 (I:cy (aU σ k)) [I.IsPrime] (a :σ)
    (heq :SQ k (BQ I a)=I) (ha :mD a∉I) :
    t4 k (JP I)=t4 k (FO I a)+1 := by
  let L:=FO I a
  let F:=pC L[X]
  let f :aU σ k →ₐ[k] L[X] :=
    qU (fun i=>p6 (BQ I a i)*ov)
  have hf :sI f=I:=heq
  let g:MG I →ₐ[k] L[X] :=
    Re I f (fun p hp=>show p∈sI f from hf.symm ▸ hp)
  have hg:oY g :=
    (Ideal.injective_lift_iff _).mpr hf
  let emb:L[X] →ₐ[k] F:=(Qx L[X] F).restrictScalars k
  let u:=emb.comp g
  have hu:oY u:=(wB L[X] F).comp hg
  let j:JP I →ₐ[k] F:=IsFractionRing.liftAlgHom hu
  have hj (i:σ) :j (SR I i) =
      emb (p6 (BQ I a i)*ov) := by
    change PM (g:=u.toRingHom) hu
      (c9 (MG I) (JP I) (lI I (mD i)))= _
    rw [zoc]
    change emb (f (mD i))= _
    rw [xu]
  have hx :j (SR I a)=emb Polynomial.X:= by
    rw [hj,bWY ha,Gj,uz]
  have hz :emb ov≠0:= by
    rw [← hx]
    exact (map_eq_zero j).not.mpr (bnL ha)
  let const:L →ₐ[k] F:=(Qx L F).restrictScalars k
  have hC (c:L) :const c=emb (p6 c) :=
    Au L L[X] F c
  have hc (i:σ) :
      const (BQ I a i)=j (SR I i/SR I a) := by
    rw [Mk,hj,hx,n5 ,Ww _ hz]
    exact hC _
  have hconst : ∀ x :L,const x∈j.fieldRange := by
    have hle :nI k (vh (BQ I a)) ≤
        j.fieldRange.comap const:= by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i,rfl⟩
      exact ⟨_,(hc i).symm⟩
    rw [bcs] at hle
    exact fun x=>hle (show x∈(⊤ : Cy k L) from trivial)
  have hpoly (p:L[X]) :emb p∈j.fieldRange := by
    refine X8 (motive := fun p:L[X]=>emb p∈j.fieldRange) p ?_ ?_
    · intro p q hp hq
      rw [qM]
      exact j.fieldRange.add_mem hp hq
    · intro n c
      rw [← TZ,n5 ,t9,← hx,← hC]
      have hmem:j (SR I a)∈j.fieldRange :=⟨SR I a,rfl⟩
      exact j.fieldRange.mul_mem (hconst c) (j.fieldRange.pow_mem hmem n)
  have hsurj:v8 j:= by
    intro z
    obtain ⟨p,q,_,rfl⟩:=P7 L[X] z
    exact j.fieldRange.div_mem (hpoly p) (hpoly q)
  have :FaithfulSMul k L :=
    (zSO k L).mpr (c9 k L).injective
  calc
    t4 k (JP I)=t4 k F :=
      (AlgEquiv.ofBijective j ⟨j.injective,hsurj⟩).trdeg_eq
    _=t4 k L[X] :=aFj L[X] F
    _=t4 k L+1 := by
      simpa only [Polynomial.trdeg_of_isDomain] using (NZ k L (A:=L[X])).symm
theorem bCy [oy σ] (I:cy (aU σ k)) [I.IsPrime] (a :σ)
   (hhom:I.IsHomogeneous (pG σ k)) (ha :mD a∉I)
   (hdim:dimension I=2) :
   CurveField k (FO I a) ∧ ∃ i,pU k (BQ I a i) := by
 let L:=FO I a
 have hh:=gD7 I a (bYw hhom ha) ha
 rw [gD6 I,hdim] at hh
 change (2 :Df)=t4 k L+1 at hh
 have htr :t4 k L=1 := by
   have hone : (1 :Df)+1=2 := by norm_num
   rw [← hone] at hh
   exact Cardinal.eq_of_add_eq_add_right hh.symm (by simp)
 have hex : ∃ i,pU k (BQ I a i) := by
   by_contra! hall
   have halg:=(IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic
     (F:=k) (S:=vh (BQ I a))).mpr (by rintro _ ⟨i,rfl⟩; exact not_not.mp (hall i))
   rw [bcs] at halg
   have :C5 k L :=
     (zYd (F:=k) (E :=L)).isAlgebraic
   rw [Pf (R:=k) (A:=L)] at htr
   exact zero_ne_one htr
 refine ⟨?_,hex⟩
 obtain ⟨i,hi⟩:=hex
 refine ⟨BQ I a i,hi,?_⟩
 let K:=nI k {BQ I a i}
 have hai:AlgebraicIndependent k (fun _:Fin 1=>BQ I a i) :=
   (algebraicIndependent_singleton_iff (0:Fin 1)).mpr hi
 have hb:=hai.isTranscendenceBasis_of_trdeg_le_of_finite (by
   change t4 k L≤Cardinal.mk (Fin 1)
   simp [htr])
 have hrange :vh (fun _:Fin 1=>BQ I a i) = {BQ I a i} := by
   ext x
   simp only [Set.mem_range,Set.mem_singleton_iff]
   exact ⟨fun ⟨_,h⟩=>h.symm,fun h=>⟨0,h.symm⟩⟩
 have halg:C5 K L:= by
   change C5 (nI k {BQ I a i}) L
   rw [← hrange]
   exact hb.isAlgebraic_field
 have htop:nI K (vh (BQ I a)) = ⊤ := by
   apply IntermediateField.restrictScalars_injective k
   rw [IntermediateField.restrictScalars_adjoin_eq_sup,bcs,sup_top_eq,
     IntermediateField.restrictScalars_top]
 have hf :=IntermediateField.finiteDimensional_adjoin (K:=K)
   (S:=vh (BQ I a)) (fun x _=>(zgs x).isIntegral)
 rw [htop] at hf
 let e :=zYd (F:=K) (E :=L)
 exact II e.toLinearMap e.surjective
theorem bFy {n:ℕ} (I:cy (aU (Fin n) k)) [I.IsPrime]
    (hd:dimension I=2) :
    ∃ a :Fin n,mD a∉I ∧ ∀ i:Fin n,a< i→mD i∈I:= by
  classical
  let s :=Finset.univ.filter fun i:Fin n=>mD i∉I
  have hs :s.Nonempty := by
    by_contra hn
    have hz (i:Fin n) :mD i∈I:= by
      by_contra hx
      exact hn ⟨i,Finset.mem_filter.mpr ⟨uW _,hx⟩⟩
    have hsurj:v8 (c9 k (MG I)) := by
      intro x
      obtain ⟨p,rfl⟩:=sH x
      refine ⟨constantCoeff p,?_⟩
      have he :lI I =
          vH (c9 k (MG I)) (fun _=>0) := by
        apply zh
        · intro c
          rw [JQ]
          rfl
        · intro i
          rw [xW,vw]
          exact hz i
      rw [eval₂Hom_zero'] at he
      exact (FK he p).symm
    let:oZ k (MG I) :=
      II (zdh k (MG I)) hsurj
    rw [dimension,ztK,Polynomial.natDegree_C] at hd
    omega
  refine ⟨s.max' hs,(Finset.mem_filter.mp (Finset.max'_mem s hs)).2,?_⟩
  intro i hi
  by_contra hz
  exact (Te hi) (Finset.le_max' s i (Finset.mem_filter.mpr ⟨uW _,hz⟩))
end
end aKt
end
section
namespace aY4
noncomputable section
open MvPolynomial MJ agN
attribute [local instance] MvPolynomial.gradedAlgebra
theorem proof :agN.c3:= by
 classical
 intro k σ _ _ P φ hprime hP hφ hker hfin
 let Q:=bKv P φ
 let A:=aU (Fin 2) k ⧸ Q
 let B:=aU σ k ⧸ P
 let F:=pC A
 let E :=pC B
 let g:A →ₐ[k] B:=aWb P φ
 have :P.IsPrime :=hprime
 have :Q.IsPrime :=EK φ.toRingHom
 have hg:oY g:=zR
 let:lV A B:=g.toRingHom.toAlgebra
 have :oZ A B:=hfin
 let f :F →+* E :=zf (show oY g.toRingHom from hg)
 let:lV F E :=f.toAlgebra
 let i:A →ₐ[k] F:=Yi k A F
 let j:B →ₐ[k] E :=Yi k B E
 have hi:oY i:=wB A F
 have hj:oY j:=wB B E
 have hcomm (a :A) :j (g a)=c9 F E (i a) := by
   change c9 B E (g a)=f (c9 A F a)
   symm
   apply S2
 have :vk k F E :=G2 fun a=> by
   calc
     c9 k E a=j (g (c9 k A a)) :=((j.comp g).commutes a).symm
     _=c9 F E (c9 k F a) := by rw [hcomm,i.commutes]
 obtain ⟨m,v₀,hv₀⟩:=d4c P φ hP hφ hfin
 let v :Fin m→B:= fun l=>lI P (v₀ l)
 have hv (n:ℕ) (x :B) (hx :x∈oD P n) :
     ∃ a :Fin m→A,(∀ l,a l∈oD Q n) ∧ ∑ l,g (a l)*v l=x := by
   obtain ⟨a,ha,he⟩:=hv₀ n x hx
   refine ⟨(lI Q) ∘ a,fun l=>t8 (ha l),?_⟩
   change (∑ l,lI P (φ (a l))* lI P (v₀ l))=x
   simpa only [n5] using he
 let V:=Fa F (vh (j ∘ v))
 have hV (x :B) :j x∈V:= by
   obtain ⟨n,hn⟩:=exists_mem_quotientDegreeLE P x
   obtain ⟨a,_,rfl⟩:=hv n x hn
   rw [oz]
   refine C9 _ fun l _ => ?_
   rw [n5 ,hcomm,← xI]
   exact Sv _ _ (XG (FU l))
 have htop:V = ⊤ := by
   refine top_unique fun x _ => ?_
   obtain ⟨p,q,hq,rfl⟩:=P7 B x
   obtain ⟨c,a,ha,he⟩:=Algebra.IsAlgebraic.exists_smul_eq_mul A p
     (MS hq)
   have hq' : j q≠0:=(G5 j hj).mpr (MS hq)
   have ha' : i a≠0:=(G5 i hi).mpr ha
   change j p/j q∈V
   have hfrac:j p/j q=j c/ c9 F E (i a) := by
     apply (div_eq_div_iff hq' ((map_ne_zero (c9 F E)).2 ha')).mpr
     have h:=oK j he
     change j (g a*p)=j (q*c) at h
     simpa only [n5 ,hcomm,t5] using h
   rw [hfrac,div_eq_inv_mul,← map_inv₀,← xI]
   exact Sv _ _ (hV c)
 have :oZ F V:=Module.Finite.span_of_finite F (Set.finite_range _)
 have :FiniteDimensional F E :=II V.subtype
   (fun x=>⟨⟨x,htop.symm ▸ Xu⟩,rfl⟩)
 let e :=Module.Basis.ofSpan htop.ge
 let:=FiniteDimensional.fintypeBasisIndex e
 have he (r :_) : ∃ u:B,j u=e r := by
   obtain ⟨l,hl⟩:=Module.Basis.ofSpan_subset htop.ge (FU r)
   exact ⟨v l,hl⟩
 choose u hu using he
 have hg₁ (l:Fin 2) :g (lI Q (mD l))∈oD P 1 :=
   t8 (hφ l).totalDegree_le
 obtain ⟨C₁,h₁⟩:=eyD g i j hi hcomm hg₁ e u hu
 obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples_of_finite (GF A)
   (fun z :Fin m×_=>e.equivFun (j (v z.1)) z.2)
 have hb (l:Fin m) (r :_) : ∃ b:A,i b=i d*e.equivFun (j (v l)) r := by
   obtain ⟨b,hb⟩:=hd (l,r)
   refine ⟨b,?_⟩
   change c9 A F b=c9 A F (d:A)*e.equivFun (j (v l)) r
   simpa only [xI] using hb
 choose b hb using hb
 have hd' : i d≠0:=(G5 i hi).mpr (MS d.property)
 obtain ⟨C₂,h₂⟩:=upper_bound g i j hi hj hcomm e v hv hd' b hb
 have hr :oj F E=zm _:=zdK e
 rw [← hr] at h₁ h₂
 have hdeg:=zMe g hfin hg
 have h:=dVz (zRt (R:=F) (M:=E)).ne' hdeg h₁ h₂
 have hplane :qz Q=1 := by
   rw [show Q = ⊥ from hker,affineDegree_bot]
 rw [hplane,GY] at h
 rw [QZ,Fz hprime]
 exact h
end
end aY4
end
section
namespace NS
noncomputable section
open Filter MvPolynomial Polynomial
open scoped BigOperators
variable {k σ τ:Type*} [lz k] [oy σ] [oy τ]
variable {I:cy (aU σ k)} {J:cy (aU τ k)}
private abbrev aSu (g: (aU τ k ⧸ J) →ₐ[k] (aU σ k ⧸ I)) (n:ℕ) :=
 (oD J n).map g.toLinearMap
private theorem dVk [yo (aU σ k ⧸ I)]
    (g: (aU τ k ⧸ J) →ₐ[k] (aU σ k ⧸ I))
    (i:τ) {ℓ:aU σ k}
    (hℓ:g (lI J (mD i))=lI I ℓ)
    (hb : ∀ x,∃ a b,g b≠0∧g b*x=g a)
    (hr :ahc I ℓ) :
    ∃ C:ℕ,∀ n:ℕ,vl I n≤vl J (n+C) := by
  classical
  obtain ⟨N,hred⟩:=hr
  let B:=Module.finBasis k (oD I N)
  choose a b hb₀ hab using fun j ↦ hb (B j:aU σ k ⧸ I)
  let d := ∏ j,b j
  let other := fun j ↦ ∏ r∈Finset.univ.erase j,b r
  have hd (j:Fin (oj k (oD I N))) :d=other j*b j:= by
    exact (Finset.prod_erase_mul _ b (uW j)).symm
  have hd₀:g d≠0:= by
    rw [show g d = ∏ j,g (b j) by simp [d,map_prod]]
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ hb₀ j
  choose levels hlevels using fun j ↦ exists_mem_quotientDegreeLE J (other j*a j)
  obtain ⟨C,hC⟩:=Finite.exists_le levels
  have hbase (x :aU σ k ⧸ I) (hx :x∈oD I N) :
      g d*x∈aSu g C:= by
    let z :oD I N :=⟨x,hx⟩
    have hz : (∑ j,(B.repr z j)•(B j:aU σ k ⧸ I))=x := by
      simpa only [oz ,FQ,Submodule.subtype_apply] using
        oK (oD I N).subtype (B.sum_repr z)
    rw [← hz,G6]
    refine C9 _ fun j _ ↦ ?_
    have hmul :g d*(B j:aU σ k ⧸ I)=g (other j*a j) := by
      rw [hd j,n5 ,yl,hab j,← n5]
    rw [show g d*((B.repr z j)•(B j:aU σ k ⧸ I)) =
      (B.repr z j)•(g d*(B j:aU σ k ⧸ I)) from
        Algebra.mul_smul_comm (B.repr z j) (g d) (B j:aU σ k ⧸ I),hmul]
    apply Sv
    exact Submodule.mem_map.mpr ⟨_,GR J (hC j) (hlevels j),rfl⟩
  have hstep (n:ℕ) (hn:N≤n) (ih : ∀ x∈oD I n,g d*x∈aSu g (n+C)) :
      ∀ x∈oD I (n+1),g d*x∈aSu g (n+1+C) := by
    intro x hx
    obtain ⟨u,hu,v,hv,rfl⟩:=hred n hn x hx
    obtain ⟨s,hs,he⟩:=Submodule.mem_map.mp (ih v hv)
    change g s=g d*v at he
    rw [mul_add,mul_left_comm (g d),← hℓ]
    apply Submodule.add_mem
    · exact zzl (GR J (by omega)) (ih u hu)
    · change g _ *(g d*v)∈_
      rw [← he,← n5]
      exact Submodule.mem_map.mpr ⟨_,by
        simpa only [Nat.add_left_comm,SM,Nat.add_assoc] using
          mul_mem_quotientDegreeLE (mk_X_mem_quotientDegreeLE J i) hs,rfl⟩
  have hall (n:ℕ) : ∀ x∈oD I n,g d*x∈aSu g (n+C) := by
    induction n with
    | zero =>
      intro x hx
      simpa using hbase x (GR I (Nat.zero_le N) hx)
    | succ n ih =>
      by_cases hn:N≤n
      · exact hstep n hn ih
      · intro x hx
        exact zzl (GR J (Nat.le_add_left C _))
          (hbase x (GR I (by omega) hx))
  refine ⟨C,fun n ↦ ?_⟩
  let mult:=(LinearMap.mulLeft k (g d)).comp (oD I n).subtype
  let m:oD I n →ₗ[k] aSu g (n+C) :=
    mult.codRestrict (aSu g (n+C)) (fun x ↦ hall n x x.property)
  have hm:oY m:= by
    intro x y hxy
    apply u8
    apply mul_left_cancel₀ hd₀
    exact oK Nj hxy
  have hfin:oZ k (aSu g (n+C)) := by
    unfold aSu
    infer_instance
  exact (LinearMap.finrank_le_finrank_of_injective hm).trans
    (Submodule.finrank_map_le _ _)
theorem cJY [yo (aU σ k ⧸ I)]
   (g: (aU τ k ⧸ J) →ₐ[k] (aU σ k ⧸ I))
   (hg:oY g) (i:τ) {ℓ:aU σ k}
   (hℓ:g (lI J (mD i))=lI I ℓ)
   (hlin : ∀ j,g (lI J (mD j))∈oD I 1)
   (hb : ∀ x,∃ a b,g b≠0∧g b*x=g a)
   (hr :ahc I ℓ) :qz I=qz J:= by
 obtain ⟨C,hupper⟩:=dVk g i hℓ hb hr
 have hlower (n:ℕ) :vl J n≤vl I n:= by
   simpa only [uz] using affineHilbertFunction_le_of_injective g hg hlin n
 let P:=qy I
 let Q:=qy J
 have hshift:Tendsto (fun n:ℕ ↦ n+C) atTop atTop :=
   tendsto_atTop_mono (fun n ↦ Nat.le_add_right n C) tendsto_id
 have hbound : ∀ᶠ n:ℕ in atTop,P.eval (n:ℚ)≤(taylor (C:ℚ) Q).eval (n:ℚ) := by
   filter_upwards [Kc I,
     hshift.eventually (Kc J)] with n hn hnC
   rw [taylor_eval,← Nat.cast_add,hn,hnC]
   exact_mod_cast hupper n
 have hbound' : ∀ᶠ n:ℕ in atTop,Q.eval (n:ℚ)≤P.eval (n:ℚ) := by
   filter_upwards [Kc I,
     Kc J] with n hn hn'
   rw [hn,hn']
   exact_mod_cast hlower n
 have hle :=VH
   (zwW I) hbound
 have hge :=VH
   (zwW J) hbound'
 have hdeg:P.natDegree= Q.natDegree :=
   (hle.1.trans_eq (natDegree_taylor Q _)).antisymm hge.1
 have hlc:P.leadingCoeff= Q.leadingCoeff := by
   apply vi _ (hge.2 hdeg.symm)
   simpa only [leadingCoeff_taylor] using hle.2 (hdeg.trans (natDegree_taylor Q _).symm)
 change (P.natDegree.factorial:ℚ)*P.leadingCoeff =
   (Q.natDegree.factorial:ℚ)*Q.leadingCoeff
 rw [hdeg,hlc]
end
end NS
end
section
set_option synthInstance.maxHeartbeats 80000
namespace aKt
noncomputable section
open MvPolynomial
open scoped Polynomial TensorProduct nonZeroDivisors
open Algebra.TensorProduct
variable {k E σ:Type} [lz k] [lz E] [lV k E]
abbrev abk (I:cy (aU σ k)) :=
 I.map (pz (c9 k E))
def bcL (I:cy (aU σ k)) :
    MG I →+* MG (abk (E :=E) I) :=
  NI _ (pz (c9 k E)) zzQ
private def Pd (I:cy (aU σ k)) :
  E ⊗[k] MG I ≃ₐ[E] MG (abk (E :=E) I) := by
 let e :=LP (σ:=σ) k E
 let ι:aU σ k →ₐ[k] E ⊗[k] aU σ k :=includeRight
 have hcomp:e.toRingHom.comp ι.toRingHom=pz (c9 k E) := by
  apply Vz
  intro p
  change e (1 ⊗ₜ[k] p)= _
  simp [e]
 refine (zTd (R:=k) E _ E I).trans
  (Un _ _ e ?_)
 exact ((Ideal.map_map (I:=I) ι.toRingHom e.toRingHom).trans
  (oK (fun f=>I.map f) hcomp)).symm
set_option backward.isDefEq.respectTransparency false in
private theorem aWG (I:cy (aU σ k))
  (z :E) (p:aU σ k) :
  Pd I (z ⊗ₜ[k] lI I p) =
    z•lI _ (pz (c9 k E) p) := by
 simp [Pd]
 exact FQ (G3 E (abk (E :=E) I)).toLinearMap z _
theorem cHF (I:cy (aU σ k)) {z :E}
    (hz :pU k z) :
    oY (vj (bcL (E :=E) I)
      (c9 E (MG (abk (E :=E) I)) z)) := by
  let A:=MG I
  let j:k[X] →ₐ[k] E :=EP z
  let b:A[X] ≃ₐ[k] A ⊗[k] k[X] :=polyEquivTensor k A
  let m:A ⊗[k] k[X] →ₐ[k] A ⊗[k] E :=zv2 (AlgHom.id k A) j
  let c:A ⊗[k] E ≃ₐ[k] E ⊗[k] A:=zOQ k A E
  let e :=Pd (E :=E) I
  let H :A[X] →+* MG (abk (E :=E) I) :=
    e.toRingHom.comp (c.toRingHom.comp (m.toRingHom.comp b.toRingHom))
  have hm:oY m :=
    TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id
      (transcendental_iff_injective.mp hz)
  have hH :H=vj (bcL (E :=E) I)
      (c9 E (MG (abk (E :=E) I)) z) := by
    apply Xp
    · intro a
      obtain ⟨p,rfl⟩:=sH a
      change e (c (m (b (p6 (lI I p)))))= _
      have hC:c (m (b (p6 (lI I p)))) =
          (1 :E) ⊗ₜ[k] lI I p:= by simp [b,c,m,j]
      rw [hC,show e _ = _ from aWG (E :=E) I 1 p,one_smul,
        Ee,Qw]
      rfl
    · change e (c (m (b ov)))= _
      have hX:c (m (b ov))=z ⊗ₜ[k] lI I 1 := by
        simp [b,c,m,j]
      rw [hX,show e _ = _ from aWG I z 1]
      simp only [Gj]
      change z•(1 :MG (abk (E :=E) I)) =
        (ov :A[X]).eval₂ (bcL (E :=E) I)
          (c9 E (MG (abk (E :=E) I)) z)
      rw [ XJ]
      exact (Algebra.algebraMap_eq_smul_one (A:=MG (abk (E :=E) I)) z).symm
  rw [← hH]
  exact e.injective.comp (c.injective.comp (hm.comp b.injective))
theorem bYy (I:cy (aU σ k)) {z :E}
  (hz :pU k z) :oY (bcL (E :=E) I) := by
 rw [← Polynomial.eval₂RingHom_comp_C (bcL (E :=E) I)
  (c9 E (MG (abk (E :=E) I)) z)]
 exact (cHF I hz).comp Polynomial.C_injective
theorem dON (I:cy (aU σ k)) [I.IsPrime]
    [(abk (E :=E) I).IsPrime] {z :E} (hz :pU k z) :
    oY (vj
      (zf (bYy I hz) :
        JP I →+* JP (abk (E :=E) I))
      (c9 E (JP (abk (E :=E) I)) z)) := by
  let A:=MG I
  let:yo A:=(Ideal.Quotient.isDomain_iff_prime I).2 u9
  let B:=MG (abk (E :=E) I)
  let C:=JP (abk (E :=E) I)
  let j:JP I →+* C:=zf (bYy I hz)
  let x :=c9 E C z
  let f :A →+* B:=bcL (E :=E) I
  have hcomp:j.comp (c9 A (JP I))=(c9 B C).comp f :=
    IsLocalization.map_comp (M:=A⁰) (T:=B⁰) _
  have he (p:A[X]) :
      p.eval₂ (j.comp (c9 A (JP I))) x =
        c9 B C (p.eval₂ f (c9 E B z)) := by
    rw [zly,← hcomp,← Au E B C]
  change oY (vj j x)
  intro p q hpq
  have hp: (p - q).eval₂ j x=0 :=
    (Polynomial.eval₂_sub (p:=p) (q:=q) j (x :=x)).trans (sub_eq_zero.mpr hpq)
  have heval :=(he (Gn A⁰ (p - q))).symm.trans
    (IsLocalization.integerNormalization_eval₂_eq_zero A⁰ j (p - q) hp)
  have hzero : (Gn A⁰ (p - q)).eval₂ f (c9 E B z)=0 :=
    (wB B C) (heval.trans (t7 (c9 B C)).symm)
  have hnorm:Gn A⁰ (p - q)=0:= by
    apply cHF I hz
    change (Gn A⁰ (p - q)).eval₂ f (c9 E B z) =
      (0:A[X]).eval₂ f (c9 E B z)
    exact hzero.trans (Polynomial.eval₂_zero _ _).symm
  exact sub_eq_zero.mp ((zQC (A:=A)).mp hnorm)
end
end aKt
end
section
namespace bas
noncomputable section
open aR dN rW
open scoped BigOperators Polynomial
private def Sp:jo[X] :=
 ∑ j:Fin bf,yU j.val (mD j)
private def aQ2 (R:af 4) :jo[X] :=
 yL (zE p5)
  (fun i=>wR i.val Sp) R
private def ajk {F:Type*} [lz F] (k :ao →+* F) (U:F[X]) :
  jo →+* F :=
 vH k (fun j=>U.coeff j.val)
private theorem ezh {F:Type*} [lz F]
  (k :ao →+* F) {U:F[X]} (hd:U.natDegree<bf) :
  Sp.map (ajk k U)=U:= by
 change zE (ajk k U) Sp=U
 simp only [Sp,oz ,Zf ,Polynomial.map_monomial,
  ajk,xW]
 rw [Kl (fun n:ℕ=>yU n (U.coeff n))]
 exact (U.as_sum_range' _ hd).symm
private theorem ezi {F:Type*} [lz F]
   (k :ao →+* F) {U:F[X]} (hd:U.natDegree<bf) (R:af 4) :
   (aQ2 R).map (ajk k U)=jW k R U:= by
 change zE (ajk k U) (aQ2 R)= _
 rw [aQ2,MvPolynomial.hom_eval₂,jW]
 congr 1
 · rw [Polynomial.mapRingHom_comp]
   congr 1
   ext a
   simp [ajk]
 · funext i
   rw [Zf ,← Polynomial.hasseDeriv_map,ezh k hd]
private def Oe :jo[X] →+* mK :=
 vj (pz ni) (p5 rI)
private theorem bpK (i:ℕ) :
   Oe (wR i Sp) =
     J1 rI i:= by
 classical
 simp only [Sp,oz ,J1]
 refine t6 rfl fun j _ => ?_
 rw [Zh]
 simp only [Oe,Ee,Pv,
   n5 ,Iw ,WX]
 rw [t9]
 ac_rfl
private theorem d3j (R:af 4) :
    Oe (aQ2 R)=mS (bC R) := by
  change (Oe.comp
      (vH (zE p5)
        (fun i:Fin 4=>wR i.val Sp))) R =
    (mS.comp (pz j8)) R
  apply FK
  apply zh
  · intro a
    simp only [vZ,JQ,MvPolynomial.map_C,mS]
    change Polynomial.eval₂ (pz ni) (p5 rI)
        (a.map p5)=p5 (j8 a)
    have hm: (pz ni).comp (p5:ao →+* jo) =
        (p5:ox →+* mK).comp ni:= by
      apply Vz
      simp
    rw [Polynomial.eval₂_map,hm,← zly]
    have hx :vj ni rI=j8:= by
      apply Xp
      · intro b
        exact Qw _ _
      · exact XJ _ _
    change p5 ((vj ni rI) a)= _
    rw [hx]
  · intro i
    simpa only [vZ,xW,WX ,
      mS] using bpK i.val
private theorem b3Z {F:Type*} [lz F] (k :ao →+* F)
   {U:F[X]} (hd:U.natDegree<bf) (R:af 4)
   (hR:jW k R U=0) :
   bC R∈lA (Zv k U) := by
 change mS (bC R)∈gN (Zv k U)
 rw [← d3j]
 let T:=aQ2 R
 have hz :T.map (ajk k U)=0:=(ezi k hd R).trans hR
 have hc (n:ℕ) :T.coeff n∈Zv k U:= by
   change ajk k U (T.coeff n)=0
   simpa only [Np,Bf] using
     oK (fun V:F[X]=>V.coeff n) hz
 change Oe T∈_
 rw [oK Oe T.as_sum_range,oz]
 apply Ideal.sum_mem
 intro n _
 rw [Oe,Ee,Pv]
 exact UY _ _ (WY _ (hc n))
private def bs3 (P:n8) :ox →+* tJ P :=
 (K4 P).comp p5
private def a6d (P:n8) (U: (tJ P)[X]) :mK →+* tJ P :=
 vH (bs3 P) (fun j=>U.coeff j.val)
private theorem eGm (P:n8) [P.IsPrime] {U: (tJ P)[X]}
   (hd:U.natDegree<bf) (i:ℕ) :
   a6d P U (J1 rI i) =
     (wR i U).eval (bs3 P rI) := by
 have hsum:U = ∑ j:Fin bf,yU j.val (U.coeff j.val) := by
   rw [Kl (fun n:ℕ=>yU n (U.coeff n))]
   exact U.as_sum_range' _ hd
 rw [oK (fun V=>(wR i V).eval (bs3 P rI)) hsum]
 simp only [J1,oz ,Polynomial.eval_finsetSum]
 refine t6 rfl fun j _ => ?_
 simp only [Zh,Polynomial.eval_monomial,n5 ,a6d,
   JQ,xW,Iw ,t9]
 ring
private theorem b3Y {f Q g:af 4} {P:n8} [P.IsPrime]
    {U: (tJ P)[X]} (h:bjr f Q g P U) :
    lA (Zv (CX P) U)≤P:= by
  have hmap : (a6d P U).comp (pz ni) =
      ajk (CX P) U:= by
    ext a <;> simp [a6d,bs3,ajk,CX]
  have hkill:gN (Zv (CX P) U) ≤
      sI (a6d P U) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact (Lf hmap a).trans ha
  have hcomp: (a6d P U).comp mS=K4 P:= by
    ext a
    · simp [a6d,mS,bs3]
    · rw [vZ,mS,xW,
        eGm P h.degree]
      exact h.initial a
  intro a ha
  have hz :K4 P a=0 :=
    (Lf hcomp a).symm.trans (hkill ha)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply wB (pQ ⧸ P) (tJ P)
  exact hz.trans (t7 _).symm
theorem gDB {f Q g:af 4} {P:n8} [P.IsPrime]
   {U: (tJ P)[X]} (h:bjr f Q g P U)
   (hsep:bC (qx g)∉P) :
   let A:=Zv (CX P) U
   kC f Q≤lA A∧lA A≤P ∧
     bC g∈lA A∧bC (qx g)∉lA A:= by
 dsimp only
 have hle :=b3Y h
 refine ⟨?_,hle,b3Z _ h.degree _ h.bY,fun hs=>hsep (hle hs)⟩
 rw [kC,Ideal.span_le]
 rintro _ (hs | hs)
 · exact hs ▸ b3Z _ h.degree _ h.factor
 · rcases hs with rfl
   exact b3Z _ h.degree _ h.an1
end
end bas
end
section
namespace aFT
noncomputable section
open aR dN
abbrev ale :=separableClosure lN ox
abbrev PJ:=aU (Fin 4) ale
def Ow:PJ →+* GeoJets :=
 pz (c9 ale ox)
def Q0:af 4 →+* PJ :=
 pz ((c9 lN ale).comp (c9 (xm ao) lN))
@[simp] theorem aQd (U:af 4) :Ow (Q0 U)=bC U:= by
  rw [Ow,Q0,MvPolynomial.map_map,bC,j8,
   ← RingHom.comp_assoc,← RP lN ale ox]
end
end aFT
end
section
namespace aFT
noncomputable section
open dN rW
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem cSI:Module.Flat PJ GeoJets := by
 have h:Algebra.IsPushout ale PJ ox GeoJets :=u9
 exact Module.Flat.isBaseChange ale PJ ox pQ h.out
private theorem bIU (J P:n8) [P.IsPrime]
   (h:oA J P ‹P.IsPrime› = 1) :
   J.map (c9 pQ (qG P)) =
     zrY (qG P) := by
 unfold oA at h
 rw [Module.length_eq_one_iff,isSimpleModule_iff_isCoatom,← Ideal.isMaximal_def,
   IsLocalRing.isMaximal_iff] at h
 exact h
end
end aFT
end
section
set_option linter.style.haveILetI false
namespace NS
noncomputable section
open aR dN rW MvPolynomial
open scoped BigOperators
private theorem arj {k K σ:Type*} [lz k] [lz K] [p7 σ]
   (f :k →+* K) (x :σ→K) (t:K) {p:aU σ k} {n:ℕ}
   (hp:p.IsHomogeneous n) :yL f (fun i ↦ t*x i) p=t^n*yL f x p:= by
 classical
 rw [eval₂_eq',eval₂_eq',G6]
 refine t6 rfl fun d hd ↦ ?_
 have hdeg:d.degree=n:= by
   by_contra h
   exact (mem_support_iff.mp hd) (hp.coeff_eq_zero h)
 rw [show (∏ i:σ,(t*x i)^d i)=t^n * ∏ i:σ,x i^d i by
   simp only [Du,GB,Gi ,
     ← PA,hdeg]]
 ring
private theorem b14 {k σ:Type*} [lz k] [p7 σ]
   (x :σ→k) (t:k) {p:aU σ k} {n:ℕ}
   (hp:p.IsHomogeneous n) (hx :eval x p=0) :eval (fun i ↦ t*x i) p=0 :=
 (arj (VC k) x t hp).trans (mul_eq_zero_of_right _ hx)
private theorem bsk {k K σ:Type*} [lz k] [lz K]
  (f :k →+* K) (A:cy (aU σ k)) {p:aU σ k}
  {n:ℕ} (hp:p∈A) (hn:p.totalDegree≤n) :
  pz f (lJ n p)∈lW (A.map (pz f)) := by
 have he :pz f (lJ n p) =
    lJ n (pz f p) := by
  ext d
  by_cases hd:d.degree=n <;> simp only [IU,coeff_map,hd,ite_true,ite_false,t7]
 have hd: (pz f p).totalDegree≤p.totalDegree :=
  Finset.sup_mono (support_map_subset f p)
 exact Aa ⟨pz f p,n,WY _ hp,hd.trans hn,he⟩
private theorem aDK {k σ:Type*} [lz k] [p7 σ] (c:σ→k) :
   (∑ j:σ,p5 (c j)*mD j).IsHomogeneous 1 :=
 (pG σ k 1).sum_mem fun j _ ↦ isHomogeneous_C_mul_X (c j) j
theorem b6J (a :ox) (r :ℕ) : (J1 a r).IsHomogeneous 1 :=
 aDK fun j:Fin bf ↦ (j.val.choose r :ox)*a^(j.val - r)
private theorem aOX (A:kT) {x :Fin bf→ ox}
   (hx :x∈pL ox (lW (gN A)))
   {i:Fin bf} (hi:x i≠0) :
   letI:lV ao GeoField:=ni.toAlgebra
   (fun j ↦ (x i)⁻¹*x j)∈pL ox (KL A i) := by
 letI:lV ao GeoField:=ni.toAlgebra
 let b:Fin bf→GeoField:= fun j ↦ (x i)⁻¹*x j
 change KL A i≤ sI (vH ni b)
 apply sup_le
 · apply Ideal.span_le.mpr
   rintro _ ⟨p,n,hp,hn,rfl⟩
   have he :=hx (pz ni (lJ n p))
     (bsk ni A hp hn)
   change (pz ni (lJ n p)).eval x=0 at he
   rw [eval_map] at he
   change yL ni b (lJ n p)=0
   rw [arj ni x ((x i)⁻¹) (qm ..),he,
     mul_zero]
 · apply Ideal.span_le.mpr
   rintro _ (rfl :_=mD i - 1)
   change yL ni b (mD i - 1)=0
   rw [eval₂_sub,eval₂_X,eval₂_one]
   exact sub_eq_zero.mpr (QL hi)
private theorem a4a {k K σ:Type*} [lz k] [lz K] [lV k K]
  [qJ k] [oy σ] (J:cy (aU σ k)) (hJ:dimension J=0)
  {x :σ→K} (hx :x∈pL K J) (j:σ) : ∃ c:k,c9 k K c=x j:= by
 letI:oZ k (aU σ k ⧸ J) :=
  moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
 let e : (aU σ k ⧸ J) →ₐ[k] K:=Re J (qU x) hx
 have h:x7 k (x j) := by
  have hJX:=(Algebra.IsIntegral.isIntegral (R:=k) (lI J (mD j))).map e
  change x7 k (qU x (mD j)) at hJX
  simpa only [xu] using hJX
 apply h.mem_range_algHom_of_minpoly_splits (K:=k) _ (Qx k K)
 simpa only [Algebra.algebraMap_self,Polynomial.map_id] using
  IsAlgClosed.splits (F9 k (x j))
private theorem ccj {k K σ:Type*} [lz k] [lz K] [p7 σ]
   (f :xm k →+* K) (hf :oY f) (d:σ→ℕ) (hd:oY d)
   (a :σ→k) {i:σ} (hi:a i≠0) :
   (∑ j:σ,f ov ^d j*f (p6 (a j)))≠0:= by
 classical
 let P:xm k := ∑ j:σ,yU (d j) (a j)
 have hcoeff :P.coeff (d i)=a i:= by
   rw [show P.coeff (d i) = ∑ j:σ,(yU (d j) (a j)).coeff (d i) by
     exact oz (Polynomial.lcoeff k (d i)) _ _]
   rw [S1 i]
   · exact Polynomial.coeff_monomial_same _ _
   · intro j _ hj
     exact Polynomial.coeff_monomial_of_ne _ (fun h ↦ hj (hd h.symm))
   · exact fun h ↦ (h (uW i)).elim
 have hp:P≠0:= by
   intro he
   exact hi (by rw [← hcoeff,he,Bf])
 have he :f P = ∑ j:σ,f ov ^d j*f (p6 (a j)) := by
   simp only [P,oz ,← TZ,n5 ,t9,t5]
 rw [← he]
 exact fun h ↦ hp (hf (h.trans f.map_zero.symm))
private theorem bqr {a :Fin bf→ao} {i:Fin bf}
  (hi:a i≠0) :eval (ni ∘ a) (J1 rI 0)≠0:= by
 have hinj:oY j8 :=
  (c9 lN ox).injective.comp (wB (xm ao) lN)
 have hne :=ccj j8 hinj Fin.val Fin.val_injective a hi
 intro h
 apply hne
 rw [← h]
 unfold J1
 rw [oz]
 refine t6 rfl fun j _ ↦ ?_
 simp only [n5 ,eval_C,eval_X,X4 ,Ef ,uz ,
  Nat.sub_zero,Function.comp_apply,rI,ni,vZ]
theorem eEP (A:kT)
  (hA : ∀ i,dimension (KL A i)=0) :
  bjR (gN A) (J1 rI 0) := by
 classical
 letI:lV ao GeoField:=ni.toAlgebra
 intro x hx hval
 funext i
 change x i=0
 by_contra hi
 let b:Fin bf→GeoField:= fun j ↦ (x i)⁻¹*x j
 have hb:b∈pL ox (KL A i) :=aOX A hx hi
 choose a ha using fun j ↦ a4a (KL A i) (hA i) hb j
 have he :ni ∘ a=b:=funext ha
 have hai:a i≠0:= by
  intro ha₀
  have hz :=ha i
  change ni (a i)=(x i)⁻¹*x i at hz
  rw [ha₀,t7,QL hi] at hz
  exact zero_ne_one hz
 apply bqr hai
 rw [he]
 exact b14 x ((x i)⁻¹) (b6J rI 0) hval
end
end NS
end
section
namespace bas
noncomputable section
open aR dN rW MvPolynomial
open scoped Polynomial
def c1 :Prop :=
  ∀ A:kT,A.IsPrime →
    (gN A).IsPrime∧dimension (gN A)=dimension A ∧
      (gN A).comap (pz ni)=A
def c2 :Prop :=
  ∀ (g:af 4) (i:Fin bf),∃ (u:pQ) (e :ℕ),
    ∀ A:kT,A.IsPrime→(gN A).IsPrime →
      bC g∈lA A→bC (qx g)∉lA A →
      mD i*mS (bC (qx g))^e -
        mS u∈gN A
private theorem ceQ (rec:c2) (g:af 4) (h:mK) :
   ∃ (u:pQ) (e :ℕ),∀ A:kT,A.IsPrime→(gN A).IsPrime →
     bC g∈lA A→bC (qx g)∉lA A →
     h*mS (bC (qx g))^e - mS u∈gN A:= by
 let s :=bC (qx g)
 induction h using WD with
 | C a =>
   refine ⟨p5 a,0,fun A _ _ _ _ => ?_⟩
   simp [mS]
 | add h h' ih ih' =>
   obtain ⟨u,e,hu⟩:=ih
   obtain ⟨v,d,hv⟩:=ih'
   refine ⟨u*s^d+v*s^e,e+d,fun A hp he hg hs => ?_⟩
   let q:=lI (gN A)
   have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
   have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   change q (h*mS s^e - mS u)=0 at hu'
   change q (h' * mS s^d - mS v)=0 at hv'
   change q ((h+h')*mS s^(e+d) - mS
     (u*s^d+v*s^e))=0
   simp only [qM,n5 ,sS ,t9,pow_add] at hu' hv' ⊢
   linear_combination q (mS s)^d*hu' + q (mS s)^e*hv'
 | mul_X h i ih =>
   obtain ⟨u,e,hu⟩:=ih
   obtain ⟨v,d,hv⟩:=rec g i
   refine ⟨u*v,e+d,fun A hp he hg hs => ?_⟩
   let q:=lI (gN A)
   have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
   have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   change q (h*mS s^e - mS u)=0 at hu'
   change q (mD i*mS s^d - mS v)=0 at hv'
   change q ((h*mD i)*mS s^(e+d) - mS
     (u*v))=0
   simp only [n5 ,sS ,t9,pow_add,Pr] at hu' hv' ⊢
   calc
     _=(q h*q (mS s)^e) *
         (q (mD i)*q (mS s)^d) := by ac_rfl
     _ = _:= by rw [hu',hv']
private theorem b30 {A:kT} (hA: (gN A).IsPrime) :
  (lA A).IsPrime := by
 let _:=hA
 exact inferInstanceAs ((gN A).comap mS).IsPrime
private theorem bGZ (rec:c2) {A:kT} (hA:A.IsPrime)
   (hext: (gN A).IsPrime) {g:af 4}
   (hg:bC g∈lA A) (hs :bC (qx g)∉lA A) :
   asY A:= by
 intro h
 obtain ⟨u,e,hrel⟩:=ceQ rec g h
 refine ⟨u,bC (qx g)^e,?_,?_⟩
 · intro hp
   exact hs ((b30 hext).mem_of_pow_mem e hp)
 · rw [t9]
   exact hrel A hA hext hg hs
private def a4k :pQ →ₐ[ox] mK :=
 qU (fun i:Fin 4=>J1 rI i.val)
private theorem b3V:a4k.toRingHom=mS:= by
 ext a <;> simp [a4k,mS]
private theorem cKK (rec:c2) {A:kT}
   (hA:A.IsPrime) (hext: (gN A).IsPrime) {g:af 4}
   (hg:bC g∈lA A) (hs :bC (qx g)∉lA A) :
   dimension (lA A)=dimension (gN A) := by
 let I:=gN A
 let J:=lA A
 let v :=bC (qx g)
 have hJ:J=I.comap a4k := by
   change I.comap mS=I.comap a4k.toRingHom
   rw [b3V]
 let F:=Mz I a4k hJ.le
 have hinj:oY F:=Ideal.quotientMap_injective' (H :=hJ.le) hJ.ge
 apply vi (natDegree_affineHilbertPolynomial_le_of_injective F hinj)
 let vI:=mS v
 have hFv :F (lI J v)=lI I vI:= by
   rw [zhw,Zt]
   change lI I (a4k.toRingHom v)= _
   rw [b3V]
 let L:=zUG (lI I vI)
 let _:IsLocalization.Away (F (lI J v)) L:= by
   rw [hFv]
   infer_instance
 let G:=IsLocalization.Away.mapₐ (R:=ox)
   (zUG (lI J v)) L F (lI J v)
 have hsurj:v8 G:= by
   apply (IsLocalization.Away.map_surjective_iff _ _ F.toRingHom (lI J v)).mpr
   intro x
   obtain ⟨h,rfl⟩:=sH x
   obtain ⟨u,e,hrel⟩:=ceQ rec g h
   have hEq:=sub_eq_zero.mp (show
     lI I (h*vI ^e) - lI I (mS u)=0 by
     rw [← sS]
     exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrel A hA hext hg hs))
   refine ⟨lI J u,e,?_⟩
   change F (lI J u)=F (lI J v)^e* lI I h
   rw [hFv,zhw,Zt]
   change lI I (a4k.toRingHom u)= _
   rw [b3V,← hEq,n5 ,t9,t5]
 let _:I.IsPrime :=hext
 have hreg:JW (lI I vI) :=
   IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
     (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
 exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away hreg G hsurj
private theorem b0I {P J:n8} (hP:P.IsPrime) (hJ:J.IsPrime)
  (hlt:P<J) :dimension J<dimension P:= by
 classical
 obtain ⟨s,hJmem,hPmem⟩:=SetLike.exists_of_lt hlt
 have hcut:P ⊔ nq {s} ≤ J :=
  sup_le hlt.le ((Ideal.span_singleton_le_iff_mem J).mpr hJmem)
 let _:=hJ
 obtain ⟨T,hT,hle⟩:=Ideal.exists_minimalPrimes_le hcut
 let _:=hP
 have hd:=SD hPmem hT
 have hlt' : dimension T<dimension P:= by
  change dimension T+1=dimension P at hd
  omega
 exact PD (zy5 hle) hlt'
private theorem cVk (base :c1) (rec:c2) (f :af 4) :
    MK lA {A | A.IsPrime∧bQ1 f A} := by
  intro A hA B hB himage
  obtain ⟨hAp,hAr⟩:=hA
  obtain ⟨hBp,_⟩:=hB
  obtain ⟨hAe,_,hAc⟩:=base A hAp
  obtain ⟨hBe,_,hBc⟩:=base B hBp
  obtain ⟨r,hgA,hsA⟩:=hAr
  let g:=(qx^[r]) f
  have hgB:bC g∈lA B:=himage ▸ hgA
  have hsB:bC (qx g)∉lA B:=himage ▸ hsA
  have hEq:gN A=gN B:= by
    ext h
    obtain ⟨u,e,hrel⟩:=ceQ rec g h
    let s :=mS (bC (qx g))
    have transfer (D:kT) (hDp:D.IsPrime) (hDe : (gN D).IsPrime)
        (hgD:bC g∈lA D) (hsD:bC (qx g)∉lA D) :
        h∈gN D↔u∈lA D:= by
      have hdiff :h*s^e - mS u∈gN D:=hrel D hDp hDe hgD hsD
      have hn:s^e∉gN D:= fun hp=>hsD (hDe.mem_of_pow_mem e hp)
      change _↔mS u∈gN D
      constructor
      · intro hh
        have hm:=UY (s^e) (gN D) hh
        exact ((gN D).sub_mem_iff_right hm).1 hdiff
      · intro hu
        have hm:=((gN D).sub_mem_iff_left hu).1 hdiff
        exact (hDe.mem_or_mem hm).resolve_right hn
    rw [transfer A hAp hAe hgA hsA,transfer B hBp hBe hgB hsB,himage]
  rw [← hAc,← hBc,hEq]
end
end bas
end
section
namespace bRt
open aFU IntermediateField
open scoped algebraAdjoinAdjoin Polynomial
noncomputable section
private def b35 (k A:Type) [lz k] [qJ k]
   [oq A] [lV k A] (p n:ℕ) [y5 k p] [y5 A p] :JM k A :=
 { (SW A p n).range.toSubsemiring with
   algebraMap_mem' r := by
     obtain ⟨s,hs⟩:=IsAlgClosed.exists_pow_nat_eq r (expChar_pow_pos k p n)
     exact ⟨c9 k A s,by rw [iterateFrobenius_def,← t9,hs]⟩ }
private theorem eaW (k A:Type) [lz k] [qJ k]
   [oq A] [lV k A] (p n:ℕ) [y5 k p] [y5 A p]
   (z :A) (hz :yB k ({z} : Set A) = ⊤) :
   oZ (b35 k A p n) A:= by
 let S:=b35 k A p n
 let T:=yB S ({z} : Set A)
 have hi:x7 S z := by
   apply IsIntegral.of_pow (expChar_pow_pos A p n)
   let s :S:=⟨z^p^n,⟨z,rfl⟩⟩
   exact Oc (x :=s)
 have ht:T = ⊤ := by
   have hle :yB k ({z} : Set A)≤T.restrictScalars k :=
     Algebra.adjoin_le (Set.singleton_subset_iff.mpr (G9 S z))
   rw [hz] at hle
   exact vi le_top fun a _=>hle (Algebra.mem_top (R:=k) (x :=a))
 have hfg:T.toSubmodule.FG:=hi.fg_adjoin_singleton
 rw [ht,Algebra.top_toSubmodule] at hfg
 exact ⟨hfg⟩
theorem proof :aFU.c1 := by
  intro k L _ _ _ _ x hx hfin
  let A:=DT k L x
  let K:=nI k ({x} : Set L)
  let E :=separableClosure K L
  let B:=DR k L x
  let C:=Dv A E
  have :oZ K L:=hfin
  have :vk A E L:=G2 fun _=>rfl
  have :Hw A:=bKh hx
  have :oZ A C:=IsIntegralClosure.finite A K E C
  let p:=ringExpChar L
  have :y5 L p:=ringExpChar.expChar L
  have :y5 k p:=(c9 k L).expChar (c9 k L).injective p
  have :y5 A p:=(c9 A L).expChar MO p
  have :y5 E p:=(c9 E L).expChar (c9 E L).injective p
  let n:=IsPurelyInseparable.exponent E L
  let S:=b35 k A p n
  let z :A:=⟨x,G9 k x⟩
  have hz :yB k ({z} : Set A) = ⊤ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval,AlgHom.range_eq_top]
    intro a
    obtain ⟨f,hf⟩:=(Kz k x hx).surjective a
    exact ⟨f,hf⟩
  have :oZ S A:=eaW k A p n z hz
  let σ:A →+* S:=(SW A p n).rangeRestrict
  let e :A ≃+* S:=RingEquiv.ofBijective σ
    ⟨fun _ _ h=>zPu A p n (oK Nj h),
      (SW A p n).rangeRestrict_surjective⟩
  have :RingHomInvPair (e :A →+* S) (e.symm:S →+* A) :=zaI e
  have :RingHomInvPair (e.symm:S →+* A) (e :A →+* S) :=zaI e.symm
  have :th S:=isNoetherianRing_of_ringEquiv A e
  have :oZ S C:=zWg A C
  have :IsNoetherian S C:=u9
  let F:L →+* E :=IsPurelyInseparable.iterateFrobenius E L p (n:=n) zc
  have hF (b:L) :c9 E L (F b)=b^p^n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius E p zc b
  have hmem (b:B) :F b.val∈Dv A E := by
    change x7 A (F b.val)
    apply (IntermediateField.coe_isIntegral_iff (R:=A)).mp
    change x7 A (c9 E L (F b.val))
    rw [hF]
    exact (show x7 A b.val from b.property).pow _
  let g:B →+* C :=
    (F.comp (Dv A L).val.toRingHom).codRestrict (Dv A E).toSubring hmem
  let f :B →ₛₗ[(e :A →+* S)] C :=
    { g with
      map_smul' a b:= by
        apply u8
        apply (c9 E L).injective
        change c9 E L (F (c9 A L a*b.val)) =
          c9 E L (c9 A E (a^p^n)*F b.val)
        rw [hF,Du,n5 ,← Au A E L,t9,hF] }
  apply zfv f
  intro b b' hb
  apply u8
  apply zPu L p n
  change b.val^p^n=b'.val^p^n
  rw [← hF,← hF]
  exact oK (fun c:C=>c9 E L c.val) hb
end
end bRt
end
section
namespace aFT
noncomputable section
open aR dN rW
def c1 :Prop :=
  ∀ (f Q:af 4) (aI:n8)
    (hz : (kC f Q).IsMinimalPrime aI),
    oA (kC f Q) aI hz.isPrime<(K1.p:ℕ∞) →
    (aI.comap Ow).map Ow=aI
def c2 :Prop :=
  ∀ (g:af 4) (aI:n8),aI.IsPrime→ Invariant g aI →
    ∃ D:G4 ℤ PJ PJ,
      (∀ U:af 4,D (Q0 U)= Q0 (u6 g U)) ∧
      (∀ u∈aI.comap Ow,D u∈aI.comap Ow)
private theorem dfw (g:af 4) (D:G4 ℤ PJ PJ)
    (hD : ∀ U:af 4,D (Q0 U)= Q0 (u6 g U))
    (n:ℕ) :
    Q0 (su g (n+1)) =
      Q0 (qx g)*D (Q0 (su g n)) -
        (↑(2*n) :PJ)*D (Q0 (qx g))*Q0 (su g n) := by
  simp only [su,aqZ,sS ,n5 ,Iw ,← hD]
private theorem dfn {R:Type*} [oq R]
  (T P:cy R) [P.IsPrime] (hle :T≤P)
  (D:G4 ℤ R R) (hT : ∀ u∈T,D u∈T)
  {e :R} (he :e∈P) (hDe :D e∈P)
  (hsat : ∀ x∈P,∃ t∉P,t*x∈T ⊔ nq {e}) :
  ∀ u∈P,D u∈P:= by
 intro u hu
 obtain ⟨t,ht,htu⟩:=hsat u hu
 obtain ⟨a,ha,b,hb,hab⟩:=Submodule.mem_sup.mp htu
 obtain ⟨c,hc⟩:=Ideal.mem_span_singleton.mp hb
 have hDb:D b∈P:= by
  rw [hc,D.leibniz,v9,v9]
  exact P.add_mem (P.mul_mem_right _ he) (P.mul_mem_left _ hDe)
 have hDtu:D (t*u)∈P:= by
  rw [← hab,qM]
  exact P.add_mem (hle (hT a ha)) hDb
 rw [D.leibniz,v9,v9] at hDtu
 exact (‹P.IsPrime›.mem_or_mem
  ((P.add_mem_iff_left (P.mul_mem_right (D t) hu)).mp hDtu)).resolve_left ht
end
end aFT
end
section
namespace agO
noncomputable section
open MJ
variable {U V R S:Type} [oq U] [oq V] [oq R] [oq S]
structure a1c (J:cy U) (w:R) where
 toQuotient:R →+* U ⧸ J
 surjective :v8 toQuotient
 ker_eq :sI toQuotient=nq {w}
def Compatible (g:U →+* V) (f :R →+* S) {J:cy U} {I:cy V} {w:R}
    (r :a1c J w) (s :a1c I (f w)) :Prop :=
  ∃ m:U ⧸ J →+* V ⧸ I,
    m.comp (lI J)=(lI I).comp g ∧
    m.comp r.toQuotient=s.toQuotient.comp f
structure cxm {k σ τ:Type} [lz k]
   (φ:aU τ k →ₐ[k] aU σ k) (A:cy (aU σ k)) where
 F:Type
 [field :lz F]
 [algebra :lV k F]
 target :JM k F
 source :JM k F
 le :target≤ source
 targetNoetherian:th target
 sourceNoetherian:th source
 fraction :ze target F
 w:target
 w_ne :w≠0
 targetSection :a1c (lW (A.comap φ)) w
 sourceSection :a1c (lW A) (Pj le w)
 compatible :Compatible φ.toRingHom (Pj le).toRingHom
   targetSection sourceSection
abbrev aF3 (J p:cy R) [p.IsPrime] :=
 qG p ⧸ J.map (c9 R (qG p))
def weight (J p:cy R) :ℕ:= by
  classical
  exact if hp:p.IsPrime then
    letI:=hp
    (t3 (qG p) (aF3 J p)).toNat
  else 0
def degree (f :R →+* S) (p:cy S) :ℕ:= by
  classical
  exact if hp:p.IsPrime then
    letI:=hp
    letI: (p.comap f).IsPrime :=EK f
    let g:pC (R ⧸ p.comap f) →+* pC (S ⧸ p) :=
     zf (zR (I:=p) (f :=f))
    letI:=g.toAlgebra
    oj (pC (R ⧸ p.comap f)) (pC (S ⧸ p))
  else 0
def auX [th S] (f :R →+* S) (J:cy S) (q:cy R) :
    p9 (cy S) := by
  classical
  exact J.minimalPrimesFinset.filter (fun p=>p.comap f=q)
def aNP [th S] (f :R →+* S) (J:cy S) (q:cy R) :ℕ :=
 ∑ p∈auX f J q,weight J p*degree f p
theorem aUP [th S] {f :R →+* S} {J:cy S} {q:cy R}
   (p:auX f J q) : (p:cy S).IsPrime :=
 (Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp p.property).1).isPrime
theorem aDc [th S] {f :R →+* S} {J:cy S} {q:cy R}
   (p:auX f J q) :q=(p:cy S).comap f :=
 (Finset.mem_filter.mp p.property).2.symm
def bmw [th S] (f :R →+* S) (J:cy S) (q:cy R)
    [q.IsPrime] (p:auX f J q) :ℕ∞ :=
  letI: (p:cy S).IsPrime :=aUP p
  letI:=(Ml q (p:cy S) f (aDc p)).toAlgebra
  t3 (qG q) (aF3 J (p:cy S))
abbrev bQZ (L:Type) [oq L] :=JM L (pC L)
abbrev aLX (x :R) (B:Type) [oq B] [lV R B] :=
 B ⧸ nq {c9 R B x}
def gnv (x :R) (B:Type) [oq B] [lV R B] :ℕ∞ :=
 t3 R (aLX x B)
end
end agO
end
section
namespace NS
noncomputable section
open dN rW MvPolynomial
def c1 :Prop :=
 ∀ A:kT,qy (gN A)=qy A
def c2 :Prop :=
  ∀ A:kT,A.IsPrime→dimension A=1 →
    ∀ i:Fin aR.bf,dimension (KL A i)=0
def c3:Prop :=
  ∀ I:cy mK,
    bjR I (J1 rI 0) →
    ahc I (J1 rI 0)
private def al7:pQ →ₐ[ox] mK :=
 qU (fun i:Fin 4 ↦ J1 rI i.val)
private theorem epu (p:pQ) :al7 p=mS p:=rfl
private def ZM (A:kT) :
  (pQ ⧸ lA A) →ₐ[ox] (mK ⧸ gN A) :=
 Mz (gN A) al7 (by
  intro p hp
  exact hp)
private theorem aDt (A:kT) (p:pQ) :
 ZM A (lI (lA A) p)=lI (gN A) (mS p) :=rfl
private theorem brl (A:kT) (j:Fin 4) :
   ZM A (lI (lA A) (mD j)) =
     lI (gN A) (J1 rI j.val) := by
 rw [aDt,← epu]
 exact oK (lI (gN A)) (xu _ _)
private theorem b6L (A:kT) :oY (ZM A) := by
 apply (injective_iff_map_eq_zero (ZM A)).mpr
 intro z hz
 obtain ⟨p,rfl⟩:=sH z
 rw [aDt,vw] at hz
 exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
private theorem dy8 {A:kT} (hb:asY A)
   (x :mK ⧸ gN A) :
   ∃ a b,ZM A b≠0∧ZM A b*x=ZM A a := by
 obtain ⟨p,rfl⟩:=sH x
 obtain ⟨u,v,hv,huv⟩:=hb p
 refine ⟨lI _ u,lI _ v,?_,?_⟩
 · rwa [aDt,Ne,vw]
 · rw [aDt,aDt,t5 ,← n5 ,← Pr,← sS]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr huv
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :rW.c4 := by
  intro A hA hExt hdim hb
  letI:=hExt
  have hred:=h3 (gN A) (eEP A (h2 A hA hdim))
  have hlin (j:Fin 4) :
      ZM A (lI (lA A) (mD j)) ∈
        oD (gN A) 1 := by
    rw [brl]
    exact t8 (b6J rI j.val).totalDegree_le
  have hz :ZM A (lI (lA A) (mD 0)) =
      lI (gN A) (J1 rI 0) :=brl A 0
  have he :=cJY (ZM A) (b6L A) 0 hz hlin
    (dy8 hb) hred
  have hext:qz (gN A)=qz A:= by
    unfold qz
    rw [h1 A]
  exact hext.symm.trans he
end
end NS
end
section
namespace WI
noncomputable section
open aR dN rW MvPolynomial RingTheory.Sequence
open scoped TensorProduct Pointwise
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem cTS:oY j8 :=
 (c9 lN ox).injective.comp
   (wB (K:=lN) _)
theorem ctQ (f :af 4) :
  (bC f).totalDegree=f.totalDegree := by
 unfold totalDegree bC
 rw [support_map_of_injective _ cTS]
theorem agr {f :af 4} (hf :f≠0) :bC f≠0 :=
 fun h=>hf (MvPolynomial.map_injective _ cTS (h.trans (t7 _).symm))
private theorem cTT :
    Module.Flat (aU (Fin 4) lN) GeoJets := by
  let R:=lN
  let B:=aU (Fin 4) R
  let E :=ox
  let e :B ⊗[R] E ≃ₐ[B] GeoJets :=
    { __:=((zOQ R B E).trans
        ((LP (σ:=Fin 4) R E).restrictScalars R)).toRingEquiv
      commutes' := fun b=> by
        change LP R E (1 ⊗ₜ[R] b)=c9 B pQ b
        simpa only [zVJ,one_smul] using
          congrFun (oK DFunLike.coe (MvPolynomial.algebraMap_def (σ:=Fin 4)
            (R:=lN) (S:=ox)).symm) b }
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
private theorem cwM {R:Type} [oq R] (f Q:R) :
   IsWeaklyRegular R [f,Q] ↔
     JW f∧JW (lI (nq {f}) Q) := by
 rw [isWeaklyRegular_cons_iff,isWeaklyRegular_singleton_iff]
 have h:f•(⊤ : z8 R R)=(nq {f} : z8 R R) := by
   rw [← Submodule.ideal_span_singleton_smul,v9,Ideal.mul_top]
 exact and_congr_right' ((Submodule.quotEquivOfEq _ _ h).isSMulRegular_congr Q)
end
end WI
end
section
namespace aY6
noncomputable section
open MvPolynomial rW MJ
variable {k σ:Type*} [lz k]
theorem bcK {I:cy (aU σ k)}
   {p:aU σ k} {n:ℕ} (hp:p∈I) (hn:p.totalDegree≤n) :
   lJ n p∈lW I:= by
 rcases hn.eq_or_lt with rfl | hn
 · exact Aa ⟨p,hp,rfl⟩
 · rw [zS _ _ hn]
   exact (lW I).zero_mem
private abbrev equations (I:cy (aU σ k)) (n:ℕ) :
  z8 k (aU σ k) :=
 I.restrictScalars k ⊓ Dz σ k n
private theorem d1w [oy σ] (I:cy (aU σ k)) (n:ℕ) :
  oZ k (equations I n) :=
 zfv (Submodule.inclusion inf_le_right) (Submodule.inclusion_injective _)
private def aIr (I:cy (aU σ k)) (n:ℕ) :
   equations I n →ₗ[k] aU σ k :=
 (lJ n).domRestrict (equations I n)
private theorem range_le (I:cy (aU σ k)) (n:ℕ) :
  FV (aIr I n)≤FV (aIr (lW I) n) := by
 rintro _ ⟨p,rfl⟩
 have hp:=(Submodule.mem_inf.mp p.property).1
 have hdeg:=(uJ σ n (p:aU σ k)).mp
  (Submodule.mem_inf.mp p.property).2
 have hh:=qm n (p:aU σ k)
 refine ⟨⟨lJ n p,Submodule.mem_inf.mpr ⟨
  bcK hp hdeg,(uJ σ n _).mpr hh.totalDegree_le⟩⟩,?_⟩
 exact z7 hh
private theorem eva {p:aU σ k} {n:ℕ}
    (hp:p.totalDegree≤n+1) :
    lJ (n+1) p=0↔p.totalDegree≤n:= by
  constructor
  · intro hz
    apply C4
    intro d hd
    have hle :d.degree≤n+1 :=(le_totalDegree hd).trans hp
    have hne :d.degree≠n+1 := by
      intro he
      apply mem_support_iff.mp hd
      simpa [IU,he] using
        oK (fun q:aU σ k ↦ q.coeff d) hz
    exact SL (RJ hle hne)
  · intro h
    exact zS _ _ (OJ h)
private theorem ebc (I:cy (aU σ k)) (n:ℕ) :
   oj k (wY (aIr I (n+1))) =
     oj k (equations I n) := by
 have hle :equations I n≤equations I (n+1) := by
   rintro p ⟨hp,hd⟩
   exact ⟨hp,(uJ σ (n+1) p).mpr
     (((uJ σ n p).mp hd).trans (Nat.le_succ n))⟩
 have he :wY (aIr I (n+1)) =
     (equations I n).comap (equations I (n+1)).subtype := by
   ext p
   have hp:=(Submodule.mem_inf.mp p.property).1
   have hdeg:=(uJ σ (n+1) (p:aU σ k)).mp
     (Submodule.mem_inf.mp p.property).2
   rw [Gr]
   change lJ (n+1) (p:aU σ k)=0 ↔
     (p:aU σ k)∈equations I n
   rw [zqd,uJ,eva hdeg]
   exact ⟨fun h ↦ ⟨hp,h⟩,And.right⟩
 rw [he]
 exact (zTz hle).finrank_eq
private theorem ebd (I:cy (aU σ k)) :
   oj k (wY (aIr I 0))=0:= by
 have hker :wY (aIr I 0) = ⊥ := by
   rw [zmb]
   intro p hp
   apply u8
   have hdeg:=(uJ σ 0 (p:aU σ k)).mp
     (Submodule.mem_inf.mp p.property).2
   change lJ 0 (p:aU σ k)=0 at hp
   rw [homogeneousComponent_zero] at hp
   exact (totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)).trans hp
 rw [hker,finrank_bot]
private theorem ebb [oy σ] (I:cy (aU σ k)) (n:ℕ) :
   oj k (equations I n)≤oj k (equations (lW I) n) := by
 have (J:cy (aU σ k)) (d:ℕ) :=d1w J d
 have step (d:ℕ) :=
   Submodule.finrank_mono (range_le I d)
 induction n with
 | zero =>
   have hI:=(aIr I 0).finrank_range_add_finrank_ker
   have hB:=(aIr (lW I) 0).finrank_range_add_finrank_ker
   rw [ebd,add_zero] at hI hB
   exact hI ▸ hB ▸ step 0
 | succ n ih =>
   have hI:=(aIr I (n+1)).finrank_range_add_finrank_ker
   have hB:=(aIr (lW I) (n+1)).finrank_range_add_finrank_ker
   rw [ebc] at hI hB
   exact hI ▸ hB ▸ Ok (step (n+1)) ih
private theorem cUL [oy σ] (I:cy (aU σ k)) (n:ℕ) :
   vl I n+Module.finrank k (equations I n) =
     oj k (Dz σ k n) := by
 let f :=(G3 k I).toLinearMap.domRestrict (Dz σ k n)
 have hker :wY f=(equations I n).comap (Dz σ k n).subtype := by
   ext p
   rw [Gr]
   change lI I (p:aU σ k)=0 ↔
     (p:aU σ k)∈equations I n
   rw [vw ,zqd]
   exact ⟨fun hp ↦ ⟨hp,p.property⟩,And.left⟩
 have hr :FV f=oD I n:=LinearMap.range_domRestrict _ _
 have h:=f.finrank_range_add_finrank_ker
 rw [hr,hker,(zTz inf_le_right).finrank_eq] at h
 exact h
theorem cDp [oy σ] (I:cy (aU σ k)) :
  dimension (lW I)≤dimension I:= by
 apply natDegree_affineHilbertPolynomial_le_of_eventually_le_mul (m:=1) (c:=1) (by decide)
 apply Filter.Eventually.of_forall
 intro n
 simp only [uz]
 have hI:=cUL I n
 have hB:=cUL (lW I) n
 have hle :=ebb I n
 omega
end
end aY6
end
section
namespace agO
noncomputable section
private theorem exN {R S:Type} [oq R] [oq S]
    (f :R →+* S) (p:cy S) [p.IsPrime] (q:cy R) [q.IsPrime]
    (h:q=p.comap f) :
    letI:=(Ml q p f h).toAlgebra
    letI:R9 (c9 (qG q) (qG p)) :=
      RC q p f h
    oj q.ResidueField p.ResidueField=degree f p:= by
  subst q
  let q:=p.comap f
  let _:q.IsPrime :=EK f
  let _:=(Ml q p f rfl).toAlgebra
  let _:R9 (c9 (qG q) (qG p)) :=
    RC q p f rfl
  change oj q.ResidueField p.ResidueField=degree f p
  rw [degree,Fz (show p.IsPrime from u9)]
  let fq: (R ⧸ q) →+* (S ⧸ p) :=NI p f zc
  let ff :pC (R ⧸ q) →+* pC (S ⧸ p) :=
    zf (zR (I:=p) (f :=f))
  let _:=ff.toAlgebra
  let i:=zwr (R ⧸ q) q.ResidueField
  let j:=zwr (S ⧸ p) p.ResidueField
  have hcomm :
      (c9 q.ResidueField p.ResidueField).comp i.toRingHom=j.toRingHom.comp ff := by
    apply Nr (A:=R ⧸ q)
    intro a
    obtain ⟨r,rfl⟩:=sH a
    have hi:i (c9 (R ⧸ q) (pC (R ⧸ q)) (lI q r)) =
        c9 R q.ResidueField r :=
      i.commutes _
    have hf :ff (c9 (R ⧸ q) (pC (R ⧸ q)) (lI q r)) =
        c9 (S ⧸ p) (pC (S ⧸ p)) (lI p (f r)) := by
      change zZC _ fq _ _ = _
      rw [S2]
      rfl
    change c9 q.ResidueField p.ResidueField
        (i (c9 (R ⧸ q) (pC (R ⧸ q)) (lI q r))) =
      j (ff (c9 (R ⧸ q) (pC (R ⧸ q)) (lI q r)))
    rw [hi,hf,j.commutes]
    change Ideal.ResidueField.map q p f rfl (c9 R q.ResidueField r)= _
    exact Ideal.ResidueField.map_algebraMap q p f rfl r
  change oj (q.ResidueField) (p.ResidueField) =
    oj (pC (R ⧸ q)) (pC (S ⧸ p))
  exact (oK Cardinal.toNat (Algebra.rank_eq_of_equiv_equiv
    i.toRingEquiv j.toRingEquiv hcomm)).symm
theorem dAq {R S:Type} [oq R] [oq S] [th S]
  (f :R →+* S) (J:cy S) (q:cy R) [q.IsPrime]
  (p:auX f J q) :
  (bmw f J q p).toNat=weight J (p:cy S)*degree f (p:cy S) := by
 classical
 let hp:=aUP p
 let T:=qG (p:cy S)
 let L:=qG q
 let e :=Ml q (p:cy S) f (aDc p)
 let _:lV L T:=e.toAlgebra
 let _:R9 (c9 L T) :=
  RC q (p:cy S) f (aDc p)
 change (t3 L (aF3 J (p:cy S))).toNat= _
 rw [IsLocalRing.length_restrictScalars L T,ENat.toNat_mul,weight,Fz hp,
  Module.length_eq_rank,Cardinal.toNat_toENat]
 change (t3 T (aF3 J (p:cy S))).toNat *
  oj q.ResidueField (p:cy S).ResidueField= _
 exact oK ((t3 T (aF3 J (p:cy S))).toNat * ·)
  (exN f (p:cy S) q (aDc p))
end
end agO
end
section
namespace cyz
noncomputable section
open rW NS MvPolynomial
open Finset.HasAntidiagonal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type*} [lz k]
private theorem ayA (a :aU σ k) (n:ℕ) :
  (z9 (pG σ k) a n:aU σ k) =
    homogeneousComponent n a :=
 Sd a n
private theorem Zy (a b:aU σ k) (n:ℕ) :
   lJ n (a*b) = ∑ ij∈antidiagonal n,
     lJ ij.1 a*lJ ij.2 b:= by
 let gw:=pG σ k
 calc
   lJ n (a*b)=(z9 gw (a*b) n:aU σ k) :=
     (ayA (a*b) n).symm
   _ = ∑ ij∈antidiagonal n,
         (z9 gw a ij.1 :aU σ k) *
           (z9 gw b ij.2 :aU σ k) := by
     rw [DirectSum.decompose_mul,DirectSum.coe_mul_apply_eq_sum_antidiagonal]
   _ = _:= by simp only [gw,ayA]
private theorem cHx {a b:aU σ k} {i j:ℕ}
  (ha :a.IsHomogeneous i) :
  lJ (i+j) (a*b)=a*lJ j b:= by
 simpa only [ayA,Nat.add_sub_cancel_left] using
  (DirectSum.coe_decompose_mul_of_left_mem_of_le
    (𝒜:=homogeneousSubmodule σ k) (b:=b) ha (Nat.le_add_right i j))
private theorem a5m (I:cy (aU σ k))
    {q:aU σ k} (hq:q∈lW I) :
    ∀ n,∃ r∈I,r.totalDegree≤n∧lJ n r=lJ n q:= by
  unfold lW at hq
  induction hq using zt0 with
  | mem q hq =>
    obtain ⟨p,m,hp,hdeg,rfl⟩:=hq
    intro n
    by_cases h:n=m
    · subst n
      exact ⟨p,hp,hdeg,(z7
        (qm m p)).symm⟩
    · refine ⟨0,I.zero_mem,by simp,?_⟩
      rw [t7 ,Ar  (Il  m p),vG  h]
  | zero=>exact fun n ↦ ⟨0,I.zero_mem,by simp,rfl⟩
  | add a b _ _ ha hb =>
    intro n
    obtain ⟨r,hr,hrd,hre⟩:=ha n
    obtain ⟨s,hs,hsd,hse⟩:=hb n
    exact ⟨r+s,I.add_mem hr hs,(Kh r s).trans (zd hrd hsd),
      by rw [qM,qM,hre,hse]⟩
  | smul a b _ hb =>
    classical
    intro n
    choose r hrI hrDegree hrComponent using hb
    change ∃ p∈I,p.totalDegree≤n ∧
      lJ n p=lJ n (a*b)
    refine ⟨∑ ij∈antidiagonal n,lJ ij.1 a*r ij.2,
      I.sum_mem (fun ij _ ↦ I.mul_mem_left _ (hrI ij.2)),?_,?_⟩
    · rw [← uJ]
      apply C9
      intro ij hij
      rw [uJ,← mem_antidiagonal.mp hij]
      exact (zk _ _).trans (Ok
        (qm ij.1 a).totalDegree_le (hrDegree ij.2))
    · rw [oz ,Zy a b n]
      refine t6 rfl fun ij hij ↦ ?_
      rw [← mem_antidiagonal.mp hij,
        cHx (qm ij.1 a),hrComponent]
private theorem dPO [oy σ] [qJ k]
  {I:cy (aU σ k)} {ℓ:aU σ k} (h:bjR I ℓ) (i:σ) :
  ∃ e :ℕ,mD i^e∈lW I ⊔ nq {ℓ} := by
 let J:=lW I ⊔ nq {ℓ}
 have hx :mD i∈vanishingIdeal k (pL k J) := by
  intro b hb
  have hbI:=zeroLocus_anti_mono (show lW I≤J from zg) hb
  have hright:nq ({ℓ} : Set (aU σ k))≤J:=le_sup_right
  have hbℓ:eval b ℓ=0:=hb ℓ (hright (Aa (by simp)))
  simp only [xu,h b hbI hbℓ,Pi.zero_apply]
 rw [TH] at hx
 exact Ideal.mem_radical_iff.mp hx
private theorem eno [p7 σ]
  {J:cy (aU σ k)} (e :σ→ℕ) (he : ∀ i,mD i^e i∈J)
  {n:ℕ} (hn: (∑ i,e i)<n) {q:aU σ k} (hq:q.IsHomogeneous n) :q∈J:= by
 classical
 rw [← q.support_sum_monomial_coeff]
 apply J.sum_mem
 intro d hd
 have hdDegree :d.degree=n:= by
  by_contra h
  exact (mem_support_iff.mp hd) (hq.coeff_eq_zero h)
 obtain ⟨i,hi⟩ : ∃ i,e i≤d i:= by
  by_contra! h
  have hsum: (∑ i,d i) ≤ ∑ i,e i:=zQk fun i _ ↦ (h i).le
  rw [← PA,hdDegree] at hsum
  exact (Te hn) hsum
 have hsingle :Finsupp.single i (e i)≤d:=Finsupp.single_le_iff.mpr hi
 let d' := d-Finsupp.single i (e i)
 have hd' : d' + Finsupp.single i (e i)=d:=tsub_add_cancel_of_le hsingle
 have hmon :=J.mul_mem_left (wA d' (q.coeff d)) (he i)
 rwa [MvPolynomial.X_pow_eq_monomial,monomial_mul_monomial,GY ,hd'] at hmon
private theorem bZ9 {p:aU σ k} {n:ℕ}
  (hp:p.totalDegree≤n+1) (hzero :lJ (n+1) p=0) :
  p.totalDegree≤n:= by
 unfold totalDegree
 refine C4 fun d hd ↦ ?_
 have hle :d.degree≤n+1 :=(le_totalDegree hd).trans hp
 have hne :d.degree≠n+1 := by
  intro h
  have hcoeff :=oK (fun q:aU σ k ↦ q.coeff d) hzero
  change (lJ (n+1) p).coeff d=0 at hcoeff
  exact (mem_support_iff.mp hd) (by simpa only [IU,u5 h] using hcoeff)
 change d.degree≤n
 omega
private theorem cvb [p7 σ] [qJ k]
    {I:cy (aU σ k)} {ℓ:aU σ k}
    (hℓ:ℓ.IsHomogeneous 1) (h:bjR I ℓ) :ahc I ℓ:= by
  classical
  choose e he using dPO h
  refine ⟨∑ i,e i,?_⟩
  intro n hn z hz
  obtain ⟨p,hp,rfl⟩:=mem_quotientDegreeLE.mp hz
  have htop:lJ (n+1) p∈lW I ⊔ nq {ℓ} :=
    eno e he (OJ hn)
      (qm (n+1) p)
  obtain ⟨u,hu,v,hv,huv⟩:=Submodule.mem_sup.mp htop
  obtain ⟨b,rfl⟩:=Ideal.mem_span_singleton.mp hv
  obtain ⟨r,hrI,hrDegree,hr⟩:=a5m I hu (n+1)
  have hmul (f :aU σ k) :lJ (n+1) (ℓ*f) =
      ℓ*lJ n f := by
    rw [SM n 1,cHx hℓ]
  have htop_eq :lJ (n+1) p =
      lJ (n+1) r+ℓ*lJ n b:= by
    have hcomp:=oK (lJ (n+1)) huv
    simpa only [qM,← hr,hmul,
      z7 (qm (n+1) p)] using hcomp.symm
  let b' := lJ n b
  have hb' : b'.IsHomogeneous n:=qm n b
  let a :=p-(r+ℓ*b')
  have hab: (r+ℓ*b').totalDegree≤n+1 :=
    (Kh _ _).trans (zd hrDegree ((zk _ _).trans
      ((Ok hℓ.totalDegree_le hb'.totalDegree_le).trans_eq (SM 1 n))))
  have ha :a.totalDegree≤n:= by
    apply bZ9
    · rw [← uJ] at hp hab ⊢
      exact (Dz σ k (n+1)).sub_mem hp hab
    · simp only [a,b',sS ,qM,hmul,z7 hb',
        ← htop_eq,sub_self]
  refine ⟨lI I a,t8 ha,
    lI I b',t8 hb'.totalDegree_le,?_⟩
  have hrzero :lI I r=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hrI
  calc
    lI I p=lI I (a+(r+ℓ*b')) :=
      oK (lI I) (sub_add_cancel p (r+ℓ*b')).symm
    _ = _:= by rw [qM,qM,hrzero,zero_add,n5]
theorem proof :NS.c3:= by
 intro I h
 exact cvb (b6J rI 0) h
end
end cyz
end
section
namespace bRp
noncomputable section
open MvPolynomial
open scoped TensorProduct
variable {k L σ:Type*} [lz k] [lz L] [lV k L]
private abbrev rT (L:Type*) [lz L] [lV k L]
  (I:cy (aU σ k)) :cy (aU σ L) :=
 I.map (pz (c9 k L))
private def anK (I:cy (aU σ k)) :
   L ⊗[k] (aU σ k ⧸ I) ≃ₐ[L] aU σ L ⧸ rT L I:= by
 let e :=LP (σ:=σ) k L
 refine (zTd L (aU σ k) L I).trans
   (Un _ _ e ?_)
 change I.map (pz (c9 k L)) =
   (I.map (Algebra.TensorProduct.includeRight (A:=L)).toRingHom).map
     e.toRingEquiv.toRingHom
 rw [Ideal.map_map]
 congr 1
 apply Vz
 intro p
 change pz (c9 k L) p=e (1 ⊗ₜ[k] p)
 simp [e]
private theorem bb2 (I:cy (aU σ k)) (a :L)
  (p:aU σ k) :
  anK I (a ⊗ₜ[k] lI I p) =
    a•lI (rT L I) (pz (c9 k L) p) := by
 unfold anK
 simp only [AlgEquiv.trans_apply,Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
  Ideal.quotientEquivAlg_mk,zVJ]
 exact FQ (G3 L (rT L I)) a _
private theorem cCX (I:cy (aU σ k)) :
  (rT L I).comap (pz (c9 k L))=I:= by
 refine vi (fun p hp => ?_) zzQ
 have hz :lI (rT L I) (pz (c9 k L) p)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr hp
 have he :anK I ((1 :L) ⊗ₜ[k] lI I p)=anK I 0:= by
  simp [bb2,hz]
 have hi:=Algebra.TensorProduct.includeRight_injective
  (B:=aU σ k ⧸ I) (zyB (c9 k L))
 apply Ideal.Quotient.eq_zero_iff_mem.mp
 apply hi
 change (1 :L) ⊗ₜ[k] lI I p=(1 :L) ⊗ₜ[k] 0
 rw [TensorProduct.tmul_zero]
 exact (anK I).injective he
section Prime
variable [oy σ] [qJ k]
private def Bt (I:cy (aU σ k)) (x :σ→k)
  (hx :x∈pL k I) : (aU σ k ⧸ I) →ₐ[k] k :=
 Re I (qU x) (mem_zeroLocus_iff.mp hx)
private theorem d4A (I:cy (aU σ k)) (hI:I.IsPrime)
   (u v :aU σ k ⧸ I) (hu:u≠0) (hv :v≠0) :
   ∃ x :σ→k,∃ hx :x∈pL k I,
     Bt I x hx u≠0∧Bt I x hx v≠0:= by
 classical
 obtain ⟨p,rfl⟩:=sH u
 obtain ⟨q,rfl⟩:=sH v
 have hpq:p*q∉I:= fun h=>(hI.mem_or_mem h).elim
   (fun hp=>hu (Ideal.Quotient.eq_zero_iff_mem.mpr hp))
   (fun hq=>hv (Ideal.Quotient.eq_zero_iff_mem.mpr hq))
 have hvan:vanishingIdeal k (pL k I)=I:= by
   rw [TH,hI.radical]
 have hx : ∃ x∈pL k I,qU x (p*q)≠0:= by
   by_contra! h
   exact hpq (hvan ▸ mem_vanishingIdeal_iff.mpr h)
 obtain ⟨x,hx,h⟩:=hx
 rw [n5 ,mul_ne_zero_iff] at h
 exact ⟨x,hx,h⟩
private theorem gAZ (I:cy (aU σ k)) (hI:I.IsPrime)
   {a b:L ⊗[k] (aU σ k ⧸ I)} (ha :a≠0) (hb:b≠0) :
   a*b≠0:= by
 classical
 let B:=Ts k L
 let e :=znv (N :=aU σ k ⧸ I) B
 have nonzero_coord (w:L ⊗[k] (aU σ k ⧸ I)) (hw:w≠0) :
     ∃ i,e w i≠0:= by
   by_contra! h
   exact hw (e.injective (by simpa only [t7] using Finsupp.ext h))
 obtain ⟨i,hi⟩:=nonzero_coord a ha
 obtain ⟨j,hj⟩:=nonzero_coord b hb
 obtain ⟨x,hx,ha',hb'⟩:=d4A I hI (e a i) (e b j) hi hj
 let f :=Bt I x hx
 let m:=zv2 (AlgHom.id k L) f
 let d:=znv (N :=k) B
 have coord (w:L ⊗[k] (aU σ k ⧸ I)) (l:Zi k L) :
     d (m w) l=f (e w l) := by
   induction w using Wl with
   | tmul c u =>
     simp [d,e,m,FQ]
   | add y z hy hz=>simp [hy,hz]
 have nonzero_image (w:L ⊗[k] (aU σ k ⧸ I))
     (l:Zi k L) (hw:f (e w l)≠0) :m w≠0:= by
   intro h
   exact hw (by rw [← coord,h]; simp)
 let r :=Algebra.TensorProduct.rid (R:=k) (S:=k) (A:=L)
 intro hab
 have h:=oK (fun w=>r (m w)) hab
 have hprod:r (m a)*r (m b)=0:= by simpa only [n5 ,t7] using h
 exact (Pc (fun h=>nonzero_image a i ha' (r.injective (h.trans r.map_zero.symm)))
   (fun h=>nonzero_image b j hb' (r.injective (h.trans r.map_zero.symm)))) hprod
private theorem dyB (I:cy (aU σ k)) (hI:I.IsPrime) :
  (rT L I).IsPrime := by
 refine ⟨fun h=>hI.ne_top ((cCX (L:=L) I).symm.trans (by rw [h,Ideal.comap_top])),
  fun {p q} hpq => ?_⟩
 by_contra! h
 let e :=(anK (L:=L) I).symm
 let a :=e (lI (rT L I) p)
 let b:=e (lI (rT L I) q)
 have ha :a≠0:= fun hz =>
  h.1 (Ideal.Quotient.eq_zero_iff_mem.mp (e.injective (hz.trans e.map_zero.symm)))
 have hb:b≠0:= fun hz =>
  h.2 (Ideal.Quotient.eq_zero_iff_mem.mp (e.injective (hz.trans e.map_zero.symm)))
 apply gAZ I hI ha hb
 rw [← n5 e,← n5 (lI (rT L I)),
  Ideal.Quotient.eq_zero_iff_mem.mpr hpq,t7]
end Prime
section Hilbert
variable [oy σ]
private theorem dyz (I:cy (aU σ k)) (n:ℕ) :
    vl (rT L I) n=vl I n:= by
  classical
  let W:=oD I n
  let V:=oD (rT L I) n
  let f :L ⊗[k] W →ₗ[L] aU σ L ⧸ rT L I :=
    (anK I).toLinearEquiv.toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor L L W.subtype)
  have hcalc (a :L) (z :W) :f (a ⊗ₜ[k] z)=anK I (a ⊗ₜ[k] z.val) :=rfl
  have hinj:oY f :=(anK I).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap W.subtype MO)
  have hrange :FV f=V:= by
    apply vi
    · rintro _ ⟨z,rfl⟩
      induction z using Wl with
      | tmul a z =>
        obtain ⟨p,hp,he⟩:=mem_quotientDegreeLE.mp z.property
        rw [hcalc,← he,bb2]
        apply V.smul_mem
        apply t8
        exact (Finset.sup_mono (support_map_subset (c9 k L) p)).trans hp
      | add y z hy hz=>simpa only [map_add] using V.add_mem hy hz
    · intro y hy
      obtain ⟨p,hp,rfl⟩:=mem_quotientDegreeLE.mp hy
      nth_rw 1 [p.as_sum]
      rw [oz]
      apply C9
      intro m hm
      have hdeg:=(le_totalDegree hm).trans hp
      let z :W:=⟨lI I (wA m 1),
        t8 ((totalDegree_monomial_le m (1 :k)).trans hdeg)⟩
      refine ⟨p.coeff m ⊗ₜ[k] z,?_⟩
      rw [hcalc,show z.val=lI I (wA m 1) from rfl,bb2]
      rw [MvPolynomial.map_monomial,Gj]
      change p.coeff m•G3 L (rT L I) (wA m 1) =
        G3 L (rT L I) (wA m (p.coeff m))
      rw [← FQ,smul_monomial,v9,GY]
  let e :=(LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hrange)
  let B:=Ts k W
  change oj L V=oj k W
  rw [zUF ((B.baseChange L).map e),zUF B]
private theorem dyA (I:cy (aU σ k)) :
  qy (rT L I)=qy I:= by
 obtain ⟨n₀,hn₀⟩:=FR I
 refine (LR (N₀:=n₀) fun n hn => ?_).symm
 rw [hn₀ n hn,dyz]
end Hilbert
open aR dN rW
theorem proof :bas.c1 := by
 intro A hA
 let:lV ao GeoField:=ni.toAlgebra
 exact ⟨dyB A hA,oK Polynomial.natDegree (dyA A),
  cCX A⟩
end
end bRp
end
section
set_option linter.style.haveILetI false
namespace aYZ
noncomputable section
open ac0 YT NS MvPolynomial
variable {k σ:Type} [lz k] [oy σ]
theorem br3 (a :σ→k) : (P5 a).IsHomogeneous 1 := by
 classical
 unfold P5
 exact (pG σ k 1).sum_mem fun i _=>isHomogeneous_C_mul_X (a i) i
private def ah0 (z :σ→k) : (σ→k) →ₗ[k] k := by
 classical
 letI:=JK σ
 exact ∑ i,z i•LinearMap.proj i
private theorem eJO (z a :σ→k) :ah0 z a=eval z (P5 a) := by
 classical
 simp [ah0,P5,t5]
private theorem eJP (z :σ→k) {i:σ} (hi:z i≠0) :
  wY (ah0 z) ≠ ⊤ := by
 classical
 letI:=JK σ
 intro h
 have hz :ah0 z (LO i 1)=0:=LinearMap.mem_ker.mp (h ▸ Xu)
 have hs :ah0 z (LO i 1)=z i:= by
  simp only [ah0,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,
    v9]
  rw [S1 i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp
 exact hi (hs.symm.trans hz)
private theorem aNz (x :σ→k) (c:k)
   {p:aU σ k} {n:ℕ} (hp:p.IsHomogeneous n) :
   eval (fun i=>c*x i) p=c^n*eval x p:= by
 classical
 letI:=JK σ
 change yL (VC k) (fun i=>c*x i) p=c^n*yL (VC k) x p
 rw [eval₂_eq',eval₂_eq',G6]
 refine t6 rfl fun d hd => ?_
 have hdeg:d.degree=n:= by
   by_contra h
   exact (mem_support_iff.mp hd) (hp.coeff_eq_zero h)
 rw [show (∏ i:σ,(c*x i)^d i)=c^n * ∏ i:σ,x i^d i by
   simp only [Du,GB,Gi ,
     ← PA,hdeg]]
 ring
private theorem aOX (I:cy (aU σ k))
   {x :σ→k} (hx :x∈pL k (lW I)) {i:σ} (hi:x i≠0) :
   (fun j=>(x i)⁻¹*x j)∈pL k (KL I i) := by
 let y :σ→k := fun j=>(x i)⁻¹*x j
 change KL I i≤ sI (eval y)
 apply sup_le
 · apply Ideal.span_le.mpr
   rintro _ ⟨p,n,hp,hn,rfl⟩
   apply RingHom.mem_ker.mpr
   change eval (fun j=>(x i)⁻¹*x j) (lJ n p)=0
   rw [aNz x (x i)⁻¹ (qm n p)]
   have hz :eval x (lJ n p)=0 :=
     hx _ (Aa ⟨p,n,hp,hn,rfl⟩)
   rw [hz,mul_zero]
 · apply Ideal.span_le.mpr
   rintro _ (rfl :_=mD i - 1)
   apply RingHom.mem_ker.mpr
   rw [sS ,eval_X,Gj]
   exact sub_eq_zero.mpr (QL hi)
omit [oy σ] in
private theorem dzQ (I:cy (aU σ k)) {i:σ}
  (z :pL k (KL I i)) :z.val i=1 := by
 have h:eval z.val (mD i - 1)=0 :=
  z.property _ (Up (NX _))
 exact sub_eq_zero.mp (by simpa using h)
theorem d31 [qJ k] (I:cy (aU σ k))
   (hI: (qy I).natDegree=1) :
   ∃ bad:p9 (z8 k (σ→k)),(∀ B∈bad,B ≠ ⊤) ∧
     ∀ a :σ→k,(∀ B∈bad,a∉B)→bjR I (P5 a) := by
 classical
 letI:=JK σ
 let e :=NW σ
 letI:G8 σ:=LinearOrder.lift' e e.injective
 letI:In σ:=Finite.to_wellFoundedGT
 let P (i:σ) :=pL k (KL I i)
 letI (i:σ) :p7 (P i) :=
   ((finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero _).mpr
     (bmo I hI i)).fintype
 let obstruction (p:Σ i,P i) :=wY (ah0 p.2.val)
 refine ⟨Finset.univ.image obstruction,?_,?_⟩
 · intro B hB
   obtain ⟨⟨i,z⟩,_,rfl⟩:=Finset.mem_image.mp hB
   apply eJP z.val (i:=i)
   rw [dzQ I z]
   exact one_ne_zero
 · intro a ha x hx hz
   funext i
   change x i=0
   by_contra hi
   let z :P i:=⟨_,aOX I hx hi⟩
   apply ha (obstruction ⟨i,z⟩) (zPV _ (uW _))
   change ah0 z.val a=0
   rw [eJO]
   change eval (fun j=>(x i)⁻¹*x j) (P5 a)=0
   rw [aNz x (x i)⁻¹ (br3 a),hz,mul_zero]
end
end aYZ
end
section
namespace agO
noncomputable section
open MJ
def c1 :Prop :=
  ∀ (k σ τ:Type) [lz k] [oy σ] [oy τ]
    (φ:aU τ k →ₐ[k] aU σ k),agH φ →
    ∀ A:cy (aU σ k),A.IsPrime→aRK φ A →
      Nonempty (cxm φ A)
def c2 :Prop :=
  ∀ (U V R S:Type) [oq U] [oq V] [oq R] [oq S]
    [th V] [th S]
    (g:U →+* V) (f :R →+* S) (J:cy U) (I:cy V) (w:R)
    (r :a1c J w) (s :a1c I (f w)),
    Compatible g f r s →
    ∀ Q:cy U,J.IsMinimalPrime Q →
      ∃ q:cy R,(nq {w}).IsMinimalPrime q ∧
        weight J Q=weight (nq {w}) q ∧
        aNP g I Q=aNP f (nq {f w}) q
def c3:Prop :=
  ∀ (L:Type) [oq L] [yo L] [th L] [IsLocalRing L]
    [Ring.KrullDimLE 1 L] (x :L),x≠0 →
    ∀ (B:bQZ L) (s :p9 (aLX x B)),
      t3 L (Fa L (s :Set (aLX x B)))≤G7 L x
def c4 :Prop :=
  ∀ (R S F:Type) [oq R] [yo R] [oq S] [th S]
    [lz F] [lV R F] [ze R F]
    (f :R →+* S) (e :S →+* F),oY e →
    e.comp f=c9 R F →
    ∀ (w:R) (q:cy R) [q.IsPrime],
      ∃ B:bQZ (qG q),
        (∑ p:auX f (nq {f w}) q,bmw f (nq {f w}) q p) ≤
          gnv (c9 R (qG q) w) B
private theorem evM {L M:Type} [Ring L] [AddCommGroup M] [Module L M]
    (n:ℕ∞) (h : ∀ s :p9 M,t3 L (Fa L (s :Set M))≤n) :
    t3 L M≤n:= by
  classical
  rw [← WithBot.coe_le_coe,WK,Order.krullDim,iSup_le_iff]
  intro t
  have hstep (i:Fin t.length) : ∃ z∈t i.succ,z∉t i.castSucc :=
    Set.not_subset.mp (t.step i).not_ge
  choose z hz hnot using hstep
  let s :=Finset.univ.image z
  let N :=Fa L (s :Set M)
  let u:LTSeries (z8 L N) :=
    { length:=t.length
      toFun:= fun i=>(t i).comap N.subtype
      step:= fun i=> by
        refine RJ (Submodule.comap_mono (t.step i).le) ?_
        intro he
        let a :N :=⟨z i,XG (zPV z (uW i))⟩
        have ha :a∈(t i.succ).comap N.subtype :=hz i
        exact hnot i (show a∈(t i.castSucc).comap N.subtype from he.symm ▸ ha) }
  calc
    _=(u.length:WithBot ℕ∞) :=rfl
    _≤Order.krullDim (z8 L N) :=Order.LTSeries.length_le_krullDim u
    _=(t3 L N :WithBot ℕ∞) :=(WK L N).symm
    _≤_:=WithBot.coe_le_coe.mpr (h s)
private theorem eOu (h3:c3) (h4 :c4)
   {R S F:Type} [oq R] [yo R] [th R]
   [oq S] [th S] [lz F] [lV R F] [ze R F]
   (f :R →+* S) (e :S →+* F) (he :oY e)
   (hcomp:e.comp f=c9 R F)
   (w:R) (hw:w≠0) (q:cy R) (hq: (nq {w}).IsMinimalPrime q) :
   aNP f (nq {f w}) q≤weight (nq {w}) q:= by
 classical
 let _:=hq.isPrime
 let L:=qG q
 let x :=c9 R L w
 have hx :x≠0:= by
   simpa only [x,t7] using (IsLocalization.injective L q.primeCompl_le_nonZeroDivisors).ne hw
 have hdim:Ring.KrullDimLE 1 L:= by
   constructor
   change ringKrullDim L≤(1 :ℕ)
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height q L]
   exact WithBot.coe_le_coe.mpr
     (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq)
 let _:=hdim
 have hfinite :G7 L x ≠ ⊤ := Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
 obtain ⟨B,hB⟩:=h4 R S F f e he hcomp w q
 let I:cy S:=nq {f w}
 have hsum: (∑ p:auX f I q,bmw f I q p)≤G7 L x :=
   hB.trans (evM _ (h3 L x hx B))
 have hsumFinite : (∑ p:auX f I q,bmw f I q p) ≠ ⊤ :=
   (PD hsum hfinite.lt_top).ne
 have hnat :=ENat.toNat_le_toNat hsum hfinite
 rw [ENat.toNat_sum (ENat.sum_ne_top.mp hsumFinite)] at hnat
 have hweight: (G7 L x).toNat=weight (nq {w}) q:= by
   rw [weight,Fz hq.isPrime]
   change _=(t3 L (L ⧸ (nq {w}).map (c9 R L))).toNat
   have hmap : (nq {w}).map (c9 R L)=nq {x} := by
     rw [KI,Vs]
   exact oK (fun J:cy L=>(t3 L (L ⧸ J)).toNat) hmap.symm
 rw [hweight] at hnat
 change aNP f I q≤_
 unfold aNP
 rw [← Finset.sum_coe_sort]
 simpa only [dAq f I q] using hnat
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :
   MJ.c5:= by
 classical
 intro k σ τ _ _ _ φ hφ A hA hbir Q hQ
 obtain ⟨M⟩:=h1 k σ τ φ hφ A hA hbir
 let _:=M.field
 let _:=M.algebra
 let _:=M.targetNoetherian
 let _:=M.sourceNoetherian
 let _:=M.fraction
 let f :=(Pj M.le).toRingHom
 let e :=M.source.val.toRingHom
 obtain ⟨q,hq,hweight,hsum⟩ :=
   h2 _ _ M.target M.source φ.toRingHom f _ _ M.w
     M.targetSection M.sourceSection M.compatible Q hQ
 change aNP φ.toRingHom (lW A) Q ≤
   weight (lW (A.comap φ)) Q
 rw [hsum,hweight]
 exact eOu h3 h4 f e MO rfl M.w M.w_ne q hq
end
end agO
end
section
namespace Aj
noncomputable section
open Polynomial K1
structure biW (U V:nC) where
 α:Fin 2→K[X]
 β:Fin 2→K[X]
 a :K[X]
 b:K[X]
 a_ne :a≠0
 b_ne :b≠0
 scalar_coprime :G1 a b
 α_primitive :G1 (α 0) (α 1)
 β_primitive :G1 (β 0) (β 1)
 direction :Z4 U V (JO a β) (J9 b α)
end
end Aj
end
