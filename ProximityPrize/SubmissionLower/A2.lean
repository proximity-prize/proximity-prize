import ProximityPrize.SubmissionLower.K
import ProximityPrize.SubmissionLower.B
import ProximityPrize.SubmissionLower.A0
import ProximityPrize.SubmissionLower.L
set_option Elab.async false
open _root_ renaming AlgHom.coe_toRingHom→zlv,AlgHom.toRingHom_eq_coe→ziQ,Algebra→yU,Algebra.algebraMap→cy,Algebra.algebraMap_self_apply→zEi,Algebra.smul_def→Oc,CharP.cast_eq_zero_iff→zX2,CommRing→qJ,DFunLike.congr_fun→Ze,DecidableEq→t7,Disjoint→Mj,Dr.ChamberBox→vj,Dr.capExponents→pz,Dr.dimension→JQ,Field→zc,Filter→Df,Filter.atTop→pG,Filter.eventually_ge_atTop→ZJ,Fin.castSucc→uz,Fin.last→pC,Fin.lastCases→G0,Fin.range_fin_succ→Aa,Fin.sum_univ_eq_sum_range→Ok,Fin.sum_univ_four→zmM,Finite→qy,Finset→nI,Finset.add_sum_erase→zT2,Finset.card_univ→S1,Finset.finite_toSet→WD,Finset.induction_on→Kl,Finset.le_sup→WX,Finset.mem_filter→zO0,Finset.mem_insert_of_mem→ IU,Finset.mem_insert_self→Kc,Finset.mem_univ→vk,Finset.mul_sum→ze,Finset.prod_congr→Dz,Finset.prod_insert→zqX,Finset.range→p7,Finset.single_le_sum→Pc,Finset.sum_add_distrib→zfW,Finset.sum_apply→Zh,Finset.sum_attach→zKD,Finset.sum_congr→qx,Finset.sum_const→Mw,Finset.sum_filter→Np,Finset.sum_insert→Mk,Finset.sum_le_sum→uW
open _root_ renaming Finset.sum_nonneg→zlo,Finset.sum_subset→Wl,Finset.sup_le→X4,Finset.univ→Kv,Finsupp.add_apply→Dv,Finsupp.degree_eq_sum→zFi,Finsupp.filter_apply→zfF,Finsupp.finsetSum_apply→Xu,Finsupp.induction_linear→FK,Finsupp.single→Pk,Finsupp.single_apply→EK,Finsupp.smul_single_one→zrt,Finsupp.tsub_apply→VH,Finsupp.weight→ oy,Finsupp.weight_apply→SW,Finsupp.weight_eq_sum→Fz,Finsupp.weight_single→qG,Finsupp.weight_sub_single_add→Zg,Fintype→ oK,Fintype.card_fin→Pj,Fintype.equivFin→G8,Fintype.ofFinite→Gk,FractionRing→t5,Function.Injective→p9,Function.Surjective→vh,Function.comp_apply→Sd,Function.update→Wm,Ideal→aU,Ideal.IsPrime.comap→zm,Ideal.Quotient.eq_zero_iff_mem→G7,Ideal.Quotient.factorₐ→z5F,Ideal.Quotient.liftₐ→zTA,Ideal.Quotient.mk→mD,Ideal.Quotient.mk_surjective→Et,Ideal.Quotient.mkₐ→Fa,Ideal.comap_comap→Pf,Ideal.comap_isPrime→zG1,Ideal.comap_map_of_bijective→zFA,Ideal.comap_map_of_surjective→zEk,Ideal.comap_mono→Vl,Ideal.coprime_of_no_prime_ge→zQx,Ideal.height_add_one_le_of_lt_of_isPrime→zSK,Ideal.isPrime_map_of_isLocalizationAtPrime→zlD,Ideal.map_isPrime_of_surjective→TI,Ideal.map_map→zf,Ideal.map_span→y5,Ideal.mem_homogeneousCore_of_homogeneous_of_mem→zFp,Ideal.mem_map_of_mem→zh
open _root_ renaming Ideal.mem_span_singleton_self→vH,Ideal.mk_ker→Pr,Ideal.mul_mem_right→zx6,Ideal.mul_top→FU,Ideal.ofList→zE,Ideal.ofList_cons→z2L,Ideal.ofList_singleton→N0,Ideal.primesOver→TZ,Ideal.ringKrullDim_quotient_succ_le_of_lt→X8,Ideal.smul_eq_mul→FV,Ideal.span→lJ,Ideal.span_insert→OJ,Ideal.span_singleton_le_iff_mem→G3,Ideal.span_singleton_prime→zw5,Ideal.subset_span→ Il,Ideal.toIdeal_homogeneousCore_le→zFP,Insert.insert→t8,Irreducible→Sv,IsCoprime→xI,IsDomain→G2,IsFractionRing.injective→xL,IsLeftCancelMulZero.mul_left_cancel_of_ne_zero→zUH,IsLocalRing→PM,IsLocalRing.maximalIdeal→ oD,IsLocalRing.maximalIdeal.isMaximal→zHl,IsLocalization.AtPrime.isUnit_to_map_iff→z7L,IsLocalization.AtPrime.map_eq_maximalIdeal→zNE,IsLocalization.AtPrime.to_map_mem_maximal_iff→zRt,IsLocalization.algebraMap_mem_map_algebraMap_iff→zZS,IsLocalization.exists_mk'_eq→zcf,IsLocalization.isPrime_of_isPrime_disjoint→PD,IsLocalization.lift→QL,IsLocalization.lift_eq→NZ,IsLocalization.map_units→z0j,IsLocalization.mk'→zzm,IsLocalization.mk'_spec→zOg,IsLocalization.orderEmbedding→zRW,IsLocalization.ringHom_ext→zuW,IsLocalization.under_map_of_isPrime_disjoint→ztT,IsNoetherianRing→MS,IsSMulRegular→wY,IsScalarTower.algebraMap_eq→zYY,IsScalarTower.of_algebraMap_eq→zsL,IsUnit→vl,Jq.Represents→PA,LinearEquiv.ofBijective→zD9,LinearMap.ker→uJ,LinearMap.mem_ker→Kz
open _root_ renaming LinearMap.range→Dw,LinearMap.range_domRestrict→zyK,LinearOrder.lift'→zEZ,Localization.AtPrime→Au,Localization.localRingHom_to_map→zMs,Module.Finite→Hw,Module.finrank→G1,Module.finrank_eq_nat_card_basis→zUF,Module.finrank_eq_zero_of_subsingleton→z6g,Module.length→qm,Module.length_eq_add_of_exact→ziu,Module.length_eq_finrank→z1C,Module.length_le_of_injective→zdt,Module.length_le_of_surjective→VS,ModuleCat.of→Kh,MonomialOrder→FR,MonomialOrder.degLex→zwf,MvPolynomial→nX,MvPolynomial.C→nq,MvPolynomial.IsWeightedHomogeneous.mul→JK,MvPolynomial.X→lV,MvPolynomial.affineHilbertFunction→Qy,MvPolynomial.affineHilbertPolynomial→yl,MvPolynomial.algHom_ext→Zf,MvPolynomial.basisRestrictSupport→zzc,MvPolynomial.coeff_eq_zero_of_totalDegree_lt→Xp,MvPolynomial.eval→p5,MvPolynomial.eval_C→FQ,MvPolynomial.eval_X→Gr,MvPolynomial.eval₂→z8,MvPolynomial.eval₂Hom→yB,MvPolynomial.eval₂Hom_C→NW,MvPolynomial.eval₂Hom_X'→Lf,MvPolynomial.eval₂_eq→zMm,MvPolynomial.eventually_eval_affineHilbertPolynomial→zaM,MvPolynomial.hom_eval₂→zUe,MvPolynomial.homogeneousComponent→zyc,MvPolynomial.isWeightedHomogeneous_X→Zi,MvPolynomial.le_weightedTotalDegree→z6P,MvPolynomial.map→t3,MvPolynomial.map_C→KI,MvPolynomial.map_X→G9,MvPolynomial.map_injective→zNV,MvPolynomial.mem_iff_weightedHomogeneousComponent_mem→z1h,MvPolynomial.mem_support_iff→zuk,MvPolynomial.mem_weightedHomogeneousSubmodule→Mz,MvPolynomial.monomial→qz,MvPolynomial.monomial_mul_monomial→zDU
open _root_ renaming MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective→zGE,MvPolynomial.optionEquivLeft→xu,MvPolynomial.optionEquivLeft_coeff_coeff→z9x,MvPolynomial.optionEquivRight→G4,MvPolynomial.pderiv→yQ,MvPolynomial.rename→ IT,MvPolynomial.renameEquiv_apply→zyl,MvPolynomial.rename_X→SC,MvPolynomial.restrictSupport→yJ,MvPolynomial.restrictSupport_eq_span→NI,MvPolynomial.ringHom_ext→Ea,MvPolynomial.support_weightedHomogeneousComponent→z66,MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt→ztH,MvPolynomial.weightedHomogeneousComponent→Ar,MvPolynomial.weightedHomogeneousComponent_eq_self→XG,MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous→zmP,MvPolynomial.weightedHomogeneousComponent_mem→zbF,MvPolynomial.weightedHomogeneousComponent_mem_of_mem→MK,MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported→zSq,MvPolynomial.weightedTotalDegree_mul_le→Eg,MvPolynomial.weightedTotalDegree_pderiv_le_sub→zYB,MvPolynomial.weightedTotalDegree_zero→z4a,MvPolynomial.zeroLocus→VO,Nat.add_le_add→zk,Nat.add_le_add_left→R9,Nat.add_mul→UY,Nat.add_sub_cancel_left→z7K,Nat.add_sub_of_le→GR,Nat.card_coe_set_eq→JM,Nat.card_congr→Nj,Nat.card_eq_fintype_card→XB,Nat.cast_mul→RD,Nat.cast_sum→SU,Nat.le_add_left→Pv,Nat.le_add_right→zi,Nat.le_of_lt_succ→Ef,Nat.lt_succ_of_le→SM,Nat.mul_le_mul_left→qU,Nat.mul_left_comm→WK,Nat.mul_pos→WY,Nat.multichoose_eq→z4m,Nat.multichoose_zero_succ→zGT,Nat.ne_of_gt→SD,Nat.nsmul_eq_mul→UZ,Nat.pos_of_ne_zero→Nq,Nat.sub_add_cancel→zxt,Nat.sub_le_sub_right→zIu,Nat.zero_le→ In
open _root_ renaming Or.inl→Gi,Pi.add_apply→Vq,Pi.single_eq_of_ne→Ye,Polynomial→zR,Polynomial.Bivariate.swap→zd,Polynomial.C→lI,Polynomial.X→ oj,Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd→zff,Polynomial.algebraMap_eq→Zt,Polynomial.coe_eval₂RingHom→x7,Polynomial.coe_mapRingHom→yo,Polynomial.coeff_C_mul_X_pow→zds,Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le→zKB,Polynomial.coeff_map→zg,Polynomial.evalRingHom→qM,Polynomial.eval_C→Te,Polynomial.eval_X→MO,Polynomial.eval_add→zvF,Polynomial.eval₂RingHom→GY,Polynomial.eval₂_C→F9,Polynomial.eval₂_X→zC9,Polynomial.eval₂_map→zem,Polynomial.eval₂_monomial→zFK,Polynomial.exists_mul_add_mul_eq_C_resultant→zKy,Polynomial.finsetSum_coeff→zaW,Polynomial.hasseDeriv→pQ,Polynomial.hasseDeriv_map→zvb,Polynomial.hasseDeriv_monomial→zKa,Polynomial.hom_eval₂→Y4,Polynomial.induction_on'→zCU,Polynomial.isUnit_resultant_iff_isCoprime→zgx,Polynomial.mapRingHom→u8,Polynomial.map_C→sS,Polynomial.map_add→z7,Polynomial.map_dvd→RP,Polynomial.map_id→Xx,Polynomial.map_map→sI,Polynomial.map_monomial→SL,Polynomial.map_mul→v8,Polynomial.map_sum→NY,Polynomial.map_taylor→zla,Polynomial.monomial→t9,Polynomial.natDegree_map_eq_of_injective→Z0,Polynomial.natDegree_map_le→RC,Polynomial.natDegree_modByMonic_lt→Yo,Polynomial.natDegree_sum_le_of_forall_le→UP,Polynomial.preHilbertPoly→zcb,Polynomial.preHilbertPoly_eq_choose_add_sub→zg1
open _root_ renaming Polynomial.ringHom_ext→C5,Polynomial.taylor→wR,PrimeSpectrum→Rm,QuotSMulTop→yL,Ring.ord→LR,RingHom.comap_ker→S2,RingHom.comp_apply→pU,RingHom.congr_fun→t4,RingHom.ext→xW,RingHom.id→LQ,RingHom.ker→sH,RingHom.ker_eq_comap_bot→Vz,RingHom.ker_isPrime→zgL,RingHom.mem_ker→ZK,RingTheory.Sequence.IsWeaklyRegular→P7,Set.disjoint_left→Up,Set.image_image→Vs,Set.image_insert_eq→z6c,Set.image_singleton→Cy,Set.mem_fintype_sum→RJ,Set.mem_insert_iff→zP8,Set.mem_ofPred_eq→Qx,Set.mem_zero→KH,Set.nsmul_mem_nsmul→zfk,Set.pair_comm→Yi,Set.range→Re,Set.range_eq_empty→zwy,Set.singleton_def→zrN,SetLike.exists_of_lt→zxV,Submodule→u9,Submodule.Quotient.mk_eq_zero→ziM,Submodule.add_mem→Ob,Submodule.factor_surjective→zSx,Submodule.ideal_span_singleton_smul→zQT,Submodule.inclusion→zwh,Submodule.inclusion_injective→zaX,Submodule.map_comp→z1U,Submodule.mem_colon_singleton→ztS,Submodule.mem_smul_pointwise_iff_exists→zeT,Submodule.mem_top→z8t,Submodule.quotEquivOfEq→Gn,Submodule.span_le→zKY,Submodule.sum_mem→zo3,Subsingleton→zS,Subtype.ext→pL,Subtype.val→C4,Transcendental→GF,UniqueFactorizationMonoid→LP
open _root_ renaming XT.Exponent→ ov,XT.admissible→HZ,aA5.numerator→Ee,aR.Shape→ ox,aR.Shape.plus→J4,aR.Shape.scale→vi,add_comm→NX,add_le_add→WW,add_right_comm→Kp,add_zero→G6,aqa.Local→t6,baE.localColength→VC,charP_of_injective_ringHom→XJ,congrArg→lz,cu.Equation→v9,dN.GeoField→c9,dN.GeoJets→n5,dN.separant→wB,finsum_eq_sum_of_fintype→zNX,gT.Ambient→ oq,inferInstance→z9,injective_iff_map_eq_zero→Un,inv_mul_cancel₀→Du,isSMulRegular_quotient_iff_mem_of_smul_mem→TH,ite_eq_right→C9,jA.jH→vG,le_add_of_nonneg_right→zA2,le_antisymm→wA,le_min_iff→Xg,le_rfl→th,le_sup_left→Nr,lt_of_le_of_ne→GB,map_add→ oY,map_mul→ oz,map_natCast→Ts,map_ne_zero_iff→Bf,map_pow→vw,map_prod→JW,map_sub→Av,map_sum→u5,map_zero→p6,mem_of_isSMulRegular_quotient_of_smul_mem→Ww,min_le_left→Xo,mul_assoc→uh,mul_comm→ Iw,mul_one→Qw,nonZeroDivisors→Yc,nonZeroDivisors.ne_zero→G5
open _root_ renaming one_mul→xm,one_nsmul→Ml,one_pow→KA,one_smul→ II,ringKrullDim→EP,smul_eq_mul→LO,wH.Lower→ oZ,zP.Exponent→vZ,zero_add→Gj
set_option autoImplicit true
section
set_option maxRecDepth 12000
namespace bzr
noncomputable section
open Polynomial K1 aR aiI gR ProximityPrize.Benchmark
open scoped BigOperators
def line (P:af 4) (S U:ao[X]) :zR ao[X] :=
  z8 lI
    (fun i=>lI (jet S i)+Polynomial.C (jet U i)*oj) P
private theorem bdm (P:af 4) (S U:ao[X]) (c:ao) :
   (line P S U).eval (lI c)=cK P (S+c•U) := by
 change (qM (lI c))
   (z8 lI
     (fun i=>lI (jet S i)+Polynomial.C (jet U i)*oj) P)= _
 rw [zUe]
 have hC: (qM (C c)).comp C=LQ ao[X] :=xW fun f=> by simp
 rw [hC]
 change p5 _ P=p5 (jet (S+c•U)) P
 have heq : (fun i:Fin 4=>(qM (C c))
     (lI (jet S i)+Polynomial.C (jet U i)*oj)) =
     jet (S+c•U) := by
   funext i
   simp only [coe_evalRingHom,eval_mul,Te,MO,jet,oY]
   rw [(pQ i.val).map_smul,Oc,Zt,Iw]
 rw [heq]
private theorem bhI (Q:zR ao[X]) (i j:ℕ) :
   ((zd Q).coeff i).coeff j=(Q.coeff j).coeff i:= by
 induction Q using zCU with
 | add P Q hp hq=>simp [hp,hq]
 | monomial n P =>
   induction P using zCU with
   | add P Q hp hq=>simp only [map_add,Polynomial.coeff_add,hp,hq]
   | monomial m c =>
     rw [Bivariate.swap_monomial_monomial]
     by_cases hi:m=i <;> by_cases hj:n=j <;> simp [Polynomial.coeff_monomial,hi,hj]
private theorem d2V (Q:zR ao[X]) (c:ao) :
  (zd Q).map (qM c)= Q.eval (lI c) := by
 simpa [Polynomial.aeval_def]
  using (Bivariate.aveal_eq_map_swap c Q).symm
private theorem bnl (Q:zR ao[X]) (x :ao) (r :ℕ)
   (h : ∀ c:ao,(oj - C x)^r∣Q.eval (C c)) (j:ℕ) :
   (oj - C x)^r∣Q.coeff j:= by
 let f :ao[X] →+* ao[X] :=(taylorAlgHom x).toRingHom
 let A:= Q.map f
 have heval (c:ao) :A.eval (C c)=wR x (Q.eval (C c)) := by
   change (Q.map f).eval (C c)=f (Q.eval (C c))
   have hC:f (C c)=C c:=taylor_C _ _
   rw [← hC,eval_map,eval₂_at_apply]
   rw [hC]
 have hzero (i:ℕ) (hi:i< r) : (zd A).coeff i=0:= by
   apply eq_zero_of_infinite_isRoot
   have hz (c:ao) : ((zd A).coeff i).eval c=0:= by
     change qM c ((zd A).coeff i)=0
     rw [← zg ,d2V,heval]
     exact X_pow_dvd_iff.mp ((zff _ _ _).mpr (h c)) i hi
   simpa [IsRoot,hz] using (Set.infinite_univ : (Set.univ :Set ao).Infinite)
 apply (zff _ _ _).mp
 apply X_pow_dvd_iff.mpr
 intro i hi
 change (f (Q.coeff j)).coeff i=0
 rw [← zg ,← bhI,hzero i hi,Polynomial.coeff_zero]
private theorem cX8 (Q:zR ao[X]) (A:nI I)
  (x :I→ao) (hx :p9 x) (r :ℕ)
  (h : ∀ i∈A,∀ c:ao,(oj - C (x i))^r∣Q.eval (C c))
  (j:ℕ) (hdeg: (Q.coeff j).natDegree< r*A.card) :Q.coeff j=0:= by
 exact wT.aHG A x hx r (Q.coeff j)
  (fun i hi=>bnl Q (x i) r (h i hi) j) hdeg
end
end bzr
end
section
set_option maxRecDepth 12000
namespace bzr
noncomputable section
open Polynomial K1 aR aiI gR
open scoped BigOperators
private theorem b2g (L:ao[X]) (x :ao) (hx :L.eval x≠0)
   (v :Fin 4→ao) :
   ∃ V:ao[X],V.natDegree≤3 ∧ ∀ i:Fin 4,(jet (L*V) i).eval x=v i:= by
 classical
 let B:=(oj - C x)^4
 have hB:B.Monic:=(monic_X_sub_C x).pow _
 have hdeg:B.natDegree=4 := by simp [B,natDegree_pow]
 have hcop:xI L B:= by
   apply (irreducible_X_sub_C x).coprime_pow_of_not_dvd
   simpa [dvd_iff_isRoot,IsRoot] using hx
 obtain ⟨a,b,hab⟩:=hcop
 let F:=wR (-x) (ofFn 4 v)
 let V:=(a*F) %ₘ B
 have hdiv :B∣L*V-F:= by
   refine ⟨-(b*F+L*((a*F) /ₘ B)),?_⟩
   dsimp only [V]
   rw [modByMonic_eq_sub_mul_div]
   linear_combination F*hab
 have hjet:=(X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero (L*V-F) x 4).mp hdiv
 refine ⟨V,?_,fun i => ?_⟩
 · have hne :B≠1 := by
     intro h
     rw [h,natDegree_one] at hdeg
     omega
   have hsmall:=Yo (a*F) hB hne
   rw [hdeg] at hsmall
   exact Ef hsmall
 · have h:=hjet i.val i.isLt
   rw [Av,eval_sub,sub_eq_zero] at h
   change (pQ i.val (L*V)).eval x=v i
   rw [h,← taylor_coeff,show F=wR (-x) (ofFn 4 v) from rfl,taylor_taylor,
     add_neg_cancel,taylor_zero,ofFn_coeff_eq_val_of_lt v i.isLt]
private theorem bXP (P:Symbol) (v :Fin 4→ao) (j:ℕ) :
   (z8 lI (fun i=>lI (v i)*oj) P).coeff j =
     p5 v (zyc j P) := by
 classical
 rw [zMm,zaW,MvPolynomial.homogeneousComponent_apply]
 change _=yB (LQ _) v _
 rw [u5 ,Np]
 apply qx rfl
 intro m _
 rw [MvPolynomial.eval₂Hom_monomial]
 simp only [Finsupp.prod,mul_pow,Finset.prod_mul_distrib,← vw lI,
   ← JW lI,← oz lI,← uh,Finset.prod_pow_eq_pow_sum,
   zds,RingHom.id_apply,Finsupp.degree_apply]
 split_ifs <;> simp_all
private theorem b7M (P:af 4) (S U:ao[X]) (x :ao) :
    (line P S U).map (qM x) =
      z8 lI (fun i:Fin 4=>lI ((jet U i).eval x) *
        oj) (LY x (Z8 P S)) := by
  let f :=qM x
  let g (i:Fin 4) :ao[X] :=lI (f (jet U i))*oj
  change (u8 f) (z8 lI
    (fun i:Fin 4=>lI (jet S i)+Polynomial.C (jet U i)*oj) P) =
    yB lI g
      (t3 f (z8 nq
        (fun i=>lV i+MvPolynomial.C (jet S i)) P))
  rw [zUe,MvPolynomial.eval₂Hom_map_hom]
  change _=yB (Polynomial.C.comp f) g
    (yB nq
      (fun i=>lV i+MvPolynomial.C (jet S i)) P)
  rw [MvPolynomial.map_eval₂Hom]
  have hl: (u8 f).comp lI=Polynomial.C.comp f :=xW fun p=> by simp
  have hr : (yB (Polynomial.C.comp f) g).comp nq =
      Polynomial.C.comp f :=xW fun p=> by simp
  rw [hl,hr]
  congr 1
  funext i
  simp [g,NX]
private theorem bfX (P:af 4) (S L:ao[X]) (hL:L≠0) (d:ℕ)
    (h : ∀ (V:ao[X]),V.natDegree≤3 → ∀ j<d,(line P S (L*V)).coeff j=0) :
    wU P S d:= by
  intro m hm
  change d≤ m.degree
  by_contra! hlt
  have hz (x :ao) (hx :L.eval x≠0) : ((Z8 P S).coeff m).eval x=0:= by
    let A:=LY x (Z8 P S)
    let Q:=zyc m.degree A
    have hQ:Q=0:= by
      apply (MvPolynomial.homogeneousComponent_isHomogeneous _ _).eq_zero_of_forall_eval_eq_zero
      intro v
      obtain ⟨V,hV,hv⟩:=b2g L x hx v
      have heval :=lz (qM x) (h V hV m.degree hlt)
      rw [p6,← zg ,b7M] at heval
      let along (u:Fin 4→ao) :=
        (z8 lI (fun i=>lI (u i)*oj) A).coeff
          m.degree
      have hdir :=lz along (funext hv)
      have hvanish:along v=0:=hdir.symm.trans heval
      simpa only [along,bXP] using hvanish
    have hcoeff :=lz (fun F:Symbol=>F.coeff m) hQ
    simpa [Q,MvPolynomial.coeff_homogeneousComponent,A,LY,MvPolynomial.coeff_map]
      using hcoeff
  have hzero : (Z8 P S).coeff m=0:= by
    apply eq_zero_of_infinite_isRoot
    refine (finite_setOfPred_isRoot hL).infinite_compl.mono ?_
    intro x hx
    exact hz x hx
  exact MvPolynomial.mem_support_iff.mp hm hzero
end
end bzr
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace aqb
noncomputable section
open K1 cu gT pI Ty Polynomial
def c1 :Prop :=
  ∀ (I:aU oq) (hI:xN I) (f :v9),
    dual I→ Sv f→0<f.natDegree→f.natDegree<p →
    I.comap Co=lJ {f} →
    letI:I.IsPrime :=hI.prime
    let a :=aIW I
    Prime (a (Co f)) ∧ ∃ t,I.map a=lJ {a (Co f),t}
def c2 :Prop :=
  ∀ (I:aU oq) (hI:xN I) (f :v9),
    ¬ dual I→ Sv f→0<f.natDegree→ gY f<p →
    I.comap Co=lJ {f} →
    letI:I.IsPrime :=hI.prime
    let a :=aIW I
    let q:=brm I
    let f' := q (a (Co f))
    p9 (fun x :aRO I=>f' * x) ∧
      (I.map a).map q=lJ {f'}
theorem of_children (h1 :c1) (h2 :c2) :Ty.c3:= by
  intro H P I m r hH hs hy hI hr hrm hhigh ho
  by_cases hmem:Co H∈I
  · obtain ⟨f,g,e,hfac,he,hf,hpos,hdeg,hseed,hcontract,hg⟩ :=
      eHJ hI hH hhigh hmem
    have hpow:O9 I (C (f^e)*P) m:= by
      have hrow:C H*P=C g*(C (f^e)*P) := by
        rw [hfac,oz ,Iw (C (f^e)) (C g),uh]
      apply bB3 hI.prime hg
      rwa [← hrow]
    refine bWc (f :=f) ?_ he hrm hpow
    have :I.IsPrime :=hI.prime
    intro Q n hQ
    by_cases hd:dual I
    · obtain ⟨hprime,t,ht⟩:=h1 I hI f hd hf hpos (hdeg.trans_lt hy) hcontract
      apply (c2C I hd Q n).mpr
      apply a1X hprime ht
      simpa only [oz ,btc] using
        (c2C I hd (C f*Q) (n+1)).mp hQ
    · obtain ⟨hinj,hgen⟩:=h2 I hI f hd hf hpos (hseed.trans_lt hs) hcontract
      apply (c2F I hd Q n).mpr
      apply cDR hgen hinj
      simpa only [oz ,btc] using
        (c2F I hd (C f*Q) (n+1)).mp hQ
  · exact cY8 (by omega) (bB3 hI.prime hmem ho)
end
end aqb
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace baz
noncomputable section
open cu gT pI ac2 aqb
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev Reduction (I:aU oq) :=nX (Fin 2) (agI I)
abbrev Gd (I:aU oq) :=nX (Fin 2) (Tw I)
def akd (I:aU oq) :oq →+* Reduction I :=
 Ih (mD (I.comap qO))
abbrev bdT (I:aU oq) :Submonoid (Reduction I) :=
 (agI I)⁰.map (nq (σ:=Fin 2))
private theorem azW:Jl.toRingHom.comp qO=MvPolynomial.C:= by
 apply Ea
 · simp [qO]
 · intro i
   change Jl (IT (Fin.natAdd 2) (lV i))= _
   rw [SC]
   exact bNE i
theorem a8J {A:Type*} [qJ A] (q:aZ →+* A) (s :aZ) :
   Ih q (qO s)=nq (q s) := by
 change t3 q (Jl (qO s))= _
 rw [show Jl (qO s)=nq s from
     t4 azW s,
   KI]
theorem ar6 (I:aU oq) :vh (akd I) :=
 (MvPolynomial.map_surjective _ Et).comp Jl.surjective
theorem aWS (I:aU oq) :sH (akd I)=azl I:= by
 rw [akd,Ih,← S2 ,MvPolynomial.ker_map,
  ← azW,← zf ,
  zFA Jl.toRingHom Jl.bijective,Pr]
 exact (b57 I).symm
theorem bp5 (I:aU oq) :
  T3 I=(cy (Reduction I) (Gd I)).comp (akd I) := by
 apply xW
 intro z
 change t3 ((cy (agI I) (Tw I)).comp
  (mD (I.comap qO))) (Jl z)= _
 rw [← MvPolynomial.map_map]
 rfl
theorem bey (I:aU oq) :azl I≤I :=
 Ideal.map_le_iff_le_comap.mpr th
private theorem cKR (I:aU oq) [I.IsPrime] :
  Mj (bdT I:Set (Reduction I)) (I.map (akd I) :Set (Reduction I)) := by
 have : (I.comap qO).IsPrime :=zm qO
 rw [Up]
 rintro _ ⟨d,hd,rfl⟩ hm
 obtain ⟨s,rfl⟩:=Et (I:=I.comap qO) d
 have hs :akd I (qO s)=nq (mD (I.comap qO) s) :=
  a8J _ s
 rw [← hs] at hm
 change qO s∈(I.map (akd I)).comap (akd I) at hm
 rw [zEk _ (ar6 I),← Vz ,aWS,
  sup_eq_left.mpr (bey I)] at hm
 exact (G5 hd) (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
theorem aUP (I:aU oq) [I.IsPrime] : (I.map (T3 I)).IsPrime := by
 have : (I.comap qO).IsPrime :=zm qO
 have hp: (I.map (akd I)).IsPrime :=
  TI (ar6 I) (aWS I ▸ bey I)
 rw [bp5,← zf]
 exact PD (bdT I) (Gd I)
  _ hp (cKR I)
theorem aDc (I:aU oq) [I.IsPrime] :
  (I.map (T3 I)).comap (T3 I)=I:= by
 have : (I.comap qO).IsPrime :=zm qO
 have hp: (I.map (akd I)).IsPrime :=
  TI (ar6 I) (aWS I ▸ bey I)
 have hu:=ztT (bdT I)
  (Gd I) hp (cKR I)
 rw [Ideal.under_def] at hu
 rw [bp5,← zf ,← Pf ,hu,
  zEk _ (ar6 I),← Vz ,aWS,
  sup_eq_left.mpr (bey I)]
private theorem enL (I:aU oq) (hI:xN I) (hd : ¬ dual I) :
   azl I ≠ ⊥ := by
 have :I.IsPrime :=hI.prime
 intro hJ
 let S:=aZ⁰.map (nq (σ:=Fin 2))
 let e :=Jl.toRingHom
 have hdisj:Mj (S:Set (nX (Fin 2) aZ)) (I.map e :Set _) := by
   rw [Up]
   rintro _ ⟨s,hs,rfl⟩ h
   rw [← show e (qO s)=nq s from t4 azW s] at h
   change qO s∈(I.map e).comap e at h
   rw [zFA e Jl.bijective] at h
   have hj:qO s∈azl I:= by
     rw [azl,b57]
     exact zh qO h
   have hz :qO s=0:=Ideal.mem_bot.mp (hJ ▸ hj)
   have hinj:p9 qO:=MvPolynomial.rename_injective _ (Fin.natAdd_injective 2 2)
   exact G5 hs (hinj (hz.trans (p6 qO).symm))
 have he :CG=(cy (nX (Fin 2) aZ) vR).comp e := by
   rw [aVL]
   rfl
 have hp: (I.map e).IsPrime := by
   exact TI (f :=e) Jl.surjective (by
     rw [(RingHom.injective_iff_ker_eq_bot e).mp Jl.injective]
     exact bot_le)
 have hprime : (I.map CG).IsPrime := by
   rw [he,← zf]
   exact PD S vR _ hp hdisj
 have :Nontrivial (Lj I) :=Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
 have :=hI.jet_finite
 exact hd Module.finrank_pos
private theorem eaf (I:aU oq) (hI:xN I) (hd : ¬ dual I) :
   (I.map (T3 I)).height≤1 := by
 have :I.IsPrime :=hI.prime
 have : (I.comap qO).IsPrime :=zm qO
 let F:=T3 I
 let J:=I.map F
 have hprime :J.IsPrime :=aUP I
 let E :aU (Gd I) ↪o aU Ambient :=
   (zRW (bdT I) (Gd I)).comp
     (Ideal.orderEmbeddingOfSurjective (akd I) (ar6 I))
 have hE (P:aU (Gd I)) :E P=P.comap F:= by
   change (P.comap (cy (Reduction I) (Gd I))).comap (akd I) =
     P.comap (T3 I)
   rw [Pf ,bp5]
 rw [show (I.map (T3 I)).height=Order.height (⟨J,hprime⟩:Rm _) from
   PrimeSpectrum.height_eq_orderHeight ⟨J,hprime⟩]
 by_contra! hh
 obtain ⟨P,Q,hQP,hPJ⟩:=Order.one_lt_height_iff.mp hh
 have : (E Q.asIdeal).IsPrime :=(hE Q.asIdeal).symm ▸ zG1 F Q.asIdeal
 have : (E P.asIdeal).IsPrime :=(hE P.asIdeal).symm ▸ zG1 F P.asIdeal
 have hQP' : E Q.asIdeal<E P.asIdeal:=E.strictMono (show Q.asIdeal<P.asIdeal from hQP)
 have hPI:E P.asIdeal<I:= by
   have h:=E.strictMono (show P.asIdeal<J from hPJ)
   rwa [hE J,aDc I] at h
 have hQ: (⊥ : aU oq)<E Q.asIdeal:= by
   refine (bot_lt_iff_ne_bot.mpr (enL I hI hd)).trans_le ?_
   rw [hE,show F=T3 I from rfl,bp5,← Pf ,
     ← aWS,Vz]
   exact Vl bot_le
 have hdim:EP oq=4 := by simp [oq,ringKrullDim_eq_zero_of_field]
 have hbad: (5:WithBot ℕ∞)≤4 := calc
   5=((EP (gk I)+1)+1)+1 := by rw [hI.dimension]; decide
   _≤(EP (oq ⧸ E P.asIdeal)+1)+1 :=
     WW (WW (X8 hPI) th) th
   _≤ EP (oq ⧸ E Q.asIdeal)+1 :=
     WW (X8 hQP') th
   _≤ EP (oq ⧸ (⊥ : aU oq)) :=
     X8 hQ
   _=4 :=(RingEquiv.quotientBot oq).ringKrullDim.trans hdim
 exact (by decide : ¬ (5:WithBot ℕ∞)≤4) hbad
theorem ean (I:aU oq) (hI:xN I) (hd : ¬ dual I)
  (hne :I.map (T3 I) ≠ ⊥) :
  ∃ g:Gd I,I.map (T3 I)=lJ {g} := by
 have :I.IsPrime :=hI.prime
 have : (I.comap qO).IsPrime :=zm qO
 have :LP (Tw I) :=PrincipalIdealRing.to_uniqueFactorizationMonoid
 have :LP (Gd I) :=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
 have :=aUP I
 have hlt: (⊥ : aU (Gd I))<I.map (T3 I) :=bot_lt_iff_ne_bot.mpr hne
 have hlo:1≤(I.map (T3 I)).height:= by
  simpa only [Ideal.height_bot,Gj] using zSK hlt
 exact (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
  (wA (eaf I hI hd) hlo)).principal
end
end baz
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace cy1
noncomputable section
open cu gT aqb Polynomial
private def afQ (n:ℕ) :
   zR (nX (Fin n) FX) ≃+* nX (Fin (n+1)) FX :=
 (xu FX (Fin n)).symm.toRingEquiv.trans
   (MvPolynomial.renameEquiv FX (finSuccEquivLast (n:=n)).symm).toRingEquiv
private theorem brx (n:ℕ) :
  afQ n oj=lV (pC n) := by
 change IT _ ((xu FX (Fin n)).symm oj)= _
 simp
private theorem brw (n:ℕ) (x :nX (Fin n) FX) :
   afQ n (C x)=IT uz x := by
 have h: (xu FX (Fin n)).symm (C x) =
     MvPolynomial.rename some x := by
   change (Polynomial.aevalTower (IT some) (lV none)) (C x)= _
   simp
 change IT _ ((xu FX (Fin n)).symm (C x))= _
 have he : (finSuccEquivLast (n:=n)).symm ∘ some=Fin.castSucc:= by
   funext i
   simp
 rw [h,MvPolynomial.rename_rename,he]
private theorem castLE_succ (n:ℕ) :
  (Fin.castLE (Nat.le_succ n) :Fin n→Fin (n+1))=Fin.castSucc:= by
 funext i
 apply Fin.ext
 rfl
private def S5:Jet ≃+* Ambient :=
 (Polynomial.mapEquiv (afQ 2)).trans (afQ 3)
private theorem epG:S5.toRingHom=iJ:= by
 have hroot : (afQ 2).toRingHom=A7:= by
   apply C5
   · intro x
     simpa [A7,pZ,castLE_succ] using brw 2 x
   · simpa [A7,x7] using brx 2
 apply C5
 · intro x
   change afQ 3 ((C x).map (afQ 2).toRingHom)=iJ (C x)
   rw [sS ,brw,hroot]
   simp [iJ,oi,castLE_succ]
 · change afQ 3 (Polynomial.X.map (afQ 2).toRingHom)=iJ oj
   rw [Polynomial.map_X,brx]
   simp [iJ]
attribute [local instance] Polynomial.algebra in
private theorem efr {R T:Type*} [qJ R] [qJ T]
    (P:aU R[X]) [P.IsPrime] (f :R) (hf :P.comap C=lJ {f})
    (b:R[X] →+* T) (hb : ∀ x∉P,vl (b x)) :
    ∃ t,P.map b=lJ {b (C f),t} := by
  let q:=P.comap C
  let Rq:=Au q
  let M:=q.primeCompl.map (C:R →+* R[X])
  let g:R[X] →+* Rq[X] :=cy R[X] Rq[X]
  have :IsLocalization M Rq[X] :=Polynomial.isLocalization q.primeCompl Rq
  let J:=P.map g
  have hdisjoint:Mj (M:Set R[X]) (P:Set R[X]) := by
    rw [Up]
    rintro _ ⟨x,hx,rfl⟩
    exact hx
  let:J.IsPrime :=
    PD M Rq[X] P z9 hdisjoint
  have hqspan:q.map (cy R Rq)=lJ {cy R Rq f} := by
    change (P.comap C).map _ = _
    rw [hf,y5 ,Cy]
  have hm:oD Rq=lJ {cy R Rq f} :=
    (zNE q Rq).symm.trans hqspan
  have hCg:g (C f)=C (cy R Rq f) := by
    change (C f).map (cy R Rq)= _
    rw [sS]
  have hfP:C f∈P:= by
    change f∈P.comap C
    rw [hf]
    exact vH f
  have hcontract :J.comap C=oD Rq:= by
    refine wA (IsLocalRing.le_maximalIdeal_of_isPrime (J.comap C)) ?_
    rw [hm,G3 ,Ideal.mem_comap,← hCg]
    exact zh g hfP
  have hbase : (J.comap C).map C=lJ {g (C f)} := by
    rw [hcontract,hm,y5 ,Cy ,hCg]
  obtain ⟨v,hv⟩ : ∃ v :Rq[X],J=lJ {g (C f),v} := by
    by_cases he :J=(J.comap C).map C
    · exact ⟨0,by rw [he,hbase,Ideal.span_pair_zero]⟩
    · have hmax : (J.comap C).IsMaximal :=
        hcontract.symm ▸ zHl Rq
      obtain ⟨v,_,hv⟩:=Polynomial.exists_monic_span_sup_map_eq Rq J hmax he
      exact ⟨v,by rw [hv,hbase,OJ]⟩
  have hu : ∀ y :M,vl (b y) := by
    rintro ⟨_,x,hx,rfl⟩
    exact hb _ hx
  let l:= QL (S:=Rq[X]) hu
  have hl (x :R[X]) :l (g x)=b x :=NZ hu x
  have hcomp:l.comp g=b:=xW hl
  refine ⟨l v,?_⟩
  calc
    P.map b=J.map l:= by
      change P.map b=(P.map g).map l
      rw [zf ,hcomp]
    _=lJ {b (C f),l v} := by
      rw [hv,y5 ,z6c,Cy ,hl]
theorem proof :aqb.c1 := by
  intro I hI f _ hirr _ _ hcon
  let:I.IsPrime :=hI.prime
  let a :=aIW I
  change Prime (a (Co f)) ∧ ∃ t,I.map a=lJ {a (Co f),t}
  have he :S5.toRingHom.comp (C:v9 →+* Jet)=Co:= by
    rw [epG,Co]
  have heval :S5 (C f)=Co f :=t4 he f
  have hfPrime :Prime f := by
    apply (zw5 hirr.ne_zero).mp
    rw [← hcon]
    infer_instance
  have hfAmbient:Prime (Co f) := by
    rw [← heval]
    exact (MulEquiv.prime_iff S5).mpr (Polynomial.prime_C_iff.mpr hfPrime)
  have hle :lJ {Co f} ≤ I:= by
    rw [G3]
    change f∈I.comap Co
    rw [hcon]
    exact vH f
  have hprime :Prime (a (Co f)) := by
    have hne :a (Co f)≠0:= by
      simpa only [a,p6] using
        (IsLocalization.injective (aBW I) I.primeCompl_le_nonZeroDivisors).ne
          hfAmbient.ne_zero
    apply (zw5 hne).mp
    rw [← Cy ,← y5]
    have : (lJ {Co f}).IsPrime :=
      (zw5 hfAmbient.ne_zero).mpr hfAmbient
    exact zlD I hle
  refine ⟨hprime,?_⟩
  let P:=I.comap S5.toRingHom
  let b:=a.comp S5.toRingHom
  have hp:P.comap C=lJ {f} := by
    change (I.comap S5.toRingHom).comap C= _
    rw [Pf ,he,hcon]
  have hb (x :Jet) (hx :x∉P) :vl (b x) :=
    (z7L (aBW I) I (S5 x)).mpr hx
  obtain ⟨t,ht⟩:=efr P f hp b hb
  refine ⟨t,?_⟩
  have hmap :P.map b=I.map a := by
    change P.map (a.comp S5.toRingHom)= _
    rw [← zf]
    congr 1
    exact Ideal.map_comap_of_surjective S5.toRingHom S5.surjective I
  rw [← hmap,ht]
  change lJ {a (S5 (C f)),t} = _
  rw [heval]
end
end cy1
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace baz
noncomputable section
open K1 cu gT pI ac2 aqb
open MvPolynomial
open scoped Polynomial
private def AV:v9 ≃ₐ[FX] nX (Fin 2) FX[X] :=
 (xu FX (Fin 2)).symm.trans (G4 FX (Fin 2))
private theorem co3 (a :aZ) :AV (lI a)=map lI a := by
 have h:AV.toRingHom.comp (lI:aZ →+* v9) =
    map (lI:FX →+* FX[X]) := by
  apply Ea
  · intro c
    simp [AV,optionEquivLeft_symm_C_C]
  · intro i
    simp [AV,optionEquivLeft_symm_C_X]
 exact t4 h a
private theorem bNH :AV oj=C (oj:FX[X]) := by
 simp [AV,optionEquivLeft_symm_X]
private theorem bNI (f :v9) (j:ℕ) (d:Fin 2 →₀ ℕ) :
  ((AV f).coeff d).coeff j=(f.coeff j).coeff d:= by
 change ((G4 FX (Fin 2) ((xu FX (Fin 2)).symm f)).coeff d).coeff j= _
 rw [optionEquivRight_coeff_coeff,← z9x]
 simp
private theorem goG (f :v9) :
  (AV f).totalDegree≤Ty.gY f := by
 rw [totalDegree,Finset.sup_le_iff]
 intro d hd
 obtain ⟨j,hj⟩:=Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hd)
 rw [Polynomial.mem_support_iff,bNI,← zuk] at hj
 have hle :=le_totalDegree hj
 exact hle.trans (WX (f := fun j=>(f.coeff j).totalDegree)
  (Polynomial.mem_support_iff.mpr (fun hz=>MvPolynomial.mem_support_iff.mp hj (by simp [hz]))))
private def aoB:FX[X] →+* aZ :=
 GY C (lV 0)
private theorem eHS:qO.comp aoB=F7:= by
 apply C5
 · intro a
   simp [aoB,F7,qO]
 · simp [aoB,F7,qO]
private theorem gt0 {A:Type*} [qJ A] (q:aZ →+* A) (f :v9) :
    Ih q (Co f)=map (q.comp aoB) (AV f) := by
  have hs : (Ih q).comp (oi.comp pZ) =
      t3 (q.comp nq) := by
    apply Ea
    · intro c
      simp [oi,pZ,Ih]
    · intro i
      simp only [pU,oi,pZ,ziQ,
        zlv,SC,G9]
      exact bOg q i
  have ho: (Ih q).comp Co =
      (map (q.comp aoB)).comp AV.toRingHom:= by
    apply C5
    · intro a
      simp only [pU,btc,iJ,x7,
        F9]
      change Ih q (oi (A7 (lI a))) =
        map (q.comp aoB) (AV (lI a))
      rw [co3,map_map]
      have hc: (q.comp aoB).comp (lI:FX →+* FX[X])=q.comp C:= by
        ext c
        simp [aoB]
      rw [hc]
      simpa only [pU,A7,x7,F9] using
        t4 hs a
    · simp only [pU,btc,iJ,x7,
        F9]
      change Ih q (oi (A7 oj)) =
        map (q.comp aoB) (AV oj)
      rw [bNH,KI]
      simp only [A7,x7,zC9,oi,
        ziQ,zlv,SC,
        pU,aoB]
      rw [show Fin.castLE (by decide :3≤4) (2 :Fin 3)=Fin.natAdd 2 (0:Fin 2) from rfl]
      exact bwR q 0
  exact t4 ho f
private theorem bJ4 (I:aU oq) (hI:xN I) :
  p9 ((avd I).comp aoB) := by
 have :I.IsPrime :=hI.prime
 have : (I.comap qO).IsPrime :=zm qO
 refine (xL (agI I) (Tw I)).comp ?_
 change p9 ((mD (I.comap qO)).comp aoB)
 rw [Un]
 intro f hf
 have hm:aoB f∈I.comap qO:=Ideal.Quotient.eq_zero_iff_mem.mp hf
 change qO (aoB f)∈I at hm
 rw [← pU,eHS] at hm
 exact (Un _).mp hI.ordinate_dominant f
  (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
theorem separant (I:aU oq) (hI:xN I) (f :v9) (hf :f≠0)
   (hdeg:Ty.gY f<p) (hcontract :I.comap Co=lJ {f}) :
   ∃ i:Fin 2,yQ i (T3 I (Co f))∉I.map (T3 I) := by
 have :I.IsPrime :=hI.prime
 have : (I.comap qO).IsPrime :=zm qO
 let F:=T3 I
 let P:=I.map F
 have hP:P.IsPrime :=aUP I
 let v :=AV f
 let e :=(avd I).comp aoB
 have hv :v≠0:=Bf AV AV.injective |>.mpr hf
 have hfe (a :v9) :F (Co a)=map e (AV a) :=
   gt0 (avd I) a
 have hfI:Co f∈I:= by
   change f∈I.comap Co
   rw [hcontract]
   exact vH f
 have hvars :v.vars.Nonempty := by
   by_contra! h
   have hc:=vars_eq_empty_iff_eq_C.mp h
   have hn:v.coeff 0≠0:= fun hz=>hv (by rw [hc,hz,p6])
   have hu:vl (F (Co f)) := by
     rw [hfe f,← show v=AV f from rfl,hc,KI]
     exact (isUnit_iff_ne_zero.mpr ((Bf e (bJ4 I hI)).mpr hn)).map C
   exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ (zh F hfI) hu)
 obtain ⟨i,hi⟩:=hvars
 have hi' : 0<v.degreeOf i:=Nq (mem_vars_iff_degreeOf_ne_zero.mp hi)
 have hlt:v.degreeOf i<p :=
   ((degreeOf_le_totalDegree v i).trans (goG f)).trans_lt hdeg
 let:CharP FX p:=XJ jz.injective p
 let:CharP FX[X] p :=
   XJ (Polynomial.C_injective (R:=FX)) p
 have hcast: (v.degreeOf i:FX[X])≠0:= by
   intro h
   exact (not_le_of_gt hlt) (Nat.le_of_dvd hi' ((zX2 _ _ _).mp h))
 have hn:=pderiv_ne_zero_of_natCast_ne_zero i v hcast
 have hb:=degreeOf_pderiv_le_sub_one i v
 let g:=AV.symm (yQ i v)
 have hg:AV g=yQ i v :=AV.apply_symm_apply _
 refine ⟨i,?_⟩
 intro hm
 change yQ i (F (Co f))∈P at hm
 rw [hfe,show AV f=v from rfl,pderiv_map,← hg,← hfe] at hm
 change Co g∈P.comap F at hm
 rw [aDc I] at hm
 change g∈I.comap Co at hm
 rw [hcontract,Ideal.mem_span_singleton] at hm
 obtain ⟨k,hk⟩:=hm
 have heq :yQ i v=v*AV k := by simpa only [hk,oz] using hg.symm
 have hkn:AV k≠0:= fun hz=>hn (by rw [heq,hz,mul_zero])
 rw [heq,degreeOf_mul_eq hv hkn] at hb
 omega
end
end baz
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace baz
noncomputable section
open cu gT pI ac2 aqb
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem proof :aqb.c2 := by
 intro I hI f hd hf _ hdeg hcontract
 let:I.IsPrime :=hI.prime
 let: (I.comap qO).IsPrime :=zm qO
 dsimp only
 let a :=aIW I
 letI:qJ (aRO I) :=Ideal.Quotient.commRing ((azl I).map a)
 let q:=brm I
 let φ:=q.comp a
 let F:=T3 I
 let P:=I.map F
 have hF:F=(cy (Reduction I) (Gd I)).comp (akd I) :=
   bp5 I
 have hfi:Co f∈I:= by
   change f∈I.comap Co
   rw [hcontract]
   exact vH f
 have hfe :F (Co f)∈P:=zh F hfi
 obtain ⟨i,hi⟩:=separant I hI f hf.ne_zero hdeg hcontract
 have hnonzero :F (Co f)≠0:= by
   intro hz
   apply hi
   rw [hz,p6]
   exact P.zero_mem
 have hP:P ≠ ⊥ := fun he=>hnonzero (Ideal.mem_bot.mp (he ▸ hfe))
 obtain ⟨g,hg⟩:=ean I hI hd hP
 change P=lJ {g} at hg
 obtain ⟨b,hb⟩:g∣F (Co f) :=Ideal.mem_span_singleton.mp (hg ▸ hfe)
 have hbP:b∉P:= by
   intro h
   apply hi
   change yQ i (F (Co f))∈P
   rw [hb,MvPolynomial.pderiv_mul]
   have hgP:g∈P:=hg.symm ▸ vH g
   exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_right _ hgP)
 have : (azl I).IsPrime := by
   rw [← aWS]
   exact zgL _
 have : ((azl I).map a).IsPrime :=
   zlD (S:=aBW I) I (bey I)
 have :G2 (aRO I) :=Ideal.Quotient.isDomain _
 have hker :sH φ=azl I:= by
   change sH ((mD ((azl I).map a)).comp a)= _
   rw [← S2 ,Pr]
   exact Ideal.under_map_of_isLocalizationAtPrime (S:=aBW I) I (bey I)
 have hf' : φ (Co f)≠0:= by
   intro hzero
   have hm:=RingHom.mem_ker.mpr hzero
   rw [hker,← aWS] at hm
   exact hnonzero (by rw [hF,pU,RingHom.mem_ker.mp hm,p6])
 change p9 (fun x :aRO I=>φ (Co f)*x) ∧
   (I.map a).map q=lJ {φ (Co f)}
 refine ⟨fun _ _ h=>mul_left_cancel₀ hf' h,?_⟩
 have hunit (x :oq) (hx :x∉I) :vl (φ x) :=
   ((z7L (aBW I) I x).mpr hx).map q
 let φ₀:Reduction I →+* aRO I :=
   (akd I).liftOfSurjective (ar6 I) ⟨φ,by rw [hker,aWS]⟩
 have hφ₀ (x :oq) :φ₀ (akd I x)=φ x :=
   RingHom.liftOfSurjective_comp_apply _ _ _ _
 have hu (s :bdT I) :vl (φ₀ s) := by
   obtain ⟨d,hd,hds⟩:=s.property
   obtain ⟨y,rfl⟩:=Et (I:=I.comap qO) d
   have hs : (s :Reduction I)=akd I (qO y) := by
     rw [← hds,akd,a8J]
   rw [hs,hφ₀]
   exact hunit _ (fun hy=>G5 hd (Ideal.Quotient.eq_zero_iff_mem.mpr hy))
 let l:= QL (S:=Gd I) (P:=aRO I) hu
 have hl (y :oq) :l (F y)=φ y := by
   rw [hF,pU]
   exact (NZ (S:=Gd I) (P:=aRO I) hu _).trans (hφ₀ y)
 have hbunit :vl (l b) := by
   obtain ⟨n,s,hs⟩:=zcf (bdT I) b
   obtain ⟨x,rfl⟩:=ar6 I n
   have hx :x∉I:= by
     intro h
     apply hbP
     rw [← hs,IsLocalization.mk'_mem_iff]
     have hfx :=zh F h
     change F x∈P at hfx
     rwa [hF,pU] at hfx
   have heq :l b*l (cy (Reduction I) (Gd I) s)=φ x := by
     rw [← oz ,← hs,zOg]
     exact (lz l (t4 hF x).symm).trans (hl x)
   exact isUnit_of_mul_isUnit_left (heq.symm ▸ hunit x hx)
 have hφ:l.comp F=φ:=xW hl
 rw [zf ,show q.comp a=l.comp F from hφ.symm,← zf]
 change P.map l= _
 rw [hg,y5 ,Cy ,← hl,hb,oz ,
   Ideal.span_singleton_mul_right_unit hbunit]
end
end baz
end
section
namespace as7
noncomputable section
open dN XT Jq MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
abbrev y8:=ℕ×GG
def Uf (a :y8) :jJ :=
 Finsupp.equivFunOnFinite.symm (Fin.snoc a.2 a.1)
def bqO (t:jJ) :y8 :=
 (t (pC 4),fun i=>t i.castSucc)
@[simp] theorem b9z (a :y8) (i:Fin 4) :
   Uf a i.castSucc=a.2 i:= by simp [Uf]
@[simp] theorem bsP (a :y8) :Uf a (pC 4)=a.1 := by
  simp only [Uf,Finsupp.coe_equivFunOnFinite_symm,Fin.snoc_last]
theorem c06 (a v :y8) :Uf (a+v)=Uf a+Uf v := by
 ext j
 refine G0 ?_ (fun i => ?_) j
 · simp only [bsP,Dv,Prod.fst_add]
 · simp
@[simp] theorem eEe (t:jJ) :Uf (bqO t)=t:= by
  ext j
  refine G0 ?_ (fun i => ?_) j
  · exact bsP _
  · exact b9z _ _
def advance (i:Fin 4) :y8:=(0,Pi.single i 1)
@[simp] theorem eEd (i:Fin 4) :
    Uf (advance i)=zY i.castSucc:= by
  ext j
  refine G0 ?_ (fun k => ?_) j
  · rw [bsP,zY,EK,C9 (Fin.castSucc_ne_last i)]
    rfl
  · by_cases he :i=k <;> simp [advance,zY,he,eq_comm]
def aFa (A:Fin 4→Set ov) (B:Set ov) :Fin 5→Set Exponent :=
 Fin.snoc A B
@[simp] theorem bxc (A:Fin 4→Set ov) (B:Set ov) :
   aFa A B (pC 4)=B:= by simp only [aFa,Fin.snoc_last]
@[simp] theorem crV (A:Fin 4→Set ov) (B:Set ov) (i:Fin 4) :
   aFa A B i.castSucc=A i:=Fin.snoc_castSucc _ _ _
abbrev Generator (A:Fin 4→Set ov) (B:Set ov) :=
 (j:Fin 5)×aFa A B j
abbrev Gl (A:Fin 4→Set ov) (B:Set ov) :=
 nX (Generator A B) c9
abbrev slot (A:Fin 4→Set ov) (B:Set ov) :Generator A B→Fin 5 :=
 Sigma.fst
theorem cR5 {A:Fin 4→Set ov} {B:Set ov}
  (hAB:HZ A B) :qy (Generator A B) := by
 have (j:Fin 5) :qy (aFa A B j) := by
  apply Set.Finite.to_subtype
  refine G0 ?_ (fun i => ?_) j
  · simpa only [bxc] using hAB.2.1
  · simpa only [crV] using (hAB.1 i).1
 infer_instance
def ew (A:Fin 4→Set ov) (B:Set ov) :Gl A B →ₐ[c9] GeoJets :=
 aeval fun v=>qz v.2.val 1
def xJ (A:Fin 4→Set ov) (B:Set ov)
    (J:aU n5) :aU (Gl A B) :=
  ((J.comap (ew A B)).homogeneousCore (dO (slot A B))).toIdeal
def P9 {σ:Type} (s :σ→Fin 5) (J:aU (nX σ c9))
    (a :y8) :ℝ :=
  KQ s J (Uf a)
def gI (dirs :List (Fin 4)) (H :y8→ℝ) (a :y8) :ℝ :=
 afK dirs 1 (fun w=>H (a.1,w)) a.2
end
end as7
end
section
namespace as7
noncomputable section
open dN WI Jq MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem a4I {σ:Type} [qy σ] (s :σ→Fin 5)
    (J:aU (nX σ c9)) (hJ:J.IsHomogeneous (dO s))
    (e :jJ) (g:nX σ c9) (hg:g∈dO s e) :
    (J ⊔ lJ {g}).IsHomogeneous (dO s) ∧
      ∀ t:jJ,KQ s (J ⊔ lJ {g}) (t+e) +
        KQ s (J.colon {g}) t=KQ s J (t+e) := by
  have hspan: (lJ {g}).IsHomogeneous (dO s) :=
    Ideal.homogeneous_span _ _ (by
      intro x hx
      obtain rfl :x=g:=hx
      exact ⟨e,hg⟩)
  refine ⟨hJ.sup hspan,?_⟩
  intro t
  let K:=J ⊔ lJ {g}
  let A:=J.colon {g}
  let q:=z5F c9 (show J≤K from Nr)
  let cut:aPz s J (t+e) →ₗ[c9] aPz s K (t+e) :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y=> by
      obtain ⟨b,hb,hby⟩:=y.property
      exact ⟨b,hb,by simpa [q] using lz q hby⟩
  have hsurj:vh cut:= by
    intro y
    obtain ⟨b,hb,hby⟩:=y.property
    exact ⟨⟨mD J b,⟨b,hb,rfl⟩⟩,pL (by simpa [cut,q] using hby)⟩
  let mu:=(Vp J g).restrictScalars c9
  let emb:aPz s A t →ₗ[c9] aPz s J (t+e) :=
    (mu.domRestrict _).codRestrict _ fun y=> by
      obtain ⟨b,hb,hby⟩:=y.property
      have hbg:b*g∈dO s (t+e) :=
        JK hb hg
      refine ⟨b*g,hbg,?_⟩
      change mD J (b*g)=mu y.val
      change mD A b=y.val at hby
      rw [← hby]
      exact (azY J g b).symm
  have hInj:p9 emb:= fun y z h =>
    pL (aPy J g (lz C4 h))
  have hker :uJ cut=Dw emb:= by
    ext y
    obtain ⟨b,hb,hby⟩:=y.property
    have hy :y=⟨mD J b,⟨b,hb,rfl⟩⟩:=pL hby.symm
    rw [hy,Kz ,LinearMap.mem_range]
    constructor
    · intro hz
      have hkb:b∈K:= by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa [cut,q] using lz C4 hz
      obtain ⟨a,ha,c,hc,hac⟩:=Submodule.mem_sup.mp hkb
      obtain ⟨d,rfl⟩:=Ideal.mem_span_singleton'.mp hc
      let m:=Ar (jT s) t d
      have hm:m∈dO s t:=zbF _ _ _
      have ha' := MK _ _ hJ ha (t+e)
      have hb' : b.IsWeightedHomogeneous (jT s) (t+e) :=hb
      have hdecomp:=lz (Ar (jT s) (t+e)) hac
      rw [oY ,bDb s hg,XG hb'] at hdecomp
      refine ⟨⟨mD A m,⟨m,hm,rfl⟩⟩,pL ?_⟩
      change Vp J g (mD A m)=mD J b
      rw [azY,← hdecomp,oY ,Ideal.Quotient.eq_zero_iff_mem.mpr ha',Gj]
    · rintro ⟨z,hz⟩
      obtain ⟨a,_,haz⟩:=z.property
      apply pL
      change mD K b=0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm:a*g∈K :=
        Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a,rfl⟩)
      have he :=lz C4 hz
      change mu z.val=mD J b at he
      rw [← haz] at he
      change Vp J g (mD A a)=mD J b at he
      rw [azY,Ideal.Quotient.eq] at he
      have hsub:a*g-(a*g - b)∈K:=K.sub_mem hm ((show J≤K from Nr) he)
      rwa [sub_sub_cancel] at hsub
  have hrank :=cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,hker,LinearMap.finrank_range_of_inj hInj] at hrank
  exact hrank
end
end as7
end
section
namespace as7
noncomputable section
open dN XT Jq MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {A:Fin 4→Set ov} {B:Set ov}
theorem aIt (J:aU n5) :
   (xJ A B J).IsHomogeneous (dO (slot A B)) :=
 ((J.comap (ew A B)).homogeneousCore (dO (slot A B))).isHomogeneous
theorem cXy {J K:aU n5} (h:J≤K) :
  xJ A B J≤xJ A B K :=
 Ideal.homogeneousCore_mono _ (Vl h)
theorem bI8 {J:aU n5} {g:Gl A B} {t:jJ}
   (hg:g∈dO (slot A B) t) :g∈xJ A B J↔ew A B g∈J:= by
 constructor
 · intro h
   exact zFP (dO (slot A B)) (J.comap (ew A B)) h
 · intro h
   exact zFp ⟨t,hg⟩ h
theorem bZt {J K:aU n5} (hJK:J≤K) {g:Gl A B} {t:jJ}
  (hg:g∈dO (slot A B) t) (h:ew A B g∈K) :
  xJ A B J ⊔ lJ {g} ≤ xJ A B K :=
 sup_le (cXy hJK) ((G3 _).mpr
  ((bI8 hg).mpr h))
theorem b7A {J K:aU n5} {g:Gl A B} {t:jJ}
    (hg:g∈dO (slot A B) t)
    (h : ∀ x :n5 ,x*ew A B g∈J↔x∈K) :
    (xJ A B J).colon {g} = xJ A B K:= by
  have hc: ((xJ A B J).colon {g}).IsHomogeneous (dO (slot A B)) := by
    intro v a ha
    rw [ztS,LO] at ha ⊢
    have hp: (DirectSum.decompose (dO (slot A B)) a v :Gl A B) =
        Ar (jT (slot A B)) v a :=
      weightedDecomposition.decompose'_apply c9 (jT (slot A B)) a v
    rw [hp,← bDb (slot A B) hg a v]
    exact MK _ _ (aIt J) ha _
  ext a
  rw [z1h _ _ hc,
    z1h _ _ (aIt K)]
  apply forall_congr'
  intro v
  let z :=Ar (jT (slot A B)) v a
  have hz :z∈dO (slot A B) v :=zbF _ _ _
  have hzg:z*g∈dO (slot A B) (v+t) :=JK hz hg
  change z∈(xJ A B J).colon {g} ↔ z∈xJ A B K
  rw [ztS,LO,bI8 hzg,
    bI8 hz,oz ,h]
theorem a3P (j:Fin 5) (f :n5)
   (hf : (f.support :Set ov)⊆aFa A B j) :
   ∃ g:Gl A B,g∈dO (slot A B) (zY j)∧ew A B g=f := by
 classical
 let gen (m:f.support) :Generator A B:=⟨j,⟨m,hf m.property⟩⟩
 refine ⟨∑ m:f.support,C (f.coeff m)*lV (gen m),?_,?_⟩
 · apply zo3
   intro m _
   exact (Zi c9 (jT (slot A B)) (gen m)).C_mul _
 · simp only [u5 ,oz ,ew,aeval_C,algebraMap_eq,aeval_X,
     C_mul_monomial,Qw ,gen]
   rw [Finset.sum_coe_sort f.support (fun m=>qz m (f.coeff m))]
   exact f.support_sum_monomial_coeff
theorem cNw (hAB:HZ A B) (f :n5) :
    ∃ t:jJ,∃ g:Gl A B,g∈dO (slot A B) t∧ew A B g=f := by
  let j:=pC 4
  let u:Generator A B:=⟨j,⟨0,by simpa only [j,bxc] using hAB.2.2.1⟩⟩
  let v (i:Fin 4) :Generator A B :=
    ⟨j,⟨Pk i 1,by simpa only [j,bxc] using hAB.2.2.2 i⟩⟩
  have hu:ew A B (lV u)=1 := by simp [ew,u]
  have hv (i:Fin 4) :ew A B (lV (v i))=lV i:= by
    rw [ew,aeval_X]
    rfl
  have hex :
      ∃ n:ℕ,∃ g:Gl A B,
        g∈dO (slot A B) (n•zY j)∧ew A B g=f := by
    induction f using MvPolynomial.induction_on with
    | C r =>
        refine ⟨0,C r,?_,by simp [ew]⟩
        simpa only [Mz ,zero_nsmul] using isWeightedHomogeneous_C (jT (slot A B)) r
    | add p q hp hq =>
        obtain ⟨n,g,hg,hgm⟩:=hp
        obtain ⟨m,h,hh,hhm⟩:=hq
        let x :Gl A B:=lV u
        have hx :x.IsWeightedHomogeneous (jT (slot A B)) (zY j) :=
          Zi c9 _ _
        refine ⟨n+m,g*x^m+h*x^n,Ob _ ?_ ?_,?_⟩
        · simpa only [Mz ,add_nsmul] using JK hg (hx.pow m)
        · simpa only [Mz ,add_nsmul,Nat.add_comm n m] using JK hh (hx.pow n)
        · simp [x,hu,hgm,hhm]
    | mul_X p i hp =>
        obtain ⟨n,g,hg,hgm⟩:=hp
        have hx : (lV (v i) :Gl A B).IsWeightedHomogeneous
            (jT (slot A B)) (zY j) :=Zi c9 _ _
        refine ⟨n+1,g*lV (v i),?_,by rw [oz ,hgm,hv]⟩
        simpa only [Mz ,add_nsmul,Ml] using JK hg hx
  obtain ⟨n,g,hg,hm⟩:=hex
  exact ⟨_,g,hg,hm⟩
abbrev cut (P:aU n5) (f :n5) :aU GeoJets :=P ⊔ lJ {f}
theorem bZu (P:aU n5) (f :n5) :f∈cut P f :=
 (le_sup_right:lJ {f} ≤ cut P f) (vH _)
theorem dS6 (P:aU n5) (f :n5) :cut P (f^2)≤ cut P f := by
 refine sup_le Nr ((G3 _).mpr ?_)
 exact (pow_two f).symm ▸ (cut P f).mul_mem_right f (bZu P f)
theorem bwV {P:aU n5} {f :n5} (hp:P.IsPrime) (hf :f∉P)
   (a :n5) :a*f∈cut P (f^2)↔a∈cut P f := by
 constructor
 · intro ha
   obtain ⟨x,hx,y,hy,hxy⟩:=Submodule.mem_sup.mp ha
   obtain ⟨c,hc⟩:=Ideal.mem_span_singleton'.mp hy
   have he : (a - c*f)*f=x := by
     rw [sub_mul,← hxy,← hc]
     ring
   have hm:a - c*f∈P:=(hp.mem_or_mem (he.symm ▸ hx)).resolve_right hf
   exact Submodule.mem_sup.mpr
     ⟨a - c*f,hm,c*f,Ideal.mem_span_singleton'.mpr ⟨c,rfl⟩,sub_add_cancel _ _⟩
 · intro ha
   obtain ⟨x,hx,y,hy,hxy⟩:=Submodule.mem_sup.mp ha
   obtain ⟨c,rfl⟩:=Ideal.mem_span_singleton'.mp hy
   exact Submodule.mem_sup.mpr ⟨x*f,P.mul_mem_right f hx,c*f*f,
     Ideal.mem_span_singleton'.mpr ⟨c,by ring⟩,by rw [← add_mul,hxy]⟩
def intersection (Q:nI (aU n5)) :aU GeoJets := Q.inf id
theorem gpL {I q:aU n5} {Q:nI (aU n5)}
  (hq:I.IsMinimalPrime q) (hQ : ∀ r∈Q,I.IsMinimalPrime r) (hn:q∉Q) :
  ∃ f∈intersection Q,f∉q:= by
 apply SetLike.not_le_iff_exists.mp
 intro hle
 obtain ⟨r,hr,hrq⟩:=hq.isPrime.inf_le'.mp hle
 have he :r=q:=wA hrq (hq.2 (hQ r hr).1 hrq)
 exact hn (he ▸ hr)
theorem eoX (q:aU n5) (Q:nI (aU n5))
  [t7 (aU n5)] :intersection (t8 q Q)=q ⊓ intersection Q:= by
 simp [intersection]
theorem gpP {q J:aU n5} {f :n5}
   (hq:q.IsPrime) (hf :f∉q) (hJ:f∈J) (a :n5) :
   a*f∈q ⊓ J↔a∈q:= by
 constructor
 · intro h
   exact (hq.mem_or_mem ((Ideal.mem_inf.mp h).1)).resolve_right hf
 · intro h
   exact Ideal.mem_inf.mpr ⟨q.mul_mem_right f h,J.mul_mem_left a hJ⟩
end
end as7
end
section
namespace as7
noncomputable section
open dN XT Jq MvPolynomial Filter
open scoped BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 :Prop :=
  ∀ {σ:Type} [qy σ] (s :σ→Fin 5) (I J:aU (nX σ c9)),
    I.IsHomogeneous (dO s)→J.IsHomogeneous (dO s)→ I≤J →
      ∀ k :ℕ,∀ᶠ a in (pG:Df y8),
        0≤gI (acC k) (fun x=>P9 s I x-P9 s J x) a
def c2 :Prop :=
  ∀ (A:Fin 4→Set ov) (B:Set ov),HZ A B →
    ∀ (P:aU n5) (a :y8),
      P9 (slot A B) (xJ A B P) a=lO A B P a.1 a.2
private theorem bEf (i:Fin 4) (dirs :List (Fin 4)) (H :y8→ℝ) (a :y8) :
 gI (i :: dirs) H a=gI dirs (fun x=>H (x+advance i) - H x) a :=rfl
private theorem b0G (dirs :List (Fin 4)) (H K:y8→ℝ) (a :y8) :
    gI dirs (fun x=>H x - K x) a=gI dirs H a - gI dirs K a := by
  induction dirs generalizing H K with
  | nil=>rfl
  | cons i dirs ih =>
      simp only [bEf]
      rw [show (fun x=>(H (x+advance i) - K (x+advance i))-(H x - K x)) =
        (fun x=>(H (x+advance i) - H x)-(K (x+advance i) - K x)) by
          funext x; ring]
      exact ih _ _
private theorem b0F (dirs :List (Fin 4)) (H :y8→ℝ) (a v :y8) :
   gI dirs (fun x=>H (x+v)) a=gI dirs H (a+v) := by
 induction dirs generalizing H with
 | nil=>rfl
 | cons i dirs ih =>
    simp only [bEf,Kp _ (advance i) v]
    exact ih (fun x=>H (x+advance i) - H x)
private theorem dWX (dirs :List (Fin 4)) (a :y8) :
   gI dirs (fun _=>0) a=0:= by
 induction dirs with
 | nil=>rfl
 | cons i dirs ih=>simpa only [bEf,sub_self] using ih
private theorem auS {F:y8→Prop} (v :y8)
  (h : ∀ᶠ a in pG,F a) : ∀ᶠ a in pG,F (a+v) := by
 obtain ⟨u,hu⟩:=eventually_atTop.mp h
 exact eventually_atTop.mpr ⟨u,fun a ha=>hu (a+v)
  (ha.trans (zA2 zero_le))⟩
private theorem d3A {F:y8→Prop} (v :y8)
  (h : ∀ᶠ a in pG,F (a+v)) : ∀ᶠ a in pG,F a := by
 obtain ⟨u,hu⟩:=eventually_atTop.mp h
 refine eventually_atTop.mpr ⟨u+v,fun a ha => ?_⟩
 obtain ⟨b,rfl⟩:=exists_add_of_le ha
 have hb:=hu (u+b) (zA2 zero_le)
 rwa [Kp] at hb
private theorem c0y (hr :c2) {A:Fin 4→Set ov} {B:Set ov}
   (hAB:HZ A B) {P:aU n5} {k :ℕ} {d:ℝ}
   (hd:aAV A B P k d) :
   ∀ᶠ a in (pG:Df y8),
     gI (acC k) (P9 (slot A B) (xJ A B P)) a=d:= by
 obtain ⟨N,hN⟩:=hd
 refine eventually_atTop.mpr ⟨(N,fun _=>N),fun a ha => ?_⟩
 have he :P9 (slot A B) (xJ A B P)=fun x=>lO A B P x.1 x.2 :=
   funext (hr A B hAB P)
 rw [he,gI]
 simpa only [Nat.cast_one,KA,xm] using hN a.1 a.2 1 ha.1 ha.2
private theorem fS0 {σ:Type} (s :σ→Fin 5) :
  P9 s (⊤ : aU (nX σ c9))=fun _=>0:= by
 funext a
 have :zS (nX σ c9 ⧸ (⊤ : aU (nX σ c9))) :=
  (Ideal.Quotient.subsingleton_iff).mpr rfl
 simp [P9,KQ,z6g]
private theorem ev2 (A:Fin 4→Set ov) (B:Set ov) :
  xJ A B (⊤ : aU n5) = ⊤ := by
 rw [xJ,show (⊤ : aU n5).comap (ew A B) = ⊤ from Ideal.comap_top]
 exact (show (⊤ : aU (Gl A B)).IsHomogeneous (dO (slot A B)) from
  fun _ _ _=>z8t).toIdeal_homogeneousCore_eq_self
private theorem cKF (hpos :c1) {σ:Type} [qy σ]
    (s :σ→Fin 5) {I J:aU (nX σ c9)}
    (hI:I.IsHomogeneous (dO s)) (hJ:J.IsHomogeneous (dO s)) (hIJ:I≤J) (k :ℕ) :
    ∀ᶠ a in (pG:Df y8),
      gI (acC k) (P9 s J) a ≤
        gI (acC k) (P9 s I) a := by
  filter_upwards [hpos s I J hI hJ hIJ k] with a ha
  rw [b0G] at ha
  exact sub_nonneg.mp ha
private theorem wD (hpos :c1) {σ:Type} [qy σ] (s :σ→Fin 5)
    {I J L:aU (nX σ c9)}
    (hI:I.IsHomogeneous (dO s)) (hJ:J.IsHomogeneous (dO s))
    (v :y8) {g:nX σ c9} (hg:g∈dO s (Uf v))
    (hcol:I.colon {g} = L) (hle :I ⊔ lJ {g} ≤ J) (k :ℕ) :
    ∀ᶠ a in (pG:Df y8),
      gI (acC k) (P9 s J) (a+v) +
          gI (acC k) (P9 s L) a ≤
        gI (acC k) (P9 s I) (a+v) := by
  obtain ⟨hcut,hex⟩:=a4I s I hI (Uf v) g hg
  let D:=acC k
  have he : (fun a=>P9 s (I ⊔ lJ {g}) (a+v)) =
      fun a=>P9 s I (a+v)-P9 s L a := by
    funext a
    have hn:=hex (Uf a)
    rw [hcol] at hn
    simp only [P9,c06]
    exact eq_sub_of_add_eq (by exact_mod_cast hn)
  have hm:=auS v (cKF hpos s hcut hJ hle k)
  filter_upwards [hm] with a ha
  have hd :
      gI D (P9 s (I ⊔ lJ {g})) (a+v) =
        gI D (P9 s I) (a+v) - gI D (P9 s L) a := by
    rw [← b0F D (P9 s (I ⊔ lJ {g})),he,b0G,b0F]
  change gI D (P9 s J) (a+v)≤_ at ha
  rw [hd] at ha
  exact le_sub_iff_add_le.mp ha
private theorem gpo (hpos :c1) (hr :c2)
    {A:Fin 4→Set ov} {B:Set ov} (hAB:HZ A B)
    (I:aU n5) (k :ℕ) (e :aU n5→ℝ)
    (Q:nI (aU n5)) (hQ : ∀ q∈Q,I.IsMinimalPrime q)
    (he : ∀ q∈Q,aAV A B q k (e q)) :
    ∀ᶠ a in (pG:Df y8),
      ∑ q∈Q,e q ≤
        gI (acC k) (P9 (slot A B) (xJ A B I)) a := by
  classical
  have :qy (Generator A B) :=cR5 hAB
  let R:=P9 (slot A B) ∘ xJ A B
  let D:=acC k
  have hcomp (S:nI (aU n5)) (hS : ∀ q∈S,I.IsMinimalPrime q)
      (hdeg : ∀ q∈S,aAV A B q k (e q)) :
      ∀ᶠ a in (pG:Df y8),∑ q∈S,e q≤gI D (R (intersection S)) a := by
    induction S using Kl with
    | empty =>
        simp [intersection,R,ev2,fS0,dWX]
    | insert q S hq ih =>
        have hhead:=hS q (Kc _ _)
        have htail r hr :=hS r (IU hr)
        obtain ⟨f,hfS,hfq⟩:=gpL hhead htail hq
        obtain ⟨t,g,hg,hgm⟩:=cNw hAB f
        let v :=bqO t
        have hg' : g∈dO (slot A B) (Uf v) := by simpa [v] using hg
        have hl: (xJ A B (q ⊓ intersection S)).colon {g} = xJ A B q :=
          b7A hg fun x=> by rw [hgm]; exact gpP hhead.isPrime hfq hfS x
        have hle :xJ A B (q ⊓ intersection S) ⊔ lJ {g} ≤
            xJ A B (intersection S) :=bZt inf_le_right hg (by rwa [hgm])
        have hcut:=wD hpos (slot A B) (aIt _) (aIt _)
          v hg' hl hle k
        have hi:=auS v (ih htail (fun r hr=>hdeg r (IU hr)))
        have hqdeg:=c0y hr hAB (hdeg q (Kc _ _))
        apply d3A v
        filter_upwards [hcut,hi,hqdeg] with a ha hs hd
        rw [Mk hq,eoX]
        change gI D (R (intersection S)) (a+v)+gI D (R q) a ≤
          gI D (R (q ⊓ intersection S)) (a+v) at ha
        change gI D (R q) a=e q at hd
        linarith
  have hle :I≤ intersection Q:=Finset.le_inf fun q hq=>(hQ q hq).le
  have hm:=cKF hpos (slot A B) (aIt I)
    (aIt (intersection Q)) (cXy hle) k
  filter_upwards [hcomp Q hQ he,hm] with a ha hb using ha.trans hb
private theorem fWe (i:Fin 4) :
  acC i.val=i :: acC (i.val+1) := by
 fin_cases i <;> rfl
theorem of_children (hpos :c1) (hr :c2) :XT.c2 := by
 classical
 intro A B hAB i P hp _ f hf hs Q hQ d e hd he
 have :qy (Generator A B) :=cR5 hAB
 let R:=P9 (slot A B) ∘ xJ A B
 let k :=i.val+1
 let D:=acC k
 let v :=advance i
 obtain ⟨g,hg,hgm⟩:=a3P (A:=A) (B:=B) i.castSucc (f^2)
   (by simpa [aFa] using hs)
 have hg' : g∈dO (slot A B) (Uf v) := by simpa [v] using hg
 have hgcol: (xJ A B P).colon {g} = xJ A B P:= by
   apply b7A hg
   intro x
   rw [hgm,pow_two]
   exact ⟨fun hx=>(hp.mem_or_mem hx).resolve_right
     (fun h=>hf ((hp.mem_or_mem h).elim id id)),P.mul_mem_right _⟩
 have hgle :xJ A B P ⊔ lJ {g} ≤ xJ A B (cut P (f^2)) :=
   bZt Nr hg (by rw [hgm]; exact bZu P (f^2))
 have hfirst:=wD hpos (slot A B) (aIt _) (aIt _)
   v hg' hgcol hgle k
 obtain ⟨t,u,hu,hum⟩:=cNw hAB f
 let z :=bqO t
 have hu' : u∈dO (slot A B) (Uf z) := by simpa [z] using hu
 have hucol: (xJ A B (cut P (f^2))).colon {u} = xJ A B (cut P f) :=
   b7A hu fun x=> by rw [hum]; exact bwV hp hf x
 have hule :xJ A B (cut P (f^2)) ⊔ lJ {u} ≤ xJ A B (cut P f) :=
   bZt (dS6 P f) hu (by rw [hum]; exact bZu P f)
 have hsecond:=wD hpos (slot A B) (aIt _) (aIt _)
   z hu' hucol hule k
 have hsel:=gpo hpos hr hAB (cut P f) k e Q hQ he
 have hparent :=c0y hr hAB hd
 have hbudget : ∀ᶠ a in (pG:Df y8),2 * ∑ q∈Q,e q≤d:= by
   filter_upwards [auS z hfirst,auS v hsecond,
     auS v hsel,auS (v+z) hsel,auS z hparent]
     with a h₁ h₂ hb hc h₀
   change gI D (R (cut P (f^2))) (a+z+v)+gI D (R P) (a+z) ≤
     gI D (R P) (a+z+v) at h₁
   change gI D (R (cut P f)) (a+v+z)+gI D (R (cut P f)) (a+v) ≤
     gI D (R (cut P (f^2))) (a+v+z) at h₂
   change gI (acC i.val) (R P) (a+z)=d at h₀
   rw [fWe,bEf,b0G,b0F] at h₀
   rw [Kp a z v] at h₁ h₀
   rw [← add_assoc a v z] at hc
   change ∑ q∈Q,e q≤gI D (R (cut P f)) (a+v) at hb
   change ∑ q∈Q,e q≤gI D (R (cut P f)) (a+v+z) at hc
   change gI D (R P) (a+v+z) - gI D (R P) (a+z)=d at h₀
   linarith only [h₁,h₂,hb,hc,h₀]
 obtain ⟨_,hb⟩:=hbudget.exists
 exact hb
end
end as7
end
section
namespace bRB
noncomputable section
open dN Jq XT as7 MvPolynomial
open scoped BigOperators Pointwise
variable {A:Fin 4→Set ov} {B:Set ov}
private abbrev alq (A:Fin 4→Set ov) (B:Set ov) :
  (Generator A B →₀ ℕ) →+ Exponent :=
 oy fun v :Generator A B=>v.2.val
private abbrev bxe (A:Fin 4→Set ov) (B:Set ov) :
  jJ →+ Set Exponent :=
 oy (aFa A B)
private theorem gxv (j:Fin 5) :
  bxe A B (zY j)=aFa A B j:= by
 rw [zY,qG,Ml]
private theorem gxu (a :y8) :
  bxe A B (Uf a)=aza A B a.1 a.2 := by
 rw [Fz ,Fin.sum_univ_castSucc]
 simp only [b9z,crV,bsP,bxc,
  zmM,aza]
 ac_rfl
private theorem dsr (e :Generator A B →₀ ℕ) :
   alq A B e∈bxe A B (oy (jT (slot A B)) e) := by
 induction e using FK with
 | zero=>simp
 | add e f he hf =>
    rw [oY ,oY ,oY]
    exact Set.add_mem_add he hf
 | single v n =>
    rw [qG,qG,map_nsmul]
    change n•v.2.val∈n•bxe A B (zY v.1)
    rw [gxv]
    exact zfk v.2.property
private theorem fUo (j:Fin 5) (n:ℕ) {m:ov}
    (hm:m∈n•aFa A B j) :
    ∃ e :Generator A B →₀ ℕ,
      oy (jT (slot A B)) e=n•zY j∧alq A B e=m:= by
  induction n generalizing m with
  | zero =>
      have hm0:m=0:= by simpa using hm
      exact ⟨0,by simp,by simp [hm0]⟩
  | succ n ih =>
      rw [succ_nsmul] at hm ⊢
      obtain ⟨x,hx,y,hy,rfl⟩:=Set.mem_add.mp hm
      obtain ⟨e,he,hxe⟩:=ih hx
      let v :Generator A B:=⟨j,⟨y,hy⟩⟩
      refine ⟨e+Finsupp.single v 1,?_,?_⟩
      · rw [oY ,he,qG,Ml]
        rfl
      · rw [oY ,hxe,qG,Ml]
private theorem fUn (t:jJ) {m:ov} (hm:m∈bxe A B t) :
   ∃ e :Generator A B →₀ ℕ,
     oy (jT (slot A B)) e=t∧alq A B e=m:= by
 induction t using FK generalizing m with
 | zero =>
     have hm0:m=0:= by simpa using hm
     exact ⟨0,by simp,by simp [hm0]⟩
 | add t u ht hu =>
     rw [oY] at hm
     obtain ⟨x,hx,y,hy,rfl⟩:=Set.mem_add.mp hm
     obtain ⟨e,he,hxe⟩:=ht hx
     obtain ⟨f,hf,hyf⟩:=hu hy
     exact ⟨e+f,by rw [oY ,he,hf],by rw [oY ,hxe,hyf]⟩
 | single j n =>
     rw [qG] at hm
     simpa only [zY,zrt] using fUo j n hm
private theorem cZ7 (a :y8) (m:ov) :
    m∈aza A B a.1 a.2 ↔
      ∃ e :Generator A B →₀ ℕ,
        oy (jT (slot A B)) e=Uf a∧alq A B e=m:= by
  rw [← gxu a]
  refine ⟨fUn (Uf a),?_⟩
  rintro ⟨e,he,rfl⟩
  rw [← he]
  exact dsr e
private theorem aT6 (e :Generator A B →₀ ℕ) :
    ew A B (qz e 1)=qz (alq A B e) 1 := by
  induction e using FK with
  | zero=>simp [monomial_zero']
  | add e f he hf =>
      rw [← xm (1 :c9),← zDU,oz ,he,hf,
        zDU,xm,oY]
  | single v n =>
      rw [← X_pow_eq_monomial,vw ,ew,aeval_X,monomial_pow,KA,
        qG]
private theorem dVP (a :y8) :
    (dO (slot A B) (Uf a)).map (ew A B).toLinearMap =
      yJ c9 (aza A B a.1 a.2) := by
  rw [show dO (slot A B) (Uf a)=yJ c9
        {e | oy (jT (slot A B)) e=Uf a} from
      zSq _ _ _,
    NI,NI,Submodule.map_span]
  apply lz (Submodule.span c9)
  ext p
  constructor
  · rintro ⟨_,⟨e,he,rfl⟩,rfl⟩
    refine ⟨alq A B e,(cZ7 a _).2 ⟨e,he,rfl⟩,?_⟩
    exact (aT6 e).symm
  · rintro ⟨m,hm,rfl⟩
    obtain ⟨e,he,rfl⟩:=(cZ7 a m).1 hm
    exact ⟨qz e 1,⟨e,he,rfl⟩,aT6 e⟩
theorem proof :as7.c2 := by
 intro A B _ P a
 let S:=dO (slot A B) (Uf a)
 let q:=(Fa c9 (xJ A B P)).toLinearMap.domRestrict S
 let p:=(((Fa c9 P).toLinearMap).comp
   (ew A B).toLinearMap).domRestrict S
 have hk :uJ q=uJ p:= by
   ext x
   rw [Kz ,Kz]
   change mD (xJ A B P) x.val=0 ↔
     mD P (ew A B x.val)=0
   rw [G7,G7]
   exact bI8 x.property
 have hr :=((q.quotKerEquivRange.symm.trans (Gn _ _ hk)).trans
   p.quotKerEquivRange).finrank_eq
 dsimp only [q,p] at hr
 rw [zyK,zyK,z1U,
   show S.map (ew A B).toLinearMap= _ from dVP a] at hr
 exact lz (fun n:ℕ=>(n:ℝ)) hr
end
end bRB
end
section
namespace cys
open aR B8 agM
open scoped BigOperators Pointwise
private theorem brB (a :ox×ℕ) (e :Exponent) :
  e∈Nl a ↔
    e 0+e 1+e 2+e 3≤2*a.1.b ∧
    e 1+2*e 2 + 3*e 3≤2*a.1.j ∧
    e 3≤2*a.1.t∧e 4≤2*a.2 := by
 change Qj (a.1.scale 2,2*a.2) e↔_
 simp only [Qj,zmM,vi]
 change (_∧(0*e 0+1*e 1+2*e 2 + 3*e 3≤_)∧_∧_)↔_
 simp
private theorem euH (p q:ox) (r s :ℕ) (hp:bF p) (hq:bF q) :
    Nl (p,r)+Nl (q,s)=Nl (p.plus q,r+s) := by
  ext e
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    simp only [brB,J4 ,Dv] at *
    omega
  · intro he
    obtain ⟨hpb,hpj⟩:=hp
    obtain ⟨hqb,hqj⟩:=hq
    simp only [brB,J4] at he
    let z :=min (e 3) (2*p.t)
    let z' := e 3 - z
    have hz :z+z' = e 3∧z≤2*p.t∧z' ≤ 2*q.t:= by dsimp [z,z']; omega
    let w:=2*p.j-3*z
    let w' := 2*q.j-3*z'
    have hw:w+3*z=2*p.j∧w' + 3*z' = 2*q.j:= by
      dsimp [w,w']
      omega
    have hhalf : (w+w')/2=w/2+w' / 2 := by
      by_cases h:e 3≤2*p.t
      · have hz' : z' = 0:= by dsimp [z,z']; omega
        omega
      · have hze :z=2*p.t:=min_eq_right (by omega)
        omega
    let y :=min (e 2) (w/2)
    let y' := e 2 - y
    have hy :y+y' = e 2∧2*y≤w∧2*y' ≤ w' := by dsimp [y,y']; omega
    let x :=min (e 1) (w - 2*y)
    let x' := e 1 - x
    have hx :x + x' = e 1∧x+2*y≤w∧x' + 2*y' ≤ w' := by
      dsimp [x,x']
      omega
    let u:=min (e 0) (2*p.b-(x+y+z))
    let u' := e 0 - u
    have hu:u+u' = e 0∧u + x+y+z≤2*p.b∧u' + x' + y' + z' ≤ 2*q.b:= by
      dsimp [u,u']
      omega
    let v :=min (e 4) (2*r)
    let v' := e 4 - v
    have hv :v+v' = e 4∧v≤2*r∧v' ≤ 2*s := by dsimp [v,v']; omega
    let a :Exponent:=Finsupp.equivFunOnFinite.symm ![u,x,y,z,v]
    let b:Exponent:=Finsupp.equivFunOnFinite.symm ![u',x',y',z',v']
    refine ⟨a,(brB (p,r) a).2 ?_,b,
      (brB (q,s) b).2 ?_,?_⟩
    · change u + x+y+z≤2*p.b∧x+2*y+3*z≤2*p.j ∧
        z≤2*p.t∧v≤2*r
      omega
    · change u' + x' + y' + z' ≤ 2*q.b∧x' + 2*y' + 3*z' ≤ 2*q.j ∧
        z' ≤ 2*q.t∧v' ≤ 2*s
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact hz.1
      · exact hv.1
private theorem euI:Nl (⟨0,0,0⟩,0)=0:= by
 ext e
 rw [brB,KH]
 constructor
 · rintro ⟨h,_,_,hlast⟩
   change e 0+e 1+e 2+e 3≤0 at h
   change e 4≤0 at hlast
   have h0:e 0=0:= by omega
   have h1 :e 1=0:= by omega
   have h2 :e 2=0:= by omega
   have h3:e 3=0:= by omega
   have h4 :e 4=0:= by omega
   ext i
   fin_cases i
   · exact h0
   · exact h1
   · exact h2
   · exact h3
   · exact h4
 · rintro rfl
   simp
private theorem df1 {ι:Type*} (I:nI ι) (A:ι→ ox×ℕ)
    (hA : ∀ i,bF (A i).1) :
    (∑ i∈I,Nl (A i))=Nl
      (⟨∑ i∈I,(A i).1.b,∑ i∈I,(A i).1.j,∑ i∈I,(A i).1.t⟩,∑ i∈I,(A i).2) := by
  classical
  induction I using Kl with
  | empty=>simp only [Finset.sum_empty,euI]
  | insert i I hi ih =>
    have hI:bF ⟨∑ k∈I,(A k).1.b,∑ k∈I,(A k).1.j,∑ k∈I,(A k).1.t⟩:= by
      constructor
      · exact uW fun k _=>(hA k).1
      · change 3*(∑ k∈I,(A k).1.t) ≤ ∑ k∈I,(A k).1.j
        rw [ze]
        exact uW fun k _=>(hA k).2
    simp only [Mk hi]
    rw [ih,euH _ _ _ _ (hA i) hI]
    rfl
private theorem c1Q (a :ox×ℕ) (ha :bF a.1) (n:ℕ) :
  n•Nl a=Nl (agj a n) := by
 simpa only [Mw ,S1 ,Pj,UZ,
  agj,vi] using
  df1 (Kv :nI (Fin n)) (fun _=>a) (fun _=>ha)
private theorem BP (a :ox×ℕ) (ha :bF a.1) (n:ℕ) :
  bF (agj a n).1 := by
 refine ⟨qU n ha.1,?_⟩
 change 3*(n*a.1.t)≤n*a.1.j
 rw [WK 3 n]
 exact qU n ha.2
private theorem b0y (B:lS) (t:Fin 5→ℕ) :
    H7 B t = ∑ i,∑ _j:Fin (t i),Nl (B i) := by
  classical
  ext e
  rw [RJ]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨fun i => ∑ j,u i j,fun i=>(RJ _ _).2 ⟨u i,hu i,rfl⟩,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    have h (i:Fin 5) : ∃ u:Fin (t i)→Exponent,
        (∀ j,u j∈Nl (B i)) ∧ ∑ j,u j=v i:= by
      obtain ⟨u,hu,hs⟩:=(RJ _ _).1 (hv i)
      exact ⟨u,hu,hs⟩
    choose u hu hs using h
    exact ⟨u,hu,by simp only [hs]⟩
theorem proof :agM.c1 := by
  intro B hB t n
  have hdiag:H7 B t=Nl (Vw B t) := calc
    _ = ∑ i,∑ _j:Fin (t i),Nl (B i) :=b0y B t
    _ = ∑ i,Nl (agj (B i) (t i)) := by
      apply qx rfl
      intro i _
      simpa only [Mw ,S1 ,Pj] using
        c1Q (B i) (hB i) (t i)
    _=Nl (Vw B t) :=
      df1 Kv (fun i=>agj (B i) (t i))
        (fun i=>BP (B i) (hB i) (t i))
  rw [hdiag]
  exact c1Q (Vw B t) (bOu B hB t) n
end cys
end
section
namespace cyt
open aR Dr aiK B8 Finset
open scoped BigOperators
noncomputable section
private def b3w (b j:ℕ) :=
 Σ y :Fin (j+1),Σ x :Fin (2*j - 2*y.val+1),
   Fin (2*b-(y.val + x.val)+1)
private def ec5 (p:ox) (hb:p.j≤p.b) (ht:p.t=0) :
  pz p ≃ b3w p.b p.j where
 toFun e := by
  have he :=(OW p e.val).mp e.property
  have hdeg:=he.1
  have hweight:=he.2.1
  have htop:=he.2.2
  let y :Fin (p.j+1) :=⟨e.val 2,by omega⟩
  let x :Fin (2*p.j - 2*y.val+1) :=⟨e.val 1,by dsimp [y]; omega⟩
  exact ⟨y,x,⟨e.val 0,by dsimp [y,x]; omega⟩⟩
 invFun a := by
  rcases a with ⟨y,x,u⟩
  have hy :=y.isLt
  have hx :=x.isLt
  have hu:=u.isLt
  refine ⟨Finsupp.equivFunOnFinite.symm ![u.val,x.val,y.val,0],(OW p _).mpr ?_⟩
  change u.val + x.val+y.val+0≤2*p.b ∧
    x.val+2*y.val+3*0≤2*p.j∧0≤2*p.t
  omega
 left_inv e := by
  have hz :e.val 3=0:= by
    have h:=((OW p e.val).mp e.property).2.2
    omega
  apply pL
  ext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hz.symm
 right_inv a := by
  rcases a with ⟨⟨y,hy⟩,⟨x,hx⟩,⟨u,hu⟩⟩
  rfl
private theorem bw6 (a d:ℚ) (n:ℕ) :
   (∑ x∈p7 n,(a+d*(x :ℚ)))=n*a+d*n*((n:ℚ) - 1)/2 := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [sum_range_succ,ih]
   push_cast
   ring
private theorem dmt (p:ox) (hb:p.j≤p.b) (ht:p.t=0) :
    ((pz p).ncard:ℚ) =
      ((p.j:ℚ)+1)^2*(2*(p.b:ℚ)+1-(p.j:ℚ)) := by
  classical
  let:oK (b3w p.b p.j) := by unfold b3w; infer_instance
  rw [← JM,Nj (ec5 p hb ht),XB]
  change (Fintype.card (Σ y :Fin (p.j+1),Σ x :Fin (2*p.j - 2*y.val+1),
    Fin (2*p.b-(y.val + x.val)+1)) :ℚ)= _
  simp only [Fintype.card_sigma,Pj,SU]
  rw [Ok (fun y => ∑ x :Fin (2*p.j - 2*y+1),
    ((2*p.b-(y + x.val)+1 :ℕ) :ℚ))]
  calc
    _ = ∑ y∈p7 (p.j+1),
        (2*(p.b:ℚ)+1 - p.j)*(2*(p.j:ℚ)+1+(-2)*(y :ℚ)) := by
      apply qx rfl
      intro y hy
      have hy' := mem_range.mp hy
      have hyj:2*y≤2*p.j:= by omega
      rw [Ok (fun x=>((2*p.b-(y + x)+1 :ℕ) :ℚ))]
      calc
        _ = ∑ x∈p7 (2*p.j - 2*y+1),
            (2*(p.b:ℚ) - y+1+(-1)*(x :ℚ)) := by
          apply qx rfl
          intro x hx
          have hx' := mem_range.mp hx
          have hxy :y + x≤2*p.b:= by omega
          push_cast [Nat.cast_sub hxy]
          ring
        _ = _:= by
          rw [bw6]
          push_cast [Nat.cast_sub hyj]
          ring
    _ = _:= by
      rw [← ze,bw6]
      push_cast
      ring
private theorem euL (p:ox) : (aIp p).natDegree≤4 := by
 rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
 intro k hk
 have hne (m:ℕ) (hm:m≤4) :k≠m:= by omega
 simp only [aIp,Polynomial.coeff_add,zds,
  Polynomial.coeff_C,C9 (hne 4 (by decide)),C9 (hne 3 (by decide)),
  C9 (hne 2 (by decide)),C9 (hne 1 (by decide)),
  C9 (hne 0 (by decide)),G6]
theorem proof :agM.c2 := by
  intro p hp
  refine ⟨aIp p,euL p,?_,?_⟩
  · rw [cWV]
    ring
  · intro n
    cases n with
    | zero =>
      rw [dmt (p.scale 0) (by simp [vi]) (by simp [vi])]
      simp [aIp,vi]
    | succ n =>
      by_cases ht:p.t=0
      · rw [dmt (p.scale (n+1)) (qU _ hp.1)
          (by simp [vi ,ht])]
        simp only [aIp,zvF,Polynomial.eval_mul,Polynomial.eval_pow,
          Te,MO,vi ,Dn,ht,Nat.cast_zero,mul_zero]
        push_cast
        ring
      · exact cWW p ⟨hp.1,hp.2,Nq ht⟩ _ (Nat.succ_pos _)
end
end cyt
end
section
namespace cyM
noncomputable section
open aR dN rW MvPolynomial
open scoped Polynomial
private theorem ep5 (P:n8) [P.IsPrime] (hP:P.height=2) :
   (yl P).natDegree=2 := by
 have hPne :P ≠ ⊥ := by
   intro he
   have hz :=Ideal.height_eq_zero_iff_eq_bot.mpr he
   rw [hP] at hz
   exact (by decide : (2 :ℕ∞)≠0) hz
 obtain ⟨f,hfP,hf⟩:=zxV (bot_lt_iff_ne_bot.mpr hPne)
 have hf0:f≠0:= fun he=>hf (he.symm ▸ Ideal.zero_mem _)
 have hfspan:lJ {f} ≤ P:=Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfP)
 obtain ⟨D,hD,hDP⟩:=Ideal.exists_minimalPrimes_le hfspan
 let:=hD.isPrime
 have hDne :D ≠ ⊥ := fun he=>hf (he ▸ hD.le (Il (by simp)))
 have hDheight:D.height = 1 :=
   wA (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ D hD)
     (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hDne))
 have hDlt:D <P:=GB hDP fun he=> by
   rw [he,hP] at hDheight
   exact (by decide : (2 :ℕ∞)≠1) hDheight
 obtain ⟨g,hgP,hgD⟩:=zxV hDlt
 have hcut: (D ⊔ lJ {g}).IsMinimalPrime P:= by
   have hgspan:lJ {g} ≤ P:=Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgP)
   refine ⟨⟨z9,sup_le hDP hgspan⟩,?_⟩
   intro J hJ hJP
   by_contra hPJ
   let:J.IsPrime :=hJ.1
   have hgJ:g∈J :=
     (le_sup_right.trans hJ.2 :lJ {g} ≤ J) (Il (by simp))
   have hDJ:D <J :=
     GB (le_sup_left.trans hJ.2) (fun he=>hgD (he.symm ▸ hgJ))
   have hJheight: (2 :ℕ∞)≤J.height:= by
     simpa only [hDheight,one_add_one_eq_two] using zSK hDJ
   have hlt:=Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_not_ge hJP hPJ)
   rw [hP] at hlt
   exact (not_lt_of_ge hJheight) hlt
 have hDdeg:=natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hf0 hD
 have hPdeg:=principalCut_natDegree_affineHilbertPolynomial_add_one hgD hcut
 rw [Nat.card_fin] at hDdeg
 omega
private def aCI (P:n8) :c9 →+* tJ P :=
 (K4 P).comp nq
private def a2I (P:n8) (U: (tJ P)[X]) :
  mK →+* tJ P :=
 yB (aCI P) (fun j=>U.coeff j.val)
private theorem dMM (P:n8) [P.IsPrime] {U: (tJ P)[X]}
   (hd:U.natDegree<bf) (i:ℕ) :
   a2I P U (J1 rI i) =
     (pQ i U).eval (aCI P rI) := by
 have hsum:U = ∑ j:Fin bf,t9 j.val (U.coeff j.val) := by
   rw [Ok (fun n:ℕ=>t9 n (U.coeff n))]
   exact U.as_sum_range' _ hd
 rw [lz (fun V=>(pQ i V).eval (aCI P rI)) hsum]
 simp only [J1,u5 ,Polynomial.eval_finsetSum]
 refine qx rfl fun j _ => ?_
 simp only [zKa,Polynomial.eval_monomial,oz ,a2I,
   NW,Lf ,Ts ,vw]
 ring
private theorem ed2 (P:n8) [P.IsPrime] (U: (tJ P)[X])
    (hd:U.natDegree<bf)
    (hjet : ∀ i:Fin 4,(pQ i.val U).eval
      (K4 P (nq rI))=K4 P (lV i)) :
    lA (Zv (CX P) U)≤P:= by
  have hmap : (a2I P U).comp (t3 ni) =
      yB (CX P) (fun j:Fin bf=>U.coeff j.val) := by
    ext a <;> simp [a2I,aCI,CX]
  have hkill:gN (Zv (CX P) U) ≤
      sH (a2I P U) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact (Ze hmap a).trans ha
  have hcomp: (a2I P U).comp mS=K4 P:= by
    ext a
    · simp [a2I,mS,aCI]
    · rw [pU,mS,Lf ,
        dMM P hd]
      exact hjet a
  intro a ha
  have hz :K4 P a=0 :=
    (Ze hcomp a).symm.trans (hkill ha)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply xL (n5 ⧸ P) (tJ P)
  exact hz.trans (p6 _).symm
private theorem enH (A:kT) :
  (yl (lA A)).natDegree≤(yl A).natDegree := by
 let f : (n5 ⧸ lA A) →ₐ[c9] (mK ⧸ gN A) :=
  Ideal.quotientMapₐ (gN A) MJ.tO (by intro p hp; exact hp)
 have hf :p9 f := by
  apply (Un f).mpr
  intro x hx
  obtain ⟨p,rfl⟩:=Et x
  change mD (gN A) (mS p)=0 at hx
  rw [G7] at hx ⊢
  exact hx
 have h:=zGE f hf
 let:yU ao GeoField:=ni.toAlgebra
 have hbase :yl (gN A)=yl A :=
  Ey.ZI (E :=c9) A
 exact hbase ▸ h
theorem proof :as9.c3:= by
 intro P hp U hheight hdegree hjet
 let:=hp
 let A:=Zv (CX P) U
 calc
   2=(yl P).natDegree :=(ep5 P hheight).symm
   _≤(yl (lA A)).natDegree :=
     natDegree_affineHilbertPolynomial_le_of_le (ed2 P U hdegree hjet)
   _≤(yl A).natDegree :=enH A
end
end cyM
end
section
namespace cxQ
noncomputable section
open aR jA aFO Polynomial
open scoped Polynomial
private def bnO:ao →+* I6:=(C:ao[X] →+* I6).comp C
private def constant (p:ao[X]) :I6[X] :=p.map bnO
@[simp] private theorem bOe (ε:ao) (u:ao[X]) :
   Wv ε (C u)=C (u.eval ε) := by
  simp [Wv]
@[simp] private theorem de4 (ε:ao) :
   Wv ε (oj:I6)=Polynomial.X:= by
  simp [Wv]
@[simp] private theorem cqm (p:ao[X]) (ε:ao) :
   (constant p).map (Wv ε)=p.map C:= by
  rw [constant,sI]
  have h: (Wv ε).comp bnO=(C:ao →+* ao[X]) := by
   ext x
   simp [bnO]
  rw [h]
@[simp] private theorem ezf (p:ao[X]) (z :ao) :
   (p.map C).map (qM z)=p:= by
  rw [sI]
  have h: (qM z).comp C=LQ ao:= by
   ext x
   simp
  rw [h,Xx]
@[simp] private theorem b8G (p:ao[X]) :
   (p.map C).map (cy ao[X] kS)=jH p:= by
  rw [jH,sI,
   ← Zt,← zYY ao ao[X] kS]
private theorem ce1 {F:Type*} [zc F] {H A:F[X]}
  (hH :H.Monic) {n:ℕ} (hA:A.natDegree≤n) (hc:xI A H) :
  H.resultant A H.natDegree n≠0:= by
 have e :=resultant_add_right_deg H A H.natDegree A.natDegree
  (n - A.natDegree) th
 rw [GR hA,coeff_natDegree,hH.leadingCoeff,KA,xm] at e
 rw [e]
 exact ((zgx hH).mpr hc.symm).ne_zero
private theorem coJ {F:Type*} [zc F] {H A U V:F[X]} {d:F}
  (hd:d≠0) (h:H*U + A*V=C d) :xI A H := by
 refine ⟨C d⁻¹*V,C d⁻¹*U,?_⟩
 calc
  _=C d⁻¹*(H*U + A*V) := by ring
  _=1 := by rw [h,← C_mul,Du hd,C_1]
private theorem aQ3 {F:Type*} [zc F] {H A B N :F[X]} {d:F}
    (hd:d≠0) (h:H∣A*N+C d*B) :
    H∣A*(C d⁻¹*N)+B:= by
  have hunit :C d⁻¹*C d=(1 :F[X]) := by
    rw [← C_mul,Du hd,C_1]
  calc
    H∣C d⁻¹*(A*N+C d*B) :=h.mul_left _
    _=A*(C d⁻¹*N)+B:= by
      calc
        _=A*(C d⁻¹*N)+(C d⁻¹*C d)*B:= by ring
        _ = _:= by rw [hunit,xm]
theorem proof :aFO.c1 := by
  intro H c q a₀ a₁ hH hpos
  let block :I6[X] :=constant H+C (C (oj:ao[X]))
  let A:I6[X] :=constant c*(constant a₀+C (oj:I6)*constant a₁)
  let B:I6[X] :=C (oj:I6)*constant q
  let den:=block.resultant A block.natDegree A.natDegree
  have hconst: (constant H).Monic:=hH.map bnO
  have hconst_deg: (constant H).natDegree=H.natDegree :=hH.natDegree_map bnO
  have hdeg:block.natDegree=H.natDegree := by
    dsimp only [block]
    rw [natDegree_add_C,hconst_deg]
  have hblock :block.Monic :=
    hconst.add_of_left (degree_C_le.trans_lt
      (natDegree_pos_iff_degree_pos.mp (by rwa [hconst_deg])))
  have hblock_pos :0<block.natDegree := by rwa [hdeg]
  have hblock_ne :block≠1 := by
    intro h
    simp [h] at hblock_pos
  obtain ⟨U,V,_,_,hbezout⟩:=zKy block A th th
    (Gi (SD hblock_pos))
  change block*U + A*V=C den at hbezout
  let num :=(-B*V) %ₘ block
  have hcleared:block∣A*num+C den*B:= by
    obtain ⟨W,hW⟩:=dvd_modByMonic_sub (-B*V) block
    refine ⟨A*W+B*U,?_⟩
    change num-(-B*V)=block*W at hW
    calc
      A*num+C den*B=A*(num-(-B*V))+B*(block*U) := by
        rw [← hbezout]
        ring
      _=block*(A*W+B*U) := by
        rw [hW]
        ring
  refine ⟨num,den,?_⟩
  intro ε hc ha
  let s :=Wv ε
  let e :=qM (0:ao)
  let f :=cy ao[X] kS
  have hHs :block.map s=(Q8 H ε).map C:= by
    simp only [block,s,Q8,z7,sS ,
      cqm,bOe,MO]
  have hAs :A.map s=c.map C*(a₀.map C+C (oj:ao[X])*a₁.map C) := by
    simp only [A,s,v8 ,z7,sS ,
      cqm,de4]
  have hBs :B.map s=C (oj:ao[X])*q.map C:= by
    simp only [B,s,v8 ,sS ,cqm,de4]
  have hHe :block.map (e.comp s)= Q8 H ε:= by
    rw [← sI,hHs,ezf]
  have hAe :A.map (e.comp s)=c*a₀:= by
    rw [← sI,hAs]
    simp [e]
  have hd: (s den).eval 0≠0:= by
    have hdegree : (block.map (e.comp s)).natDegree=block.natDegree := by
      rw [hHe,cps,hdeg]
    change (e.comp s) (block.resultant A block.natDegree A.natDegree)≠0
    rw [← resultant_map_map,← hdegree]
    exact ce1 (hblock.map (e.comp s)) RC (by
      rw [hHe,hAe]
      exact hc.mul_left ha)
  have hden:s den≠0:= by
    intro h
    exact hd (by simp [h])
  have hf :f (s den)≠0 :=
    (Bf f (xL ao[X] kS)).mpr hden
  have hHf :block.map (f.comp s)=jH (Q8 H ε) := by
    rw [← sI,hHs,b8G]
  have hAf :A.map (f.comp s)=bu4 c a₀ a₁:= by
    rw [← sI,hAs]
    simp only [v8 ,z7,sS ,
      b8G,bu4,f]
  have hBf :B.map (f.comp s)=bu5 q:= by
    rw [← sI,hBs]
    simp only [v8 ,sS ,b8G,bu5,f]
  refine ⟨hd,?_,?_,?_⟩
  · rw [cps,← hdeg]
    exact natDegree_map_le.trans_lt (Yo _ hblock hblock_ne)
  · have hm:=lz (u8 (f.comp s)) hbezout
    simp only [yo ,z7,v8 ,sS ,
      hHf,hAf,pU] at hm
    exact coJ hf hm
  · have hm:=RP (f.comp s) hcleared
    simp only [z7,v8 ,sS ,hHf,hAf,hBf,
      pU] at hm
    have h:=aQ3 hf hm
    simpa only [awc,ahH,sI,f,s] using h
end
end cxQ
end
section
set_option maxHeartbeats 1000000
namespace cxX
noncomputable section
open aR oR we aeC MvPolynomial
open scoped BigOperators Polynomial
private abbrev Rg (P:aU (eT 3)) :=eT 3 ⧸ P
private abbrev sep (f :af 3) :=fW (separant f)
private abbrev Chart (f :af 3) (P:aU (eT 3)) :=
 Localization.Away (mD P (sep f))
private def azh (f :af 3) (P:aU (eT 3)) :
   eT 3 →ₐ[cH] Chart f P :=
 (IsScalarTower.toAlgHom cH (Rg P) (Chart f P)).comp
   (Fa cH P)
private def eMj {f :af 3} {P:aU (eT 3)} {y :Fin 3→cH}
  (hy :y∈D7 f P) :Rg P →ₐ[cH] cH :=
 zTA P (aeval y) (fun p hp=>hy.1 p hp)
private def aoJ {f :af 3} {P:aU (eT 3)} {y :Fin 3→cH}
  (hy :y∈D7 f P) :Chart f P →ₐ[cH] cH :=
 IsLocalization.Away.liftAlgHom (f :=eMj hy) (mD P (sep f))
  (isUnit_iff_ne_zero.mpr hy.2)
private theorem a6C {f :af 3} {P:aU (eT 3)}
  {y :Fin 3→cH} (hy :y∈D7 f P) (p:eT 3) :
  aoJ hy (azh f P p)=eval y p:= by
 change aoJ hy
  (cy (Rg P) (Chart f P) (mD P p))= _
 rw [aoJ,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq] <;> rfl
private theorem cFg {f :af 3} {P:aU (eT 3)} (hp:P.IsPrime)
   (hsep:sep f∉P) {z :Chart f P}
   (hz : ∀ y (hy :y∈D7 f P),aoJ hy z=0) :z=0:= by
 let:=hp
 let s :=mD P (sep f)
 obtain ⟨n,a,h⟩:=IsLocalization.Away.surj s z
 obtain ⟨p,rfl⟩:=Et a
 change z*azh f P (sep f)^n=azh f P p at h
 have hm:sep f*p∈P:= by
   rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K:=cH) P]
   intro y hy
   change eval y (sep f*p)=0
   rw [oz]
   by_cases hs :eval y (sep f)=0
   · rw [hs,zero_mul]
   · have hr :y∈D7 f P:=⟨hy,hs⟩
     have he :=lz (aoJ hr) h
     rw [oz ,hz y hr,zero_mul,a6C] at he
     rw [← he,mul_zero]
 have hmem:=(hp.mem_or_mem hm).resolve_left hsep
 have hzero :azh f P p=0:= by
   change cy (Rg P) (Chart f P) (mD P p)=0
   rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem,p6]
 have hu:vl (azh f P (sep f)^n) :=
   IsLocalization.Away.algebraMap_pow_isUnit (S:=Chart f P) s n
 exact hu.mul_right_cancel (by rw [h,hzero,zero_mul])
private def azj (f :af 3) (P:aU (eT 3)) :Chart f P :=
 IsLocalization.Away.invSelf (mD P (sep f))
private theorem eMb {f :af 3} {P:aU (eT 3)}
  {y :Fin 3→cH} (hy :y∈D7 f P) :
  aoJ hy (azj f P)=(eval y (sep f))⁻¹:= by
 have h:azh f P (sep f)*azj f P=1 :=
  IsLocalization.Away.mul_invSelf (mD P (sep f))
 have he :=lz (aoJ hy) h
 rw [oz ,a6C,map_one] at he
 exact (inv_eq_of_mul_eq_one_right he).symm
private def U5 (f :af 3) (P:aU (eT 3)) :ℕ→Chart f P
 | 0=>azh f P (MvPolynomial.X 0)
 | 1=>azh f P (MvPolynomial.X 1)
 | 2=>azh f P (MvPolynomial.X 2)
 | k+3=>2*azh f P (fW (AR f k)) *
     cy cH (Chart f P) (((k+3).factorial:cH)⁻¹) *
     azj f P^(2*k+1)
private theorem eMf {y :Fin 3→cH} (p:af 3) :
 Bt y p=eval y (fW p) :=rfl
private theorem eL9 {f :af 3} {P:aU (eT 3)}
   {y :Fin 3→cH} (hy :y∈D7 f P) (j:ℕ) :
   aoJ hy (U5 f P j)=afk f (Bt y) j:= by
 match j with
 | 0=>simp [U5,afk,Bt,a6C]
 | 1=>simp [U5,afk,Bt,a6C]
 | 2=>simp [U5,afk,Bt,a6C]
 | k+3 =>
   simp only [U5,afk,oz ,map_ofNat,vw ,AlgHom.commutes,
     zEi,a6C,eMb,eMf]
   rw [div_eq_mul_inv,mul_inv,← inv_pow,uh (2*_)]
private def ab2 (f :af 3) (P:aU (eT 3)) : (Chart f P)[X] :=
 wR (-(cy cH (Chart f P) (qY oj)))
  (∑ j:Fin bf,t9 j.val (U5 f P j.val))
private theorem eMa {f :af 3} {P:aU (eT 3)}
  {y :Fin 3→cH} (hy :y∈D7 f P) :
  (ab2 f P).map (aoJ hy).toRingHom=aac f (Bt y) := by
 have hc:centre (Bt y)=qY Polynomial.X:= by simp [centre,Bt]
 have hmap (z :Chart f P) : (aoJ hy).toRingHom z=aoJ hy z :=rfl
 simp only [ab2,aac,hc,zla,map_neg,hmap,
  AlgHom.commutes,zEi,NY ,SL,
  eL9]
private def chartCoefficientMap (f :af 3) (P:aU (eT 3)) :
  eT bf →ₐ[cH] Chart f P :=
 aeval (fun j:Fin bf=>(ab2 f P).coeff j.val)
private theorem cbZ {f :af 3} {P:aU (eT 3)}
   {y :Fin 3→cH} (hy :y∈D7 f P) (p:eT bf) :
   aoJ hy (chartCoefficientMap f P p)=eval (aWP f y) p:= by
 rw [chartCoefficientMap,comp_aeval_apply]
 have hj (j:Fin bf) :aoJ hy ((ab2 f P).coeff j.val) =
     (aac f (Bt y)).coeff j.val := by
   change (aoJ hy).toRingHom ((ab2 f P).coeff j.val)= _
   rw [← zg (f :=(aoJ hy).toRingHom),
     eMa hy]
 exact lz (fun a :GD =>eval a p) (funext hj)
private theorem dRV {f :af 3} {P:aU (eT 3)}
   (hp:P.IsPrime) (hsep:sep f∉P) :
   aHk f P=sH (chartCoefficientMap f P).toRingHom:= by
 ext p
 rw [ZK]
 change (∀ a∈bX0 f P,eval a p=0)↔chartCoefficientMap f P p=0
 constructor
 · intro h
   apply cFg hp hsep
   intro y hy
   rw [cbZ hy]
   exact h _ ⟨y,hy,rfl⟩
 · rintro h _ ⟨y,hy,rfl⟩
   rw [← cbZ hy,h,p6]
private def bHR (i:Fin 3) :eT bf :=
 (pQ i.val (∑ j:Fin bf,
   t9 j.val (lV j))).eval
    (nq (qY oj))
private theorem d2v (a :GD) (i:Fin 3) :
    eval a (bHR i) =
      (pQ i.val (JC a)).eval
        (qY oj) := by
  rw [bHR,← Polynomial.eval_map_apply,← zvb]
  simp only [NY ,SL,Gr,FQ,JC]
private theorem dPG {f :af 3} {P:aU (eT 3)}
  (hp:P.IsPrime) (hsep:sep f∉P) (p:eT 3) :
  azh f P p∈Re (chartCoefficientMap f P) := by
 have he : (chartCoefficientMap f P).comp (aeval bHR)=azh f P:= by
  apply Zf
  intro i
  rw [AlgHom.comp_apply,aeval_X]
  apply sub_eq_zero.mp
  apply cFg hp hsep
  intro y hy
  rw [Av,cbZ hy,d2v,
    bCY,c7C,a6C,Gr,sub_self]
 exact ⟨aeval bHR p,Ze he p⟩
theorem proof :aeC.c4 := by
  intro f P hp hsep hdim
  let:=hp
  have hs :mD P (sep f)≠0 :=
    mt Ideal.Quotient.eq_zero_iff_mem.mp hsep
  let:G2 (Chart f P) :=Localization.Away.isDomain hs
  let Φ:=chartCoefficientMap f P
  have hk :aHk f P=sH Φ.toRingHom:=dRV hp hsep
  rw [hk]
  refine ⟨zgL Φ.toRingHom,?_⟩
  rw [← hdim]
  apply wA
  · let e :=awayPresentationEquiv P (sep f)
    exact (zGE
      (e.symm.toAlgHom.comp (Ideal.kerLiftAlg Φ))
      (e.symm.injective.comp (Ideal.kerLiftAlg_injective Φ))).trans
        (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le P (sep f))
  · have hregular :IsLeftRegular (mD P (sep f)) :=
      zUH hs
    exact natDegree_affineHilbertPolynomial_le_of_away_range P (sep f) hregular Φ
      (dPG hp hsep) th
end
end cxX
end
section
namespace cxV
noncomputable section
open we zP aaq MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Index (A:Fin 4→nI vZ) :=Σ i:Fin 4,↥(A i)
private abbrev aRI (A:Fin 4→nI vZ) :=
 nX (Fin 4) (xB A)
private abbrev bTC:=nX (Fin 4) cH
private abbrev X5 {A:Fin 4→nI vZ} (v :Index A) :=
 nX {w:Index A // w≠v} bTC
variable {A:Fin 4→nI vZ}
private def Tg (v :Index A) :aRI A ≃+* zR (X5 v) := by
 classical
 exact (commAlgEquiv cH (Fin 4) (Index A)).toRingEquiv.trans
  ((renameEquiv bTC (Equiv.optionSubtypeNe v).symm).toRingEquiv.trans
    (xu bTC {w:Index A // w≠v}).toRingEquiv)
private theorem cbM (v :Index A) :
  Tg v (C (lV v))=Polynomial.X:= by
 classical
 simp [Tg,zyl]
private theorem cbL (v w:Index A) (h:w≠v) :
  Tg v (C (lV w))=lI (lV ⟨w,h⟩) := by
 classical
 simp [Tg,zyl,Equiv.optionSubtypeNe_symm_of_ne h]
private theorem cbI (v :Index A) (j:Fin 4) :
  Tg v (lV j)=lI (C (lV j)) := by
 classical
 simp [Tg,zyl]
private theorem cbK (v :Index A) (a :vZ) :
  Tg v (qz a 1)=lI (C (qz a 1)) := by
 simp only [monic_monomial_eq,Finsupp.prod,JW,vw ,cbI]
private def ava (A:Fin 4→nI vZ) (j:Fin 4) (a : ↥(A j)) :
   aRI A :=
 C (lV (⟨j,a⟩:Index A))*qz a.1 1
private def Nk (A:Fin 4→nI vZ) (j:Fin 4) :aRI A :=
 ∑ a : ↥(A j),ava A j a
private def aol (A:Fin 4→nI vZ) (i:Fin 4) :
  aU (aRI A) :=
 lJ (Nk A '' {j:Fin 4 | (j:ℕ)< i.val})
private def awd (v :Index A) (j:Fin 4) (a : ↥(A j)) :X5 v := by
 classical
 exact if h: (⟨j,a⟩:Index A)=v then 0
  else lV ⟨⟨j,a⟩,h⟩*C (qz a.1 1)
private def akf (v :Index A) (j:Fin 4) :X5 v :=
 ∑ a : ↥(A j),awd v j a
private theorem btC (v :Index A) (j:Fin 4) (a : ↥(A j))
  (h: (⟨j,a⟩:Index A)≠v) :
  Tg v (ava A j a)=lI (awd v j a) := by
 simp [ava,awd,h,cbL v _ h,cbK]
private theorem cbN (i j:Fin 4) (hi:0∈A i) (hji:j.val< i.val) :
   Tg (⟨i,⟨0,hi⟩⟩:Index A) (Nk A j) =
     lI (akf ⟨i,⟨0,hi⟩⟩ j) := by
 rw [Nk,akf,u5 ,u5]
 refine qx rfl fun a _=>btC _ _ _ ?_
 exact fun h=>(ne_of_lt hji) (lz (fun w:Index A=>w.1.val) h)
private theorem cbJ (i:Fin 4) (hi:0∈A i) :
   Tg (⟨i,⟨0,hi⟩⟩:Index A) (Nk A i) =
     oj+Polynomial.C (akf ⟨i,⟨0,hi⟩⟩ i) := by
 classical
 let a₀ : ↥(A i) :=⟨0,hi⟩
 let v :Index A:=⟨i,a₀⟩
 change Tg v (Nk A i)=oj+Polynomial.C (akf v i)
 have h₀:Tg v (ava A i a₀)=Polynomial.X:= by
   simp [ava,a₀,v,cbM]
 have hr₀:awd v i a₀=0:= by simp [awd,v]
 rw [Nk,akf,u5 ,u5 ,
   ← zT2 _ _ (vk a₀),
   ← zT2 _ _ (vk a₀),h₀,hr₀,p6,Gj]
 congr 1
 refine qx rfl fun a ha=>btC _ _ _ ?_
 intro h
 apply (Finset.mem_erase.mp ha).1
 exact pL (lz (fun w:Index A=>(w.2 :vZ)) h)
private theorem bWb {B:Type*} [qJ B] (J:aU B) (b:B)
  (q:zR B) (h: (oj+Polynomial.C b)*q∈J.map lI) :
  q∈J.map Polynomial.C:= by
 let f :=u8 (mD J)
 have hf :sH f=J.map Polynomial.C:= by
  dsimp only [f]
  rw [Polynomial.ker_mapRingHom,Pr]
 rw [← hf,ZK,oz] at h
 rw [← hf,ZK]
 apply (Polynomial.monic_X_add_C (mD J b)).mul_right_eq_zero_iff.mp
 simpa [f] using h
private theorem bra (i:Fin 4) (hi:0∈A i) (q:aRI A)
  (h:Nk A i*q∈aol A i) :
  q∈aol A i:= by
 let v :Index A:=⟨i,⟨0,hi⟩⟩
 let e :=Tg v
 let J:aU (X5 v) :=lJ (akf v '' {j:Fin 4 | (j:ℕ)< i.val})
 have hJ: (aol A i).map e.toRingHom=J.map Polynomial.C:= by
  dsimp only [J]
  rw [aol,y5 ,y5 ,Vs ,Vs]
  exact lz lJ (Set.image_congr fun j hj=>cbN i j hi hj)
 have hq:=zh e.toRingHom h
 change e (Nk A i*q)∈(aol A i).map e.toRingHom at hq
 rw [hJ,oz ,show e (Nk A i) =
  oj+Polynomial.C (akf v i) from cbJ i hi] at hq
 have hq' := bWb J (akf v i) (e q) hq
 rw [← hJ] at hq'
 obtain ⟨r,hr,he⟩:=(Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hq'
 exact (e.injective he) ▸ hr
private theorem bsl (A:Fin 4→nI vZ) (j:Fin 4) :
  cy (aRI A) (af A) (Nk A j)=ve A j:= by
 simp only [Nk,ava,ve,MvPolynomial.algebraMap_def,
  u5 ,MvPolynomial.map_monomial,C_mul_monomial,Qw]
theorem proof :aaq.c2 := by
 intro A hA i p hp
 let M:Submonoid (aRI A) :=(xB A)⁰.map (C (σ:=Fin 4))
 let J:=aol A i
 let f :=cy (aRI A) (af A)
 have hJ:J.map f=mo A i.val := by
   dsimp only [J]
   rw [aol,mo,y5 ,Vs]
   exact lz lJ (Set.image_congr fun j _=>bsl A j)
 obtain ⟨⟨q,s⟩,hs⟩:=IsLocalization.surj M p
 change p*f s=f q at hs
 have h:f (Nk A i*q)∈J.map f := by
   rw [oz ,show f (Nk A i)=ve A i from
     bsl A i,← hs,← uh,hJ]
   exact (mo A i.val).mul_mem_right _ hp
 obtain ⟨t,ht,htq⟩ :=
   (zZS M (af A) J _).mp h
 have hq:t*q∈J:= by
   apply bra i (hA i)
   rw [mul_left_comm]
   exact htq
 have hfp:f q∈J.map f :=
   (zZS M (af A) J q).mpr ⟨t,ht,hq⟩
 rw [hJ,← hs] at hfp
 exact (Ideal.mul_unit_mem_iff_mem _ (z0j (af A) s)).mp hfp
end
end cxV
end
section
namespace aKr
noncomputable section
open Kd
open scoped BigOperators Function
variable {ι σ:Type} [t7 ι]
abbrev Cell (T:σ→ℕ) := ∀ x,Fin (T x+1)
def aMI (T:σ→ℕ) (e :σ →₀ ℕ) :Cell T :=
 fun x=>⟨min (T x) (e x),SM (Xo _ _)⟩
def base [qy σ] {T:σ→ℕ} (p:Cell T) :σ →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm (fun x=>(p x :ℕ))
@[simp] theorem blO [qy σ] {T:σ→ℕ} (p:Cell T) (x :σ) :
   base p x=(p x :ℕ) :=
  rfl
theorem cEv [qy σ] {T:σ→ℕ} (p:Cell T) (e :σ →₀ ℕ) :
   aMI T e=p↔base p≤e ∧ ∀ x,(p x :ℕ)<T x→e x=base p x := by
 constructor
 · intro h
   have hx (x :σ) :min (T x) (e x)=(p x :ℕ) :=
     lz (fun q:Cell T=>(q x :ℕ)) h
   refine ⟨fun x => ?_,?_⟩
   · rw [blO,← hx x]
     exact min_le_right _ _
   · intro x hlt
     simp only [blO]
     have he :=hx x
     omega
 · rintro ⟨h,hf⟩
   funext x
   apply Fin.ext
   change min (T x) (e x)=(p x :ℕ)
   have hle : (p x :ℕ)≤T x :=Ef (p x).isLt
   have he : (p x :ℕ)≤e x := by simpa using h x
   by_cases hlt: (p x :ℕ)<T x
   · have hfix :e x=(p x :ℕ) := by simpa using hf x hlt
     omega
   · omega
theorem cW1 [qy σ] {T:σ→ℕ} {b e :σ →₀ ℕ} (hb : ∀ x,b x≤T x) :
  b≤base (aMI T e)↔b≤e := by
 simp only [Finsupp.le_def,blO,aMI,Xg]
 exact ⟨fun h x=>(h x).2,fun h x=>⟨hb x,h x⟩⟩
abbrev cV (slot:σ→ι) : (σ →₀ ℕ) →+ (ι→ℕ) :=
 oy (step ∘ slot)
theorem cT2 [oK σ] (slot:σ→ι) (e :σ →₀ ℕ) (i:ι) :
   cV slot e i = ∑ x∈Finset.univ.filter (fun x=>slot x=i),e x := by
 rw [Fz ,Zh,Np]
 refine qx rfl fun x _ => ?_
 by_cases h:slot x=i
 · simp [h,step]
 · simp [h,Ne.symm h,step]
theorem cR6 [oK σ] (slot:σ→ι) (a :ι→ℕ) :
    {e :σ →₀ ℕ | cV slot e=a}.Finite := by
  classical
  let f (e : {e :σ →₀ ℕ | cV slot e=a}) (x :σ) :Fin (a (slot x)+1) :=
    ⟨e.1 x,SM (by
      have h:=Pc (f := fun y :σ=>e.1 y)
        (s :=Finset.univ.filter (fun y=>slot y=slot x))
        (fun _ _=>In _) (Finset.mem_filter.mpr ⟨vk x,rfl⟩)
      rwa [← cT2,e.2] at h)⟩
  have :qy {e :σ →₀ ℕ | cV slot e=a} := Finite.of_injective f (by
    intro e g h
    exact pL (Finsupp.ext fun x=>lz (fun z=>(z x :ℕ)) h))
  exact Set.toFinite _
def alB {T:σ→ℕ} (slot:σ→ι) (p:Cell T) (a :ι→ℕ) :Set (σ →₀ ℕ) :=
 {e | aMI T e=p∧cV slot e=a}
theorem grM [oK σ] (slot:σ→ι) (A B:nI (σ →₀ ℕ))
    (hn:zJ B⊆zJ A) (T:σ→ℕ)
    (hT : ∀ b,b∈A∨b∈B → ∀ x,b x≤T x) (a :ι→ℕ) :
    DL slot A a - DL slot B a =
      ∑ᶠ p : {p:Cell T // base p∈zJ A∧base p∉zJ B},
        ((alB slot p.1 a).ncard:ℚ) := by
  classical
  let P := {p:Cell T // base p∈zJ A∧base p∉zJ B}
  let SA:Set (σ →₀ ℕ) := {e | e∈zJ A∧cV slot e=a}
  let SB:Set (σ →₀ ℕ) := {e | e∈zJ B∧cV slot e=a}
  have ho (e :σ →₀ ℕ) (C:nI (σ →₀ ℕ)) (hC : ∀ b∈C,b∈A∨b∈B) :
      base (aMI T e)∈zJ C↔e∈zJ C:= by
    change (∀ b∈C,¬ b≤base (aMI T e))↔(∀ b∈C,¬ b≤e)
    exact ⟨fun h b hb he=>h b hb ((cW1 (hT b (hC b hb))).mpr he),
      fun h b hb he=>h b hb ((cW1 (hT b (hC b hb))).mp he)⟩
  have hu:SA \ SB = ⋃ p:P,alB slot p.1 a := by
    ext e
    simp only [Set.mem_sdiff,Set.mem_iUnion]
    constructor
    · rintro ⟨⟨heA,hw⟩,heB⟩
      refine ⟨⟨aMI T e,(ho e A (fun _ hb=>Gi hb)).mpr heA,?_⟩,rfl,hw⟩
      exact fun h=>heB ⟨(ho e B (fun _ hb=>Or.inr hb)).mp h,hw⟩
    · rintro ⟨p,he,hw⟩
      have hp:=p.2
      rw [← he] at hp
      exact ⟨⟨(ho e A (fun _ hb=>Gi hb)).mp hp.1,hw⟩,
        fun h=>hp.2 ((ho e B (fun _ hb=>Or.inr hb)).mpr h.1)⟩
  have hcard:=Set.ncard_sdiff_add_ncard_of_subset
    (s :=SB) (t:=SA) (fun _ he=>⟨hn he.1,he.2⟩)
    ((cR6 slot a).subset fun _ he=>he.2)
  rw [hu,Set.ncard_iUnion_of_finite
    (fun p=>(cR6 slot a).subset fun _ he=>he.2) ?_] at hcard
  · let _:oK P:=Gk P
    change (SA.ncard:ℚ)-(SB.ncard:ℚ) = ∑ᶠ p:P,_
    rw [zNX] at hcard ⊢
    push_cast [← hcard]
    ring
  · intro p q hpq
    refine Set.disjoint_left.mpr fun e hp hq=>hpq (pL ?_)
    exact hp.1.symm.trans hq.1
end
end aKr
end
section
namespace aKr
noncomputable section
open scoped BigOperators
variable {ι σ:Type} [t7 ι] [oK σ] {T:σ→ℕ}
def free (slot:σ→ι) (p:Cell T) (i:ι) :nI σ :=
 Finset.univ.filter (fun x=>(p x :ℕ)=T x∧slot x=i)
private theorem ahR {slot:σ→ι} {p:Cell T} {i:ι} {x :σ} :
  x∈free slot p i↔(p x :ℕ)=T x∧slot x=i:= by
 simp [free]
private def extras (slot:σ→ι) (p:Cell T) (e :σ →₀ ℕ)
 (i:ι) (x :free slot p i) :ℕ:=e x - p x
private def extend (slot:σ→ι) (p:Cell T)
  (d : ∀ i,free slot p i→ℕ) (x :σ) :ℕ :=
 if h: (p x :ℕ)=T x then d (slot x) ⟨x,ahR.mpr ⟨h,rfl⟩⟩ else 0
private def restore (slot:σ→ι) (p:Cell T)
  (d : ∀ i,free slot p i→ℕ) :σ →₀ ℕ :=
 base p+Finsupp.equivFunOnFinite.symm (extend slot p d)
private theorem fW6 (slot:σ→ι) (p:Cell T) (d : ∀ i,free slot p i→ℕ) :
  aMI T (restore slot p d)=p:= by
 apply (cEv _ _).mpr
 refine ⟨le_add_right (le_refl _),?_⟩
 intro x hx
 simp [restore,extend,ne_of_lt hx]
private theorem c8D (slot:σ→ι) (p:Cell T) (e :σ →₀ ℕ)
   (h:aMI T e=p) :
   restore slot p (extras slot p e)=e := by
 obtain ⟨hle,hfix⟩:=(cEv _ _).mp h
 ext x
 by_cases hx : (p x :ℕ)=T x
 · have hpx : (p x :ℕ)≤e x := by simpa using hle x
   simp [restore,extend,extras,hx]
   omega
 · have hlt: (p x :ℕ)<T x :=
     GB (Ef (p x).isLt) hx
   simpa [restore,extend,hx] using (hfix x hlt).symm
private theorem cNU (slot:σ→ι) (p:Cell T) (d : ∀ i,free slot p i→ℕ)
  (i:ι) (x :free slot p i) :extend slot p d x=d i x := by
 obtain ⟨hT,hi⟩:=ahR.mp x.2
 let y :free slot p (slot x) :=⟨x,ahR.mpr ⟨hT,rfl⟩⟩
 have hh (j:ι) (z :free slot p j) (h:j=i) (hz : (z :σ)=x) :d j z=d i x := by
  subst j
  exact lz (d i) (pL hz)
 rw [extend,dite_eq_left hT]
 exact hh _ y hi rfl
private theorem c8E (slot:σ→ι) (p:Cell T)
   (d : ∀ i,free slot p i→ℕ) (i:ι) :
   cV slot (restore slot p d) i=cV slot (base p) i + ∑ x :free slot p i,d i x := by
 rw [restore,oY ,Vq]
 congr 1
 rw [cT2 slot _ i]
 have hsub:free slot p i⊆Finset.univ.filter (fun x=>slot x=i) :=
   fun x hx=>Finset.mem_filter.mpr ⟨vk x,(ahR.mp hx).2⟩
 have hz (x :σ) (hx :x∈Finset.univ.filter (fun x=>slot x=i))
     (hn:x∉free slot p i) :extend slot p d x=0:= by
   have hne : (p x :ℕ)≠T x := fun he=>hn (ahR.mpr ⟨he,(Finset.mem_filter.mp hx).2⟩)
   simp [extend,hne]
 change (∑ x∈Finset.univ.filter (fun x=>slot x=i),extend slot p d x)= _
 rw [← Wl hsub hz,← zKD (free slot p i) (extend slot p d)]
 exact qx rfl fun x _=>cNU slot p d i x
private def bWA (slot:σ→ι) (p:Cell T) (a :ι→ℕ)
  (ha :cV slot (base p)≤a) :
  alB slot p a ≃
    (∀ i,{d:free slot p i→ℕ // ∑ x,d x=a i - cV slot (base p) i}) where
 toFun e i:=⟨extras slot p e i,by
  have h:=(c8E slot p (extras slot p e) i).symm
  rw [c8D slot p e e.2.1,e.2.2] at h
  omega⟩
 invFun d:=⟨restore slot p (fun i=>(d i).1),fW6 slot p _,by
  funext i
  rw [c8E,(d i).2]
  exact GR (ha i)⟩
 left_inv e :=pL (c8D slot p e e.2.1)
 right_inv d:= by
  funext i
  apply pL
  funext x
  change restore slot p (fun j=>(d j).1) x-(p x :ℕ)=(d i).1 x
  rw [restore,Dv,blO]
  change (p x :ℕ)+extend slot p (fun j=>(d j).1) x-(p x :ℕ)=(d i).1 x
  rw [cNU,z7K]
theorem bWC [oK ι] (slot:σ→ι) (p:Cell T) (a :ι→ℕ)
   (ha :cV slot (base p)≤a) :
   (alB slot p a).ncard =
     ∏ i,(free slot p i).card.multichoose (a i - cV slot (base p) i) := by
 classical
 rw [← JM,Nj (bWA slot p a ha),Nat.card_pi]
 refine Dz rfl fun i _ => ?_
 rw [← Nj (Sym.equivNatSumOfFintype (free slot p i)
   (a i - cV slot (base p) i)),Sym.natCard_sym_eq_multichoose,XB]
 exact lz (fun n=>n.multichoose (a i - cV slot (base p) i)) (Fintype.card_coe _)
end
end aKr
end
section
namespace aKr
noncomputable section
open Kd Filter
open scoped BigOperators
variable {ι:Type} [oK ι] [t7 ι]
private def ab1 (n d:ℕ) :ℚ :=
 if d=0 then 0 else (n.choose (d - 1) :ℚ)
private def model (w c d a :ι→ℕ) :ℚ :=
 ∏ i,ab1 (a i+c i - w i) (d i)
private theorem dy4 (n d:ℕ) :
   ab1 (n+1) d-ab1 n d=ab1 n (d - 1) := by
 cases d with
 | zero=>simp [ab1]
 | succ d =>
   cases d with
   | zero=>simp [ab1]
   | succ d =>
     simp only [ab1,Nat.succ_ne_zero,ite_false,Nat.succ_sub_one,Nat.choose_succ_succ']
     push_cast
     ring
private theorem eA8 (w c d:ι→ℕ) (i:ι) :
   (fun a=>model w c d (a+step i) - model w c d a) =ᶠ[pG]
     model w c (Wm d i (d i - 1)) := by
 filter_upwards [ZJ w] with a ha
 let rest (d' a' : ι→ℕ) :=
   ∏ j∈Finset.univ.erase i,ab1 (a' j+c j - w j) (d' j)
 have hfactor (d' a' : ι→ℕ) :
     model w c d' a' = ab1 (a' i+c i - w i) (d' i)*rest d' a' :=
   (Finset.mul_prod_erase _ _ (vk i)).symm
 have hshift:rest d (a+step i)=rest d a := by
   refine Dz rfl fun j hj => ?_
   have hne :=(Finset.mem_erase.mp hj).1
   simp [step,hne]
 have hupdate :rest (Wm d i (d i - 1)) a=rest d a := by
   refine Dz rfl fun j hj => ?_
   rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
 have htop: (a+step i) i+c i - w i=(a i+c i - w i)+1 := by
   simp only [Vq,step,Pi.single_eq_same]
   have h:w i≤a i:=ha i
   omega
 simp only [hfactor,hshift,hupdate,htop,Function.update_self]
 rw [← sub_mul,dy4]
omit [oK ι] in
private theorem d3y {p: (ι→ℕ)→Prop} (h : ∀ᶠ a in pG,p a) (i:ι) :
  ∀ᶠ a in pG,p (a+step i) := by
 obtain ⟨a,h⟩:=eventually_atTop.mp h
 refine eventually_atTop.mpr ⟨a,fun b hb=>h _ (hb.trans ?_)⟩
 exact fun j=>zi _ _
omit [oK ι] in
private theorem cKi (used :List ι) {H G: (ι→ℕ)→ℚ} (h:H =ᶠ[pG] G) :
   uU used H =ᶠ[pG] uU used G:= by
 induction used with
 | nil=>exact h
 | cons i used ih =>
   filter_upwards [d3y ih i,ih] with a h₁ h₂
   exact congrArg₂ (· - ·) h₁ h₂
omit [oK ι] in
private theorem b0h (used :List ι) (H : (ι→ℕ)→ℚ) (i:ι) (a :ι→ℕ) :
   uU used (fun b=>H (b+step i) - H b) a =
    uU used H (a+step i) - uU used H a := by
 induction used generalizing a with
 | nil=>rfl
 | cons j used ih =>
   simp only [uU,ih]
   rw [Kp a (step j) (step i)]
   ring
private theorem eA7 (used :List ι) (w c d:ι→ℕ) :
   ∀ᶠ a in pG,0≤uU used (model w c d) a := by
 induction used generalizing d with
 | nil =>
   exact Eventually.of_forall fun a =>
     Finset.prod_nonneg fun j _=> by unfold ab1; split <;> positivity
 | cons i used ih =>
   filter_upwards [cKi used (eA8 w c d i),ih (Wm d i (d i - 1))]
     with a he hn
   rw [b0h] at he
   change 0≤uU used (model w c d) (a+step i) - uU used (model w c d) a
   rwa [he]
private def bWB (w d:ι→ℕ) :nX ι ℚ :=
 ∏ i,if d i=0 then 0 else
   (zcb ℚ (d i - 1) (w i)).eval₂ nq (lV i)
omit [t7 ι] in
private theorem d1V (w d:ι→ℕ) {a :ι→ℕ} (ha :w≤a) :
   p5 (fun i=>(a i:ℚ)) (bWB w d) =
     model w (fun i=>d i - 1) d a := by
 let E :=p5 (fun i=>(a i:ℚ))
 have hC:E.comp nq=LQ ℚ:= by
   apply xW
   intro q
   simp [E]
 simp only [bWB,JW,model]
 refine Dz rfl fun i _ => ?_
 by_cases hi:d i=0
 · simp [ab1,hi]
 · simp only [ab1,hi,ite_false]
   change E (_:nX ι ℚ)= _
   rw [Y4 ,hC,Gr]
   exact zg1 ℚ _
     ((ha i).trans (zi _ _))
private theorem dy3 (d a w:ℕ) (h:w<a) :
   (d.multichoose (a - w) :ℚ)=ab1 (a+(d - 1) - w) d:= by
 cases d with
 | zero =>
   rw [show a - w=(a - w - 1)+1 by omega,zGT]
   simp [ab1]
 | succ d =>
   simp only [z4m,ab1,Nat.succ_ne_zero,ite_false,Nat.succ_sub_one]
   rw [show d+1+(a - w) - 1=(a - w)+d by omega,Nat.choose_symm_add,
     show (a - w)+d=a+d - w by omega]
omit [oK ι] in
private theorem dV3 {β:Type} (s :nI β) (H :β→(ι→ℕ)→ℚ)
   (used :List ι) (a :ι→ℕ) :
   uU used (fun b => ∑ p∈s,H p b) a = ∑ p∈s,uU used (H p) a := by
 induction used generalizing a with
 | nil=>rfl
 | cons i used ih=>simp only [uU,ih,Finset.sum_sub_distrib]
theorem proof :Kd.c1 := by
 intro ι σ _ _ _ slot A B hn
 classical
 let _:oK σ:=Gk σ
 let T (x :σ) :=max (A.sup fun b=>b x) (B.sup fun b=>b x)
 have hT (b:σ →₀ ℕ) (hb:b∈A∨b∈B) (x :σ) :b x≤T x :=
   hb.elim (fun h=>(WX (f := fun z :σ →₀ ℕ=>z x) h).trans (le_max_left _ _))
     (fun h=>(WX (f := fun z :σ →₀ ℕ=>z x) h).trans (le_max_right _ _))
 let P := {p:Cell T // base p∈zJ A∧base p∉zJ B}
 let _:oK P:=Gk P
 let w (p:P) :=cV slot (base p.1)
 let d (p:P) (i:ι) :=(free slot p.1 i).card
 let F (p:P) :=model (w p) (fun i=>d p i - 1) (d p)
 have hcell (p:P) : ∀ᶠ a in pG,((alB slot p.1 a).ncard:ℚ)=F p a := by
   filter_upwards [ZJ (fun i=>w p i+1)] with a ha
   have hl (i:ι) :w p i<a i:=ha i
   rw [bWC slot p.1 a (fun i=>(hl i).le),Nat.cast_prod]
   exact Dz rfl fun i _=>dy3 _ _ _ (hl i)
 have hsum: (fun a=>DL slot A a - DL slot B a) =ᶠ[pG]
     (fun a => ∑ p:P,F p a) := by
   filter_upwards [eventually_all.mpr hcell] with a ha
   rw [grM slot A B hn T hT]
   change (∑ᶠ p:P,_)= _
   rw [zNX]
   exact qx rfl fun p _=>ha p
 refine ⟨⟨∑ p:P,bWB (w p) (d p),?_⟩,?_⟩
 · filter_upwards [hsum,eventually_all.mpr fun p:P=>ZJ (w p)] with a h ha
   rw [h,u5]
   exact qx rfl fun p _=>d1V _ _ (ha p)
 · intro used
   filter_upwards [cKi used hsum,
     eventually_all.mpr fun p:P=>eA7 used (w p) _ (d p)] with a h ha
   rw [h,dV3]
   exact zlo fun p _=>ha p
end
end aKr
end
section
namespace Jq
noncomputable section
open dN MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem a8M {σ:Type} (s :σ→Fin 5) (m:FR σ)
    (J:aU (nX σ c9)) (hJ:J.IsHomogeneous (dO s)) (t:jJ) :
    KQ s J t =
      {a∈m.standardExponents J | oy (jT s) a=t}.ncard:= by
  let A := {a∈m.standardExponents J | oy (jT s) a=t}
  let S:=yJ c9 A
  let T:=(dO s t).map (Fa c9 J).toLinearMap
  let L:S →ₗ[c9] T :=
    ((Fa c9 J).toLinearMap.domRestrict S).codRestrict T fun z =>
      ⟨z.val,fun _ he=>(z.property (mem_support_iff.mpr he)).2,rfl⟩
  have hinj:p9 L:= by
    intro x y h
    apply pL
    apply m.eq_of_mem_standardSpace_of_sub_mem
    · exact fun _ ha=>(x.property ha).1
    · exact fun _ ha=>(y.property ha).1
    · exact Ideal.Quotient.eq.mp (lz C4 h)
  have hsurj:vh L:= by
    intro y
    obtain ⟨b,hb,hby⟩:=y.property
    obtain ⟨q,hq,hbq,_⟩:=m.exists_mem_standardSpace_sub_mem J b
    let r :=Ar (jT s) t q
    have hr :r∈S:= by
      intro a ha
      have hw:r.IsWeightedHomogeneous (jT s) t :=
        zmP t q
      refine ⟨hq ?_,hw (mem_support_iff.mp ha)⟩
      change a∈(Ar (jT s) t q).support at ha
      rw [z66] at ha
      exact (Finset.mem_filter.mp ha).1
    have hbr :b - r∈J:= by
      have hc:=MK _ _ hJ hbq t
      rwa [Av,XG (show
        b.IsWeightedHomogeneous (jT s) t from hb)] at hc
    exact ⟨⟨r,hr⟩,pL ((Ideal.Quotient.eq.mpr hbr).symm.trans hby)⟩
  let e :=zD9 L ⟨hinj,hsurj⟩
  change G1 c9 T=A.ncard
  rw [← e.finrank_eq,zUF (zzc c9 A),
    JM]
theorem a4h
    (hc : ∀ (σ:Type) [qy σ] (s :σ→Fin 5) (A C:nI (σ →₀ ℕ)),
      zJ C⊆zJ A → ∃ p q:Form,
        PA p (fun t=>DL s A t) ∧
        PA q (fun t=>DL s C t)∧OQ (p - q))
    (σ:Type) [qy σ] (s :σ→Fin 5) (J K:aU (nX σ c9))
    (hJ:J.IsHomogeneous (dO s)) (hK:K.IsHomogeneous (dO s)) (hJK:J≤K) :
    ∃ p q:Form,PA p (fun t=>KQ s J t) ∧
      PA q (fun t=>KQ s K t)∧OQ (p - q) := by
  let _:=Gk σ
  let _:LinearOrder σ:=zEZ (G8 σ) (G8 σ).injective
  let m:FR σ:=zwf
  obtain ⟨A,hA⟩:=m.exists_finset_standardExponents_iff J
  obtain ⟨C,hC⟩:=m.exists_finset_standardExponents_iff K
  have hJA:m.standardExponents J=zJ A:=Set.ext hA
  have hKC:m.standardExponents K=zJ C:=Set.ext hC
  have hsub:zJ C⊆zJ A:= by
    rw [← hJA,← hKC]
    intro a ha p hp
    exact ha p (hJK hp)
  obtain ⟨p,q,hp,hq,hpq⟩:=hc σ s A C hsub
  have hilbertJ (t:jJ) :KQ s J t=DL s A t:= by
    rw [a8M s m J hJ t,hJA]
    rfl
  have hilbertK (t:jJ) :KQ s K t=DL s C t:= by
    rw [a8M s m K hK t,hKC]
    rfl
  exact ⟨p,q,by simpa only [hilbertJ] using hp,by simpa only [hilbertK] using hq,hpq⟩
end
end Jq
end
section
namespace cyD
noncomputable section
open dN Jq XT as7
open Kd (step uU)
open MvPolynomial Filter
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private abbrev coords (a :y8) :Fin 5→ℕ:=Uf a
private theorem dPV (a :y8) (i:Fin 4) :
  coords (a+advance i)=coords a+step i.castSucc:= by
 funext j
 change Uf (a+advance i) j=Uf a j+step i.castSucc j
 rw [c06,eEd,Dv]
 simp [zY,step,EK,Pi.single_apply,eq_comm]
private theorem d3z {p: (Fin 5→ℕ)→Prop}
   (h : ∀ᶠ t in pG,p t) : ∀ᶠ a in pG,p (coords a) := by
 obtain ⟨t,ht⟩:=eventually_atTop.mp h
 refine eventually_atTop.mpr ⟨(t (pC 4),fun i=>t i.castSucc),fun a ha=>ht _ ?_⟩
 intro j
 refine G0 ?_ (fun i => ?_) j
 · simpa only [coords,bsP] using ha.1
 · simpa only [coords,b9z] using ha.2 i
private theorem b0h (dirs :List (Fin 5)) (H : (Fin 5→ℕ)→ℚ)
   (i:Fin 5) (t:Fin 5→ℕ) :
   uU dirs (fun u=>H (u+step i) - H u) t =
     uU dirs H (t+step i) - uU dirs H t:= by
 induction dirs generalizing t with
 | nil=>rfl
 | cons j dirs ih =>
   simp only [uU,ih]
   rw [Kp t (step j) (step i)]
   ring
private theorem dWT (dirs :List (Fin 4)) (H : (Fin 5→ℕ)→ℚ)
   (a :y8) :
   gI dirs (fun b=>(H (coords b) :ℝ)) a =
     (uU (dirs.map uz) H (coords a) :ℝ) := by
 induction dirs generalizing H with
 | nil=>rfl
 | cons i dirs ih =>
   change gI dirs (fun b=>(H (coords (b+advance i)) :ℝ)-(H (coords b) :ℝ)) a= _
   simp only [dPV,← Rat.cast_sub]
   rw [ih (fun t=>H (t+step i.castSucc) - H t),b0h,List.map_cons,uU]
private theorem gL6 {σ:Type} [oK σ] (s :σ→Fin 5) (e :σ →₀ ℕ) :
  (⇑(oy (jT s) e) :Fin 5→ℕ)=oy (step ∘ s) e := by
 funext j
 rw [Fz ,Fz ,Xu,Zh]
 refine qx rfl fun v _ => ?_
 simp [jT,zY,step,Pi.smul_apply,EK,Pi.single_apply,eq_comm]
private theorem c6B {σ:Type} [oK σ] (s :σ→Fin 5) (m:FR σ)
  (I:aU (nX σ c9)) (hI:I.IsHomogeneous (dO s))
  (A:nI (σ →₀ ℕ)) (hA:m.standardExponents I=Kd.zJ A)
  (a :y8) :P9 s I a=(Kd.DL s A (coords a) :ℝ) := by
 rw [P9,a8M s m I hI,hA]
 simp only [Kd.DL,Rat.cast_natCast]
 apply lz (fun S:Set (σ →₀ ℕ)=>(S.ncard:ℝ))
 ext e
 change (_∧oy (jT s) e=Uf a) ↔
  (_∧oy (step ∘ s) e=coords a)
 refine and_congr_right fun _ => ?_
 rw [← gL6 s e]
 exact ⟨fun h=>lz (fun t:jJ=>(⇑t:Fin 5→ℕ)) h,
  fun h=>DFunLike.coe_injective h⟩
theorem proof :as7.c1 := by
 classical
 intro σ _ s I J hI hJ hIJ k
 let _:=Gk σ
 let _:LinearOrder σ:=zEZ (G8 σ) (G8 σ).injective
 let m:FR σ:=zwf
 obtain ⟨A,hA⟩:=m.exists_finset_standardExponents_iff I
 obtain ⟨B,hB⟩:=m.exists_finset_standardExponents_iff J
 have hIA:m.standardExponents I=Kd.zJ A:=Set.ext hA
 have hJB:m.standardExponents J=Kd.zJ B:=Set.ext hB
 have hBA:Kd.zJ B⊆Kd.zJ A:= by
  rw [← hIA,← hJB]
  intro e he f hf
  exact he f (hIJ hf)
 let H (t:Fin 5→ℕ) :=Kd.DL s A t - Kd.DL s B t
 let dirs :=acC k
 have hH : (fun a=>P9 s I a-P9 s J a)=fun a=>(H (coords a) :ℝ) := by
  funext a
  rw [c6B s m I hI A hIA,c6B s m J hJ B hJB]
  exact (Rat.cast_sub _ _).symm
 have hp : ∀ᶠ t in pG,0≤uU (dirs.map uz) H t :=
  (aKr.proof s A B hBA).2 _
 rw [hH]
 filter_upwards [d3z hp] with a ha
 rw [dWT]
 exact_mod_cast ha
end
end cyD
end
section
namespace bzL
open wH aqa
open Ideal IsLocalRing MvPolynomial RingTheory.Sequence
open CategoryTheory Abelian
open scoped Pointwise
private noncomputable abbrev coord:Fin 3→Lower :=lV
private theorem a9t {s :Set (Fin 3)} {i:Fin 3} (hi:i∉s)
  (p:oZ) (hp:coord i*p∈span (coord '' s)) :p∈span (coord '' s) := by
 rw [mem_ideal_span_X_image] at hp ⊢
 intro m hm
 have hcoeff :=coeff_X_mul m i p
 have hmem:Pk i 1+m∈(coord i*p).support :=
  mem_support_iff.mpr (hcoeff.trans_ne (mem_support_iff.mp hm))
 obtain ⟨j,hj,hne⟩:=hp _ hmem
 have hji:i≠j:= fun e=>hi (e.symm ▸ hj)
 exact ⟨j,hj,by simpa [Dv,EK,hji] using hne⟩
private theorem a9u :
   P7 oZ ([coord 0,coord 1,coord 2] :List oZ) := by
 classical
 have step (s :Set (Fin 3)) (i:Fin 3) (hi:i∉s) :
     wY (oZ ⧸ span (coord '' s)) (coord i) :=
   (TH _ _).mpr (a9t hi)
 have h₀: (zE ([] :List oZ)•(⊤ : u9 oZ oZ)) =
     span (coord '' (∅ : Set (Fin 3))) := by
   rw [FV,FU,Ideal.ofList_nil,Set.image_empty,Ideal.span_empty]
 have h₁: (zE [coord 0]•(⊤ : u9 oZ oZ)) =
     span (coord '' ({0} : Set (Fin 3))) := by
   rw [FV,FU,N0 ,Cy]
 have h₂: (zE [coord 0,coord 1]•(⊤ : u9 oZ oZ)) =
     span (coord '' ({0,1} : Set (Fin 3))) := by
   rw [FV,FU,z2L,N0 ,
     z6c,Cy ,OJ]
 refine ⟨?_⟩
 intro i hi
 have hib:i<3:=hi
 interval_cases i
 · change wY (oZ ⧸ (zE []•(⊤ : u9 oZ oZ))) (coord 0)
   exact ((Gn _ _ h₀).isSMulRegular_congr (coord 0)).mpr
     (step ∅ 0 (by simp))
 · change wY (oZ ⧸ (zE [coord 0]•(⊤ : u9 oZ oZ)))
     (coord 1)
   exact ((Gn _ _ h₁).isSMulRegular_congr (coord 1)).mpr
     (step {0} 1 (by simp))
 · change wY (oZ ⧸ (zE [coord 0,coord 1]•(⊤ : u9 oZ oZ)))
     (coord 2)
   exact ((Gn _ _ h₂).isSMulRegular_congr (coord 2)).mpr
     (step {0,1} 2 (by simp))
private noncomputable def translation (y :Sz) :oZ ≃ₐ[cH] Lower :=
 AlgEquiv.ofAlgHom (aeval (fun i=>coord i - C (y i))) (aeval (fun i=>coord i+C (y i)))
  (Zf (fun i=> by simp))
  (Zf (fun i=> by simp))
set_option maxHeartbeats 1000000 in
theorem d4K (q:Rm oZ) (hh:q.asIdeal.height=3) :
   ∃ rs :List (t6 q),rs.length=3 ∧
     (∀ x∈rs,x∈oD (t6 q))∧IsRegular (t6 q) rs := by
 classical
 have hd:EP oZ=3:= by
   rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
   simp
 have hd' : EP oZ=((3:ℕ∞) :WithBot ℕ∞) :=hd
 have :FiniteRingKrullDim Lower :=finiteRingKrullDim_iff_ne_bot_and_top.mpr (by
   rw [hd']
   refine ⟨WithBot.coe_ne_bot,?_⟩
   rw [← WithBot.coe_top]
   exact fun h=>ENat.natCast_ne_top 3 (WithBot.coe_inj.mp h))
 have hq:q.asIdeal.IsMaximal:=Ideal.isMaximal_of_height_eq_ringKrullDim (by
   rw [hd,hh]
   rfl)
 obtain ⟨y,hy⟩ :=
   MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (K:=cH) hq
 let e :=(translation y).toRingEquiv
 let rs :List Lower :=[coord 0,coord 1,coord 2]
 have hcongr :List.Forall₂ (fun (r s :oZ) => ∀ x :oZ,e (r•x)=s•e x)
     rs (rs.map e) :=
   List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x=>e.map_mul r x)
 have hwr :P7 oZ (rs.map e) :=
   (e.toAddEquiv.isWeaklyRegular_congr hcongr).mp a9u
 have hm (x :oZ) (hx :x∈rs.map e) :x∈q.asIdeal:= by
   obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hx
   have hw' : ∃ i:Fin 3,w=coord i:= by
     simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hw
     rcases hw with rfl | rfl | rfl
     · exact ⟨0,rfl⟩
     · exact ⟨1,rfl⟩
     · exact ⟨2,rfl⟩
   obtain ⟨i,rfl⟩:=hw'
   rw [hy,mem_vanishingIdeal_singleton_iff]
   change aeval y (aeval (fun j=>coord j - C (y j)) (coord i))=0
   simp
 have hreg:=hwr.isRegular_of_isLocalization_of_mem (t6 q) q.asIdeal hm
 refine ⟨(rs.map e).map (cy oZ (t6 q)),by simp [rs],?_,hreg⟩
 intro x hx
 obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hx
 exact (zRt (t6 q) q.asIdeal w).mpr (hm w hw)
universe u
private theorem aHM {R:Type u} [qJ R] (N M:ModuleCat.{u} R)
  {a :R} (ha :wY M a) {n:ℕ}
  (h : ∀ i<n+1,zS (Ext N M i)) :
  ∀ i<n,zS (Ext N (Kh R (yL a M)) i) := by
 intro i hi
 have h₀:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
 have h₁:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i+1) (by omega))
 exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
  (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i+1) rfl)
  (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)
theorem fVH {R:Type u} [qJ R] [MS R] [PM R]
    {a b:R} (ha :wY R a) (hb:wY (yL a R) b)
    (rs :List R) (hlen:rs.length=3) (hmem : ∀ x∈rs,x∈oD R)
    (hreg:IsRegular R rs) :
    ∃ r∈oD R,wY (R ⧸ span ({a,b} : Set R)) r := by
  let N :=Kh R (R ⧸ oD R)
  let M:=Kh R R
  let M₁:=Kh R (yL a R)
  let M₂:=Kh R (yL b (yL a R))
  have hAnn:Module.annihilator R N=oD R:=Ideal.annihilator_quotient
  have hSupp:Module.support R N⊆PrimeSpectrum.zeroLocus (oD R) := by
    rw [Module.support_eq_zeroLocus,hAnn]
  have hlt:oD R•(⊤ : u9 R M) < ⊤ := by
    change oD R•(⊤ : aU R) < ⊤
    rw [FV,FU]
    exact (zHl R).ne_top.lt_top
  have h₀ : ∀ i<3,zS (Ext N M i) := by
    rw [← hlen]
    exact ModuleCat.subsingleton_ext_of_exists_isRegular _ N hSupp M hlt rs hmem hreg
  have h₁ : ∀ i<2,zS (Ext N M₁ i) :=aHM N M ha h₀
  have h₂ : ∀ i<1,zS (Ext N M₂ i) :=aHM N M₁ hb h₁
  have hHom:zS (N →ₗ[R] M₂) :=
    (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp (h₂ 0 (by decide))
  obtain ⟨r,hr,hreg₂⟩:=IsSMulRegular.subsingleton_linearMap_iff.mp hHom
  have e : (R ⧸ span ({a,b} : Set R)) ≃ₗ[R] yL b (yL a R) := by
    have hfirst: (zE [a,b]•(⊤ : u9 R R))=span ({a,b} : Set R) := by
      rw [FV,FU,z2L,N0 ,
        OJ]
    have hsecond: (zE [b]•(⊤ : u9 R (yL a R)))=b • ⊤ := by
      rw [N0 ,zQT]
    have e' := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner R a [b]
    rwa [hfirst,hsecond] at e'
  exact ⟨r,hAnn ▸ hr,(e.isSMulRegular_congr r).mpr hreg₂⟩
end bzL
end
section
namespace bzL
open wH aqa
open Ideal IsLocalRing
open scoped Pointwise
section LocalRing
variable {R:Type*} [qJ R] [MS R] [PM R]
private theorem aVi {I:aU R} (hI:I.radical=oD R)
  (s :nI R) (hs : (↑s :Set R)⊆oD R) (hle :I≤ span (↑s :Set R)) :
  (oD R).height≤ s.card:= by
 apply Ideal.height_le_card_of_mem_minimalPrimes_span_finset
 refine ⟨⟨z9,span_le.mpr hs⟩,?_⟩
 intro p hp _
 exact hI ▸ hp.1.radical_le_iff.mpr (hle.trans hp.2)
omit [MS R] [PM R] in
private theorem c5p (a :R) :
  a•(⊤ : u9 R R)=(span {a} : aU R) := by
 rw [← zQT,FV,FU]
private theorem c3D [G2 R] [LP R] {a b:R}
   (s :nI R) (hrad: (span (t8 a (t8 b (↑s :Set R)))).radical=oD R)
   (hheight: (↑(s.card+1) :ℕ∞)<(oD R).height) :
   wY R a∧wY (yL a R) b:= by
 classical
 let I:=span (t8 a (t8 b (↑s :Set R)))
 have hm: (t8 a (t8 b (↑s :Set R)))⊆oD R:= fun _ hx =>
   hrad ▸ I.le_radical (Il hx)
 have hsmall (x :R) (hx :x∈oD R) (hle :I≤ span (↑(t8 x s) :Set R)) :
     False := by
   have hs : (↑(t8 x s) :Set R)⊆oD R:= by
     intro z hz
     simp only [Finset.coe_insert,zP8] at hz
     rcases hz with rfl | hz
     · exact hx
     · exact hm (by simp [hz])
   exact hheight.not_ge ((aVi hrad (t8 x s) hs hle).trans
     (by exact_mod_cast Finset.card_insert_le x s))
 have ha :a≠0:= by
   intro hzero
   apply hsmall b (hm (by simp))
   simp [I,hzero]
 have hab:IsRelPrime a b:= by
   apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors ha).mpr
   intro d hda hdb hd
   apply hsmall d ((IsLocalRing.mem_maximalIdeal d).mpr hd.not_isUnit)
   apply span_le.mpr
   intro z hz
   simp only [zP8] at hz
   have hdmem:d∈span (↑(t8 d s) :Set R) :=Il (by simp)
   rcases hz with rfl | rfl | hz
   · exact Ideal.mem_of_dvd _ hda hdmem
   · exact Ideal.mem_of_dvd _ hdb hdmem
   · exact Il (by simp [hz])
 refine ⟨(zUH ha).isSMulRegular,?_⟩
 apply ((Gn _ _ (c5p a)).isSMulRegular_congr b).mpr
 rw [TH]
 intro x hx
 exact mem_span_singleton.mpr (hab.dvd_of_dvd_mul_left (mem_span_singleton.mp hx))
private theorem a1X [G2 R] [LP R] {a b x :R}
  (hh: (oD R).height=2) (hrad: (span ({a,b} : Set R)).radical=oD R)
  (hx :b*x∈span ({a} : Set R)) :x∈span ({a} : Set R) := by
 have hp:=(c3D (a :=a) (b:=b) ∅ (by simpa using hrad)
  (by rw [hh]; norm_num)).2
 have hq:=((Gn _ _ (c5p a)).isSMulRegular_congr b).mp hp
 exact Ww hq hx
private theorem dEm [G2 R] [LP R] {a b c x :R}
   (hh: (oD R).height=3) (hrad: (span ({a,b,c} : Set R)).radical=oD R)
   (href : ∃ rs :List R,rs.length=3 ∧
     (∀ z∈rs,z∈oD R)∧RingTheory.Sequence.IsRegular R rs)
   (hx :c*x∈span ({a,b} : Set R)) :x∈span ({a,b} : Set R) := by
 classical
 obtain ⟨ha,hb⟩:=c3D (a :=a) (b:=b) {c} (by simpa using hrad)
   (by rw [hh]; norm_num)
 obtain ⟨rs,hlen,hmem,hreg⟩:=href
 obtain ⟨r,hr,hregular⟩:=fVH ha hb rs hlen hmem hreg
 have hrad' : (span (t8 c ({a,b} : Set R))).radical=oD R:= by
   rw [Set.insert_comm c a,Yi c b]
   exact hrad
 have hr' : r∈(span (t8 c ({a,b} : Set R))).radical:=hrad'.symm ▸ hr
 obtain ⟨k,hk⟩:=Ideal.mem_radical_iff.mp hr'
 rw [OJ] at hk
 obtain ⟨v,hv,w,hw,hsum⟩:=Submodule.mem_sup.mp hk
 obtain ⟨t,rfl⟩:=mem_span_singleton.mp hv
 apply Ww (hregular.pow k)
 change r^k*x∈span ({a,b} : Set R)
 rw [← hsum,add_mul,Iw c t,uh]
 exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (zx6 _ _ hw)
end LocalRing
private theorem c8e {R:Type*} [qJ R] {n:ℕ}
  (g:Fin (n+1)→R) :K7 g 0=span (Re (Fin.tail g)) := by
 unfold K7
 congr 1
 ext z
 simp [Set.mem_image,Set.mem_range,Fin.exists_fin_succ,Fin.tail]
private theorem fVN {R ι:Type*} [qJ R] (f :ι→R)
   (e :ι ≃ ι) (j:ι) :K7 (f ∘ e) j=K7 f (e j) := by
 unfold K7
 congr 1
 ext x
 constructor
 · rintro ⟨k,hk,rfl⟩
   exact ⟨e k,fun he=>hk (e.injective he),rfl⟩
 · rintro ⟨k,hk,rfl⟩
   obtain ⟨l,rfl⟩:=e.surjective k
   exact ⟨l,fun he=>hk (lz e he),rfl⟩
private theorem cU8 {R:Type*} [qJ R] [PM R] {n:ℕ}
   (h : ∀ (g:Fin (n+1)→R),(span (Re g)).radical=oD R →
     ∀ x,g 0*x∈K7 g 0→x∈K7 g 0)
   (f :Fin (n+1)→R) (hf : (span (Re f)).radical=oD R)
   (i:Fin (n+1)) (x :R) (hx :f i*x∈K7 f i)
   : x∈K7 f i:= by
 classical
 let e :=Equiv.swap (0:Fin (n+1)) i
 have he :e 0=i:=Equiv.swap_apply_left _ _
 have hrem:K7 (f ∘ e) 0=K7 f i:= by
   rw [fVN,he]
 rw [← hrem] at hx ⊢
 exact h (f ∘ e) (by rw [EquivLike.range_comp]; exact hf) x (by simpa only [Sd ,he] using hx)
theorem proof :aqa.c1 := by
 classical
 intro n hn q hh f hf i x hx
 have hheight: (oD (t6 q)).height=n:= by
   apply WithBot.coe_inj.mp
   rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (t6 q),hh]
 rcases hn with rfl | rfl
 · refine cU8 (n:=1) (fun g hg y hy => ?_) f hf i x hx
   rw [c8e,Aa] at hy ⊢
   rw [Aa ,Aa] at hg
   simp only [zwy,← zrN] at hg hy ⊢
   change y∈span ({g 1} : Set (t6 q))
   apply a1X hheight (a :=g 1) (b:=g 0) ?_ hy
   change (span ({g 1,g 0} : Set (t6 q))).radical= _
   rw [show ({g 1,g 0} : Set (t6 q)) = {g 0,g 1} from Yi _ _]
   exact hg
 · refine cU8 (n:=2) (fun g hg y hy => ?_) f hf i x hx
   rw [c8e,Aa ,Aa] at hy ⊢
   rw [Aa ,Aa ,Aa] at hg
   simp only [zwy,← zrN] at hg hy ⊢
   change y∈span ({g 1,g 2} : Set (t6 q))
   apply dEm hheight (a :=g 1) (b:=g 2) (c:=g 0) ?_
    (d4K q hh) hy
   change (span ({g 1,g 2,g 0} : Set (t6 q))).radical= _
   rw [Yi (g 2) (g 0),Set.insert_comm (g 1) (g 0)]
   exact hg
end bzL
end
section
namespace bRu
open E7 aFU IsDedekindDomain WithZero
open scoped WithZero
noncomputable section
variable {k L:Type} [zc k] [zc L] [yU k L] {x :L}
local notation "A" => DT k L x
local notation "B" => DR k L x
local notation "p" => origin k L x
private abbrev parameter :A:=⟨x,Algebra.self_mem_adjoin_singleton k x⟩
private theorem bQb (v :Valuation L ℤᵐ⁰) (hx :x≠0) :
  KB v x≠0↔v x<1 := by
 have h:=log_lt_iff_lt_exp (a :=(0:ℤ)) (v.ne_zero_iff.mpr hx)
 rw [exp_zero] at h
 unfold KB
 exact (show (-log (v x)).toNat≠0↔log (v x)<0 by omega).trans h
private theorem cu7 {v w:Valuation L ℤᵐ⁰}
    (hv :vh v) (hw:vh w) (h:v.IsEquiv w) :
    v=w:= by
  have hsmall {z :ℤᵐ⁰} (hz :z<1) :z≤exp (-1 :ℤ) := by
    apply (lt_mul_exp_iff_le (y :=exp (-1 :ℤ)) exp_ne_zero).mp
    simpa only [← exp_add,neg_add_cancel,exp_zero] using hz
  obtain ⟨π,hπ⟩:=hv (exp (-1 :ℤ))
  obtain ⟨τ,hτ⟩:=hw (exp (-1 :ℤ))
  have hπw:w π=exp (-1 :ℤ) := by
    apply wA
    · apply hsmall
      apply h.lt_one_iff_lt_one.mp
      simp [hπ]
    · rw [← hτ,← h.le_iff_le,hπ]
      apply hsmall
      apply h.lt_one_iff_lt_one.mpr
      simp [hτ]
  ext a
  by_cases ha :a=0
  · simp [ha]
  · have hpow (u:Valuation L ℤᵐ⁰) (hu:u π=exp (-1 :ℤ)) :
        u (π^(-log (v a)))=v a := by
      rw [map_zpow₀,hu,← exp_zsmul]
      have hs : (-log (v a))•(-1 :ℤ)=log (v a) := by simp
      rw [hs,exp_log (v.ne_zero_iff.mpr ha)]
    exact (hpow w hπw).symm.trans (h.eq_iff.mp (hpow v hπ))
private theorem dRX :
  p9 (CurvePlace.value (k :=k) (L:=L)) := by
 rintro ⟨v,hv,hc⟩ ⟨w,hw,hd⟩ h
 change v=w at h
 subst w
 rfl
private theorem bW3 (v :ax5 k L x) (hx :x≠0) (a :A) :
   v.val.value (cy A L a)≤1 := by
 let w:=v.val.value
 obtain ⟨a,ha⟩:=a
 change w a≤1
 induction ha using Algebra.adjoin_induction with
 | mem y hy =>
   have hy' : y=x :=Set.mem_singleton_iff.mp hy
   subst y
   exact ((bQb w hx).mp v.property).le
 | algebraMap c =>
   by_cases hc:c=0
   · simp [hc]
   · exact (v.val.on_constants c hc).le
 | add a b ha hb hwa hwb =>
   exact (w.map_add _ _).trans (max_le hwa hwb)
 | mul a b ha hb hwa hwb =>
   rw [oz]
   exact mul_le_one' hwa hwb
private theorem a6a (v :ax5 k L x) (hx :x≠0) (b:B) :
  v.val.value (cy B L b)≤1 := by
 let w:=v.val.value
 let f :A →+* w.valuationSubring :=
  (cy A L).codRestrict w.valuationSubring.toSubring (bW3 v hx)
 let:yU A w.valuationSubring :=f.toAlgebra
 let:IsScalarTower A w.valuationSubring L :=
  zsL (fun _=>rfl)
 have hvalInt:w.Integers w.valuationSubring :=Valuation.integer.integers w
 have hb:IsIntegral w.valuationSubring (b.val :L) :=IsIntegral.tower_top b.property
 exact hvalInt.isIntegral_iff_v_le_one.mp hb
private def RG (v :ax5 k L x) (hx :x≠0) :
   B →+* v.val.value.valuationSubring :=
 (cy B L).codRestrict v.val.value.valuationSubring.toSubring
   (a6a v hx)
private def bcf (v :ax5 k L x) (hx :x≠0) :aU B :=
 (oD v.val.value.valuationSubring).comap (RG v hx)
private theorem bsy (v :ax5 k L x) (hx :x≠0) (b:B) :
  b∈bcf v hx↔v.val.value (cy B L b)<1 :=
 v.val.value.mem_maximalIdeal_iff (a :=RG v hx b)
private def center (v :ax5 k L x) (hx :GF k x) :
  Ideal.primesOver p B:= by
 let P:=bcf v hx.ne_zero
 letI:P.IsPrime :=(z9 :
  (oD v.val.value.valuationSubring).IsPrime).comap (RG v hx.ne_zero)
 refine ⟨P,z9,⟨(a6k hx).eq_of_le (Ideal.IsPrime.ne_top z9) ?_⟩⟩
 change lJ {parameter (x :=x) (k :=k)} ≤ P.under A
 apply (G3 _).mpr
 change cy A B (parameter (x :=x) (k :=k))∈P
 apply (bsy v hx.ne_zero _).mpr
 exact (bQb v.val.value hx.ne_zero).mp v.property
variable [IsDedekindDomain (DR k L x)] [IsFractionRing (DR k L x) L]
private def aDm (hx :GF k x) (P:TZ p B) :
  HeightOneSpectrum B:= by
 refine ⟨P.val,P.property.1,?_⟩
 intro h
 have hmem:cy A B (parameter (x :=x) (k :=k))∈P.val :=
  (P.val.mem_of_liesOver p _).mp (vH _)
 rw [h,Ideal.mem_bot] at hmem
 exact hx.ne_zero (lz C4 hmem)
private def bKu (hx :GF k x) (P:TZ p B) :
    ax5 k L x := by
  let w:=aDm hx P
  have hconst: (w.valuation L).IsTrivialOn k :=
    Valuation.IsTrivialOn.of_le_one (w.valuation L)
      (fun c=> by
        rw [IsScalarTower.algebraMap_apply k B L c]
        exact w.valuation_le_one (cy k B c))
  refine ⟨⟨w.valuation L,w.valuation_surjective L,hconst.eq_one⟩,
    (bQb (w.valuation L) hx.ne_zero).mpr ?_⟩
  change w.valuation L (cy B L (cy A B (parameter (x :=x) (k :=k))))<1
  exact (w.valuation_lt_one_iff_mem _).mpr
    ((P.val.mem_of_liesOver p _).mp (vH _))
private theorem eLx (hx :GF k x) :
  p9 (bKu hx) := by
 intro P Q h
 have hval : (aDm hx P).valuation L=(aDm hx Q).valuation L :=
  lz (fun v :ax5 k L x=>v.val.value) h
 exact pL (lz HeightOneSpectrum.asIdeal
  (HeightOneSpectrum.valuation_injective L hval))
private theorem eLz (hx :GF k x) :
    vh (bKu hx) := by
  intro z
  let v :=z.val.value
  let w:=aDm hx (center z hx)
  have hbelow:w.valuationSubringAtPrime L≤v.valuationSubring := by
    intro y hy
    rw [w.valuationSubringAtPrime_eq_valuationSubring] at hy
    obtain ⟨a,s,hs⟩:=w.exists_primeCompl_mul_eq_of_integer y hy
    have hsV:v (cy B L s)=1 :=
      wA (a6a z hx.ne_zero s)
        (le_of_not_gt fun h=>s.property ((bsy z hx.ne_zero s).mpr h))
    change v y≤1
    have hval :=lz (fun b:L=>v b) hs
    rw [oz ,hsV,Qw] at hval
    exact hval.trans_le (a6a z hx.ne_zero a)
  have hproper :v.valuationSubring ≠ ⊤ := by
    rw [ne_eq,Valuation.valuationSubring_eq_top_iff,not_not]
    exact (Valuation.isNontrivial_iff_exists_lt_one v).mpr
      ⟨x,hx.ne_zero,(bQb v hx.ne_zero).mp z.property⟩
  have hring :=(w.valuationSubringAtPrime_eq_valuationSubring (K:=L)).symm.trans
    (ValuationSubring.eq_of_le_of_ne_top _ hbelow hproper)
  have heq :=(Valuation.isEquiv_iff_valuationSubring (w.valuation L) v).mpr hring
  refine ⟨center z hx,pL (dRX ?_)⟩
  exact cu7 (w.valuation_surjective L) z.val.normalized heq
private theorem eLy (hx :GF k x) (P:TZ p B) :
  KB (bKu hx P).val.value x=P.val.ramificationIdx A:= by
 let w:=aDm hx P
 let b:B:=cy A B (parameter (x :=x) (k :=k))
 have hb:b≠0:= by
  intro h
  exact hx.ne_zero (lz C4 h)
 have hspan:Ideal.map (cy A B) p=lJ {b} := by
  simp only [origin,y5 ,Cy ,b,parameter]
 have hmap :Ideal.map (cy A B) p ≠ ⊥ := by
  rw [hspan,ne_eq,Ideal.span_singleton_eq_bot]
  exact hb
 rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P.val hmap,hspan]
 change (-log (w.valuation L (cy B L b))).toNat =
  multiplicity w.asIdeal (lJ {b})
 simp only [w.valuation_of_algebraMap,w.intValuation_eq_exp_neg_multiplicity hb,
  log_exp,neg_neg,Int.toNat_natCast]
theorem proof :aFU.c2 := by
 intro k L _ _ _ x hx _ _
 let e :=Equiv.ofBijective (bKu hx)
  ⟨eLx hx,eLz hx⟩
 refine ⟨e.symm,fun v => ?_⟩
 have h:=eLy hx (e.symm v)
 change KB (e (e.symm v)).val.value x= _ at h
 simpa only [Equiv.apply_symm_apply] using h
end
end bRu
end
section
namespace aw8
open jA NR Finset
open scoped BigOperators
set_option maxHeartbeats 1500000
private def ajS (B c a d e :ℕ) :ℕ :=
 ama B fun q k l=>c+a*(l+2*k)+d*(B - q)+e*(B - q)^2
private def raw (b:Bank) :ℕ:=ajS b.box.b (aEw b) 1 131071 0
private def extra (B:ℕ) :ℕ:=ajS B 0 0 2300 1
private def iL (B:ℕ) :ℕ:=ama B fun q _ _=>2300+(B - q)
private theorem cT3 (B:ℕ) (f :ℕ→ℕ) :
  ama B (fun q _ _=>f q) =
   ∑ q∈p7 (B+1),ay8 ⟨B,2300,1150⟩ q*f q:= by
 simp only [ama,ay8,Nat.reduceDiv,min_self,sum_mul,Mw ,
  card_range,UZ]
private abbrev Triple :=Σ _:ℕ,Σ _:ℕ,ℕ
private def bmz (B:ℕ) :nI Triple :=
 (p7 (B+1)).sigma fun q=>(p7 (min q 1150+1)).sigma fun k =>
   p7 (min (q - k) (2300 - 2*k)+1)
private def bmy (B:ℕ) :nI Triple :=
 (p7 1151).sigma fun k=>(p7 (2300 - 2*k+1)).sigma fun l =>
   p7 (B-(k+l)+1)
set_option linter.constructorNameAsVariable false in
private theorem ep0 {M:Type*} [AddCommMonoid M] {B:ℕ} (hB:2300≤B)
    (f :ℕ→ℕ→ℕ→M) :
    ama B (fun q k l=>f k l (B - q)) =
      ∑ k∈p7 1151,∑ l∈p7 (2300 - 2*k+1),
        ∑ r∈p7 (B-(k+l)+1),f k l r := by
  calc
    _ = ∑ t∈bmz B,f t.2.1 t.2.2 (B - t.1) := by
      simp only [ama,bmz,sum_sigma]
    _ = ∑ t∈bmy B,f t.1 t.2.1 t.2.2 := by
      refine sum_nbij' (fun t:Triple=>⟨t.2.1,t.2.2,B - t.1⟩)
        (fun t:Triple=>⟨B - t.2.2,t.1,t.2.1⟩) ?_ ?_ ?_ ?_ (fun _ _=>rfl)
      · rintro ⟨q,k,l⟩ h
        simp only [bmz,bmy,mem_sigma,mem_range,Nat.lt_succ_iff,Xg] at *
        omega
      · rintro ⟨k,l,r⟩ h
        simp only [bmz,bmy,mem_sigma,mem_range,Nat.lt_succ_iff,Xg] at *
        omega
      · rintro ⟨q,k,l⟩ h
        simp only [bmz,mem_sigma,mem_range] at h
        rw [show B-(B - q)=q by omega]
      · rintro ⟨k,l,r⟩ h
        simp only [bmy,mem_sigma,mem_range] at h
        rw [show B-(B - r)=r by omega]
    _ = _:= by simp only [bmy,sum_sigma]
private def bcT (c d e f n:ℤ) :ℤ :=
 12*c*n+6*d*n*(n - 1)+2*e*n*(n - 1)*(2*n - 1) +
  3*f*n^2*(n - 1)^2
private theorem dfW (c d e f :ℤ) (n:ℕ) :
   12*(∑ i∈p7 n,(c+d*(i:ℤ)+e*i^2+f*i^3)) =
    bcT c d e f n:= by
 induction n with
 | zero=>simp [bcT]
 | succ n ih =>
   rw [sum_range_succ,mul_add,ih]
   push_cast
   unfold bcT
   ring
private def slice (B c a d e k :ℤ) :ℤ :=
 let N :=B - k+1
 let C:=c+2*a*k
 bcT
  (12*N*C+6*d*N*(N - 1)+2*e*N*(N - 1)*(2*N - 1))
  (12*N*a - 12*C+6*d*(1 - 2*N)+2*e*(-6*N^2+6*N - 1))
  (-12*a+6*d+2*e*(6*N-3))
  (-4*e)
  (2301 - 2*k)
private theorem awG {B k :ℕ} (hB:2300≤B) (hk :k<1151) (c a d e :ℤ) :
   144*(∑ l∈p7 (2300 - 2*k+1),∑ r∈p7 (B-(k+l)+1),
     (c+a*((l:ℤ)+2*k)+d*(r :ℤ)+e*(r :ℤ)^2)) =
     slice B c a d e k := by
 let N :ℤ:=(B:ℤ) - k+1
 let C:ℤ:=c+2*a*k
 have hn: ((2300 - 2*k+1 :ℕ) :ℤ)=2301 - 2*(k :ℤ) := by omega
 unfold slice
 rw [← hn,← dfW]
 rw [show (144 :ℤ)=12*12 by decide,uh,ze]
 congr 1
 apply qx rfl
 intro l hl
 have hl' := mem_range.mp hl
 have hlen: ((B-(k+l)+1 :ℕ) :ℤ)=N-l:= by dsimp [N]; omega
 have hi:=dfW (c+a*((l:ℤ)+2*k)) d e 0 (B-(k+l)+1)
 simp only [zero_mul,G6] at hi
 rw [hi,hlen]
 dsimp [N,C,bcT]
 ring
private def auf (f :ℤ→ℤ) (n:ℤ) :ℤ :=
  n*(120*f 0+(n - 1)*(60*(f 1 - f 0) +
    (n - 2)*(20*(f 2 - 2*f 1+f 0) +
      (n-3)*(5*(f 3-3*f 2 + 3*f 1 - f 0) +
        (n-4)*(f 4-4*f 3+6*f 2 - 4*f 1+f 0)))))
private theorem aE9 (B c a d e :ℤ) (n:ℕ) :
    120*(∑ k∈p7 n,slice B c a d e k) =
      auf (slice B c a d e) n:= by
  have hstep (x :ℤ) :
      auf (slice B c a d e) (x+1) =
        auf (slice B c a d e) x+120*slice B c a d e x := by
    unfold auf slice bcT
    ring
  induction n with
  | zero=>simp [auf]
  | succ n ih=>rw [Nat.cast_succ,hstep,sum_range_succ,mul_add,ih]
private theorem m8 (B c a d e :ℕ) (hB:2300≤B) :
   17280*(ajS B c a d e :ℤ) =
     auf (slice B c a d e) 1151 := by
 have hs :144*(ajS B c a d e :ℤ) = ∑ k∈p7 1151,slice B c a d e k := by
   unfold ajS
   rw [ep0 hB (fun k l r=>c+a*(l+2*k)+d*r+e*r^2)]
   simp only [SU,Nat.cast_add,RD,Nat.cast_pow,Nat.cast_ofNat]
   rw [ze]
   exact qx rfl fun k hk=>awG hB (mem_range.mp hk) _ _ _ _
 rw [show (17280:ℤ)=120*144 by decide,uh,hs,aE9]
 exact lz (auf (slice B c a d e))
   (show ((1151 :ℕ) :ℤ)=1151 from by decide)
private theorem a5Q (B c a d e value :ℕ) (hB:2300≤B)
  (cert:auf (slice B c a d e) 1151=17280*(value :ℤ)) :
  ajS B c a d e=value := by
 have h:=(m8 B c a d e hB).trans cert
 omega
set_option maxHeartbeats 300000 in
private theorem bVk :
  raw .first=2823319580182079460∧raw .second = 2845830394728456187 ∧
   extra 6789=129644787051371740∧extra 6820=131501361258434295:= by
 have h₁:=a5Q 6789 5737627 1 131071 0 2823319580182079460 (by decide) (by decide)
 have h₂:=a5Q 6820 4650787 1 131071 0 2845830394728456187 (by decide) (by decide)
 have h₃:=a5Q 6789 0 0 2300 1 129644787051371740 (by decide) (by decide)
 have h₄:=a5Q 6820 0 0 2300 1 131501361258434295 (by decide) (by decide)
 have r₁:aEw .first=5737627:= by decide
 have r₂:aEw .second=4650787:= by decide
 have e₁:raw .first=ajS 6789 5737627 1 131071 0 :=
  lz (fun base=>ajS 6789 base 1 131071 0) r₁
 have e₂:raw .second=ajS 6820 4650787 1 131071 0 :=
  lz (fun base=>ajS 6820 base 1 131071 0) r₂
 exact ⟨e₁.trans h₁,e₂.trans h₂,h₃,h₄⟩
end aw8
end
section
namespace bjB
noncomputable section
open agO
variable {S ι:Type} [qJ S] (P:ι→ aU S) [∀ i,(P i).IsPrime]
def Ek :Submonoid S := ⨅ i,(P i).primeCompl
theorem bsA {s :S} :
  s∈Ek P ↔ ∀ i,s∉P i :=
 Submonoid.mem_iInf
abbrev ajb:=Localization (Ek P)
def toChart (i:ι) :ajb P →+* Au (P i) :=
  QL (M:=Ek P)
    (g:=cy S (Au (P i)))
    (fun s=>z0j _ (⟨s,(bsA P).mp s.2 i⟩: (P i).primeCompl))
@[simp]
theorem ctr (i:ι) (s :S) :
  toChart P i (cy S (ajb P) s) =
   cy S (Au (P i)) s :=
 NZ _ s
def aQR (J:aU S) (i:ι) :ajb P →+* aF3 J (P i) :=
 (mD _).comp (toChart P i)
private theorem cKS (i:ι) :
  Mj (Ek P:Set S) (P i:Set S) :=
 Set.disjoint_left.mpr fun _ hs hp=>(bsA P).mp hs i hp
private theorem bii (i:ι) :
  ((P i).map (cy S (ajb P))).under S=P i :=
 ztT (Ek P) _
  (z9 : (P i).IsPrime) (cKS P i)
private theorem ddr [oK ι] {J:aU S}
   (hP : ∀ i,J.IsMinimalPrime (P i)) (i:ι) :
   ((P i).map (cy S (ajb P))).IsMaximal:= by
 classical
 let M:=Ek P
 let A:=ajb P
 let E :=(P i).map (cy S A)
 have hE :E.IsPrime :=
   PD M A (P i) (hP i).isPrime (cKS P i)
 apply Ideal.isMaximal_def.mpr
 refine ⟨hE.ne_top,Ideal.maximal_of_no_maximal ?_⟩
 intro N hEN hN
 have hd:=((IsLocalization.isPrime_iff_isPrime_disjoint M A N).mp hN.isPrime).2
 have hcover : (N.under S:Set S) ⊆ ⋃ j∈(Kv :nI ι),(P j:Set S) := by
   intro s hs
   have hnot:s∉M:= fun hm=>Set.disjoint_left.mp hd hm hs
   have hex : ∃ j,s∈P j:= by
     by_contra! hnone
     exact hnot ((bsA P).mpr hnone)
   obtain ⟨j,hj⟩:=hex
   exact Set.mem_iUnion₂.mpr ⟨j,vk j,hj⟩
 obtain ⟨j,_,hNj⟩ :=
   (Ideal.subset_union_prime (s :=Kv) i i
     (f :=P) (fun k _ _ _=>(hP k).isPrime)).mp hcover
 have hiN :P i≤N.under S :=
   (bii P i).symm.trans_le (Vl hEN.le)
 have hji:P j≤P i:=(hP j).2 (hP i).1 (hiN.trans hNj)
 exact hEN.not_ge ((IsLocalization.under_le_under_iff M A).mp
   ((hNj.trans hji).trans_eq (bii P i).symm))
private theorem c6x {J:aU S} (i:ι) (h:J.IsMinimalPrime (P i)) :
   (sH (aQR P J i)).radical=(P i).map (cy S (ajb P)) := by
 let T:=Au (P i)
 let A:=ajb P
 have hk :sH (aQR P J i) =
     (J.map (cy S T)).comap (toChart P i) := by
   unfold aQR
   rw [← S2 ,Pr]
 rw [hk,← Ideal.comap_radical,IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
   T (P i) J h,zNE]
 apply (zRW (Ek P) A).injective
 change ((oD T).comap (toChart P i)).under S =
   ((P i).map (cy S (ajb P))).under S
 rw [bii P i]
 apply Ideal.ext
 intro s
 change toChart P i (cy S (ajb P) s)∈oD T↔s∈P i
 rw [ctr]
 exact zRt T (P i) s
private theorem gBV [oK ι] {J:aU S}
    (hP : ∀ i,J.IsMinimalPrime (P i)) (i:ι) :
    vh (aQR P J i) := by
  let A:=ajb P
  let T:=Au (P i)
  let E :=(P i).map (cy S A)
  let g:=aQR P J i
  have hE :E.IsMaximal:=ddr P hP i
  have hg: (sH g).radical=E :=c6x P i (hP i)
  intro z
  obtain ⟨y,rfl⟩:=Et z
  obtain ⟨a,s,rfl⟩:=zcf (P i).primeCompl (S:=T) y
  let d:A:=cy S A s
  have hd:d∉E := by
    change (s :S)∉E.under S
    rw [bii P i]
    exact s.2
  have hc:xI (sH g) (lJ {d}) := by
    apply zQx
    intro N hKN hDN hN
    have hEN :E≤N :=hg ▸ hN.radical_le_iff.mpr hKN
    exact hd (hE.eq_of_le hN.ne_top hEN ▸ hDN (vH d))
  obtain ⟨r,hr,u,hu,hsum⟩:=hc.exists
  obtain ⟨v,rfl⟩:=Ideal.mem_span_singleton'.mp hu
  have hv :g v*g d = 1 := by
    simpa only [oY ,oz ,RingHom.mem_ker.mp hr,Gj,map_one]
      using lz g hsum
  have hfrac:mD _ (zzm T a s)*g d =
      g (cy S A a) := by
    change mD _ (zzm T a s) *
        mD _ (toChart P i (cy S (ajb P) (s :S))) =
      mD _ (toChart P i (cy S (ajb P) a))
    simpa only [ctr,oz]
      using lz (mD (J.map (cy S T))) (zOg T a s)
  refine ⟨cy S A a*v,?_⟩
  rw [oz ,← hfrac,uh,Iw (g d) (g v),hv,Qw]
theorem gnQ [oK ι] {J:aU S} (hP : ∀ i,J.IsMinimalPrime (P i))
   (hinj:p9 P) :
   vh (fun a :ajb P=> fun i=>aQR P J i a) := by
 let K:= fun i=>sH (aQR P J i)
 let E := fun i=>(P i).map (cy S (ajb P))
 have hk (i:ι) : (K i).radical=E i:=c6x P i (hP i)
 have hm (i:ι) : (E i).IsMaximal:=ddr P hP i
 have hc:Pairwise (fun i j=>xI (K i) (K j)) := by
   intro i j hij
   apply zQx
   intro N hKi hKj hN
   have hi:E i≤N :=hk i ▸ hN.radical_le_iff.mpr hKi
   have hj:E j≤N :=hk j ▸ hN.radical_le_iff.mpr hKj
   have he :E i=E j :=
     (hm i).eq_of_le hN.ne_top hi |>.trans ((hm j).eq_of_le hN.ne_top hj).symm
   apply hij (hinj ?_)
   exact (bii P i).symm.trans
     ((lz (fun I:aU (ajb P)=>I.under S) he).trans (bii P j))
 intro z
 choose a ha using fun i=>gBV P hP i (z i)
 obtain ⟨r,hr⟩:=Ideal.pi_quotient_surjective hc (fun i=>mD (K i) (a i))
 refine ⟨r,funext fun i => ?_⟩
 let lift:=Ideal.Quotient.lift (K i) (aQR P J i) (fun _ h=>RingHom.mem_ker.mp h)
 exact (lz lift (hr i)).trans (ha i)
end
end bjB
end
section
namespace bjB
noncomputable section
open agO
theorem proof :agO.c4 := by
  classical
  intro R S F _ _ _ _ _ _ _ f e he hcomp w q _
  let L:=Au q
  let x :L:=cy R L w
  let J:aU S:=lJ {f w}
  let ι := ↥(auX f J q)
  let P:ι→ aU S:=C4
  let _ : ∀ i:ι,(P i).IsPrime :=aUP
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · let _:=hempty
    refine ⟨⊥,?_⟩
    change (∑ i:ι,bmw f J q i)≤_
    simp
  obtain ⟨i₀⟩:=hnonempty
  have hP (i:ι) :J.IsMinimalPrime (P i) :=
    Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp i.property).1
  let A:=ajb P
  have hden:q.primeCompl≤(Ek P).comap f.toMonoidHom:= by
    intro r hr
    apply (bsA P).mpr
    intro i hi
    apply hr
    change r∈q
    rw [aDc i]
    exact hi
  let g:L →+* A:=IsLocalization.map A f hden
  let _:yU L A:=g.toAlgebra
  have hg r :g (cy R L r)=cy S A (f r) :=
    IsLocalization.map_eq _ _
  let lF:L →ₐ[R] F :=
    Localization.mapToFractionRing F q.primeCompl L q.primeCompl_le_nonZeroDivisors
  let _:yU L F:=lF.toRingHom.toAlgebra
  let _:IsScalarTower R L F:=zsL fun r=>(lF.commutes r).symm
  let _:IsFractionRing L F :=
    IsFractionRing.isFractionRing_of_isLocalization q.primeCompl L F
      q.primeCompl_le_nonZeroDivisors
  have hu (s :Ek P) :vl (e s) := by
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hs : (s :S)=0:=he (hzero.trans e.map_zero.symm)
    exact (bsA P).mp s.2 i₀ (hs.symm ▸ (P i₀).zero_mem)
  let k :A →+* F:= QL hu
  have hk s :k (cy S A s)=e s :=NZ hu s
  have hkinj:p9 k := by
    apply (IsLocalization.lift_injective_iff hu).mpr
    intro s t
    exact ⟨fun hst=>(hk s).symm.trans ((lz k hst).trans (hk t)),
      fun hst=>lz _ (he hst)⟩
  let aF:A →ₐ[L] F := {
    __:=k
    commutes' := by
      have hc:k.comp (cy L A)=cy L F:= by
        apply zuW q.primeCompl
        apply xW
        intro r
        change k (g (cy R L r))=lF (cy R L r)
        rw [hg,hk,lF.commutes]
        exact t4 hcomp r
      exact t4 hc }
  let _:yU L (t5 L) :=OreLocalization.instAlgebra
  let equiv :=(FractionRing.algEquiv L F).symm
  let j:=equiv.toAlgHom.comp aF
  let B:bQZ L:=j.range
  let bEquiv :A ≃ₐ[L] B:=AlgEquiv.ofInjective j (equiv.injective.comp hkinj)
  let T (i:ι) :=Au (P i)
  let t (i:ι) :L →+* T i:=Localization.localRingHom q (P i) f (aDc i)
  let _ : ∀ i:ι,yU L (T i) := fun i=>(t i).toAlgebra
  let π (i:ι) :A →ₐ[L] aF3 J (P i) := {
    __:=aQR P J i
    commutes' := by
      have hchart: (toChart P i).comp g=t i:= by
        apply zuW q.primeCompl
        apply xW
        intro r
        change toChart P i (g (cy R L r))=t i (cy R L r)
        rw [hg,ctr]
        exact (zMs q (P i) f (aDc i) r).symm
      intro y
      exact lz (mD _) (t4 hchart y) }
  let φ:B →ₐ[L] (∀ i:ι,aF3 J (P i)) :=
    (AlgHom.pi π).comp bEquiv.symm.toAlgHom
  have hφ:vh φ :=
    (gnQ P hP Subtype.val_injective).comp bEquiv.symm.surjective
  have hx :φ (cy L B x)=0:= by
    rw [φ.commutes]
    funext i
    change mD (J.map (cy S (T i))) (t i x)=0
    have hw:t i x=cy S (T i) (f w) :=
      zMs q (P i) f (aDc i) w
    rw [hw,G7]
    exact zh _ (vH _)
  have hker :lJ {cy L B x} ≤ sH φ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (RingHom.mem_ker.mpr hx))
  let ψ:aLX x B →ₐ[L] (∀ i:ι,aF3 J (P i)) :=
    zTA _ φ (fun _ h=>RingHom.mem_ker.mp (hker h))
  have hψ:vh ψ:= by
    intro z
    obtain ⟨b,hb⟩:=hφ z
    exact ⟨mD _ b,hb⟩
  refine ⟨B,?_⟩
  change (∑ i:ι,qm L (aF3 J (P i))) ≤
    qm L (aLX x B)
  rw [← Module.length_pi_of_fintype L]
  exact VS ψ.toLinearMap hψ
end
end bjB
end
section
namespace axa
noncomputable section
open Polynomial K1 aR jA
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
private def Bound (d:ℕ) (F:Lq) :Prop := ∀ m,(F.coeff m).natDegree≤d
private theorem bb6 {p:kS[X]} {d:ℕ} (hp:p.natDegree≤d) :
   Bound d (nq p) := by
 classical
 intro m
 rw [MvPolynomial.coeff_C]
 split
 · exact hp
 · simp
private theorem bBM {d e :ℕ} {F G:Lq} (hF:Bound d F) (hG:Bound e G) :
  Bound (d+e) (F*G) := by
 classical
 intro m
 rw [MvPolynomial.coeff_mul]
 apply UP
 intro p _
 exact natDegree_mul_le.trans (zk (hF p.1) (hG p.2))
private theorem cDk {ι:Type*} (S:nI ι) (F:ι→Lq) {d:ℕ}
  (hF : ∀ i∈S,Bound d (F i)) :Bound d (∑ i∈S,F i) := by
 intro m
 rw [MvPolynomial.coeff_sum]
 apply UP
 exact fun i hi=>hF i hi m
private theorem dzJ {d:ℕ} {F:Lq} (hF:Bound d F) (n:ℕ) :
   Bound (n*d) (F^n) := by
 induction n with
 | zero=>simpa only [pow_zero,Nat.zero_mul,← MvPolynomial.C_1] using
    (bb6 (p:=(1 :kS[X])) (by simp) :Bound 0 _)
 | succ n ih=>simpa only [pow_succ,Nat.succ_mul] using bBM ih hF
private theorem dzK {ι:Type*} (S:nI ι) (d:ι→ℕ) (F:ι→Lq)
   (hF : ∀ i∈S,Bound (d i) (F i)) :Bound (∑ i∈S,d i) (∏ i∈S,F i) := by
 classical
 induction S using Kl with
 | empty =>
   simpa only [Finset.sum_empty,Finset.prod_empty,← MvPolynomial.C_1] using
     (bb6 (p:=(1 :kS[X])) (by simp) :Bound 0 _)
 | insert i S hi ih =>
   rw [Mk hi,zqX hi]
   exact bBM (hF i (Kc ..))
     (ih fun j hj=>hF j (IU hj))
private theorem dzF (j:Fin 3) :Bound 0 (lV j) := by
 classical
 intro m
 rw [MvPolynomial.coeff_X]
 split <;> simp
private theorem cXJ (p:ao[X]) : (vG p).natDegree=p.natDegree :=
 Z0 (FaithfulSMul.algebraMap_injective ao kS) p
private theorem cfm {Γ s} (P:jF Γ s) (L:kH P)
    {T:ℕ} {F:jK} (hF:ahb P.H.natDegree T F) :
    Bound T (restore P L F) := by
  classical
  let h:=P.H.natDegree
  have hres : (ahH L.numerator L.denominator).natDegree≤h :=
    ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (Nat.le_of_lt L.small)))
  let v :mA→ℕ:= fun i=>i.elim 0 (fun _=>h)
  let g:mA→Lq:= fun i=>i.elim
    (nq (lI (cy ao[X] kS oj)))
    (ar9 P L)
  have hg (i:mA) :Bound (v i) (g i) := by
    cases i with
    | none=>exact bb6 (by simp)
    | some i =>
      change Bound h (ar9 P L i)
      unfold ar9
      have hs :Bound h (∑ j:Fin 3,if j.val≤ i.val then
          nq (pQ (i.val - j.val) (vG P.H)) *
            lV j else 0) := by
        apply cDk
        intro j _
        split
        · simpa only [Nat.add_zero] using bBM
            (bb6 ((natDegree_hasseDeriv_le _ _).trans (by rw [cXJ]; omega)))
            (dzF j)
        · intro m
          simp
      intro m
      change ((nq _+_:Lq).coeff m).natDegree≤h
      simp only [AddMonoidAlgebra.coeff_add,Dv]
      exact natDegree_add_le _ _ |>.trans (max_le
        (bb6 ((natDegree_hasseDeriv_le _ _).trans ((Nat.sub_le _ _).trans hres)) m) (hs m))
  change Bound T (z8 _ g F)
  rw [zMm]
  apply cDk
  intro a ha m
  have hp:=dzK a.support (fun i=>a i*v i) (fun i=>g i^a i)
    (fun i _=>dzJ (hg i) (a i))
  have hdeg:=bBM (bb6 (p:=(F.coeff a).map (cy ao kS))
    (d:=(F.coeff a).natDegree) RC) hp m
  apply hdeg.trans
  refine (R9 ?_ _).trans (hF a ha)
  change _≤weight h a
  unfold weight Finsupp.sum
  apply uW
  intro i _
  cases i with
  | none=>simp [v]
  | some i =>
    change a (some i)*h≤(131071+h - i.val)*a (some i)
    rw [Nat.mul_comm (a (some i))]
    exact Nat.mul_le_mul_right _ (by omega)
private abbrev bAD:=t5 (kS[X])
private abbrev A:=nX (Fin 3) bAD
private abbrev beI:kS[X] →+* bAD:=cy _ _
private def blQ:jK →+* A :=
 (t3 beI).comp
   ((t3 ((u8 (cy ao[X] kS)).comp
     (zd (R:=ao)).toRingHom)).comp
     (G4 ao[X] (Fin 3)).toRingHom)
private theorem dyS:p9 blQ:= by
 have hcoeff :p9 ((u8 (cy ao[X] kS)).comp
    (zd (R:=ao)).toRingHom) :=
  (Polynomial.map_injective _ (xL ao[X] kS)).comp
    Bivariate.swap.injective
 exact (zNV _ (xL kS[X] bAD)).comp
  ((zNV _ hcoeff).comp
    (G4 ao[X] (Fin 3)).injective)
private theorem fXd {Γ s} (P:jF Γ s) (L:kH P) :
    p9 (bgL P L) := by
  let c (p:kS[X]) :A:=nq (beI p)
  let cInv :A:=nq ((beI (vG P.H))⁻¹)
  let H (i:ℕ) :=c (pQ i (vG P.H))
  let R (i:ℕ) :=c (pQ i (ahH L.numerator L.denominator))
  let u₀:=cInv*(lV 0 - R 0)
  let u₁:=cInv*(lV 1 - R 1 - H 1*u₀)
  let u₂:=cInv*(lV 2 - R 2 - H 2*u₀ - H 1*u₁)
  let u:Fin 3→A := ![u₀,u₁,u₂]
  let back :Lq →+* A:=yB (MvPolynomial.C.comp beI) u
  have hH :beI (vG P.H)≠0:= by
    simpa only [beI,vG,p6] using
      (xL kS[X] bAD).ne
        ((P.monic.map (cy ao kS)).ne_zero)
  have hc:H 0*cInv=1 := by
    simp [H,c,cInv,← oz ,hH]
  have hcancel (y :A) :H 0*(cInv*y)=y := by rw [← uh,hc,xm]
  have hc_back (p:kS[X]) :back (nq p)=c p:= by
    simp [back,c]
  have hu (i:Fin 3) :back (ar9 P L i)=lV i:= by
    have hterm (j:Fin 3) :back (if j.val≤ i.val then
        nq (pQ (i.val - j.val) (vG P.H))*lV j
        else 0)=if j.val≤ i.val then H (i.val - j.val)*u j else 0:= by
      split
      · rw [oz ,hc_back]
        simp [back,H]
      · simp
    simp only [ar9,oY ,u5 ,hterm,hc_back]
    change R i.val+(∑ j:Fin 3,if j.val≤ i.val then H (i.val - j.val)*u j else 0)= _
    fin_cases i <;> norm_num [Fin.sum_univ_three,u,u₀,u₁,u₂,hcancel]
  have hopt (F:jK) :
      (G4 ao[X] (Fin 3)).toRingHom F =
        G4 ao[X] (Fin 3) F:=rfl
  have hswap (p:ao[X][X]) :
      (zd (R:=ao)).toRingHom p=zd p:=rfl
  have hcomp:back.comp (bgL P L)=blQ:= by
    apply Ea
    · intro p
      simp only [blQ,pU,hopt,hswap,MvPolynomial.optionEquivRight_C,
        KI,Polynomial.Bivariate.swap_C,yo ,
        sI,bgL,NW,hc_back]
      rfl
    · rintro (_ | i)
      · simp [blQ,bgL,hc_back,c,Bivariate.swap_Y]
      · simp only [pU,bgL,Lf ,Option.elim_some,hu,
          blQ,hopt,MvPolynomial.optionEquivRight_X_some,G9]
  intro F G h
  apply dyS
  rw [← hcomp]
  exact lz back h
set_option maxRecDepth 4096 in
private theorem Ly (Γ:nI K) (s :K→K[X]) (P:jF Γ s) (L:kH P)
   (F:jK) (hcut : ∀ m∈F.support,(F.coeff m).natDegree+weight P.H.natDegree m <
     arX*P.H.natDegree)
   (hpole : (nq (vG P.H))^arX∣restore P L F) :F=0:= by
 apply fXd P L
 rw [p6,fXc]
 have hd:=cfm P L (T:=arX*P.H.natDegree - 1)
   (F:=F) (fun m hm=>Nat.le_sub_one_of_lt (hcut m hm))
 rw [← vw] at hpole
 obtain ⟨Q,hQ⟩:=hpole
 apply MvPolynomial.ext
 intro m
 change (restore P L F).coeff m=0
 by_contra hn
 have hcoeff :vG P.H^arX∣(restore P L F).coeff m:= by
   rw [hQ,MvPolynomial.coeff_C_mul]
   exact dvd_mul_right _ _
 have hle :=natDegree_le_of_dvd hcoeff hn
 have hmon : (vG P.H).Monic:=P.monic.map (cy ao kS)
 rw [hmon.natDegree_pow,cXJ] at hle
 have hpos :0<arX*P.H.natDegree :=
   WY (by decide) P.small.1
 exact (Nat.not_le_of_lt (Nat.sub_lt hpos Nat.zero_lt_one)) (hle.trans (hd m))
end
end axa
end
section
namespace vq
noncomputable section
open K1 cu MN MvPolynomial
open scoped Polynomial BigOperators
local notation "Y" => MvPolynomial.X (R:=FX) (none :Option (Fin 2))
private abbrev incl:=cy L[X] FX
private abbrev center :FX:=incl oj
end
end vq
end
section
namespace dnc
noncomputable section
open aR oR we Polynomial
open RingTheory.Sequence
open scoped Pointwise
private theorem aOO {R:Type*} [qJ R] (f x :R) :
  x∈f•(⊤ : u9 R R)↔f∣x := by
 simp only [zeT,z8t,true_and,LO]
 exact exists_congr fun _=>eq_comm
attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem cTL {f g:af 3} (hf :Sv f) (hg : ¬ f∣g) :
   ∀ x :eT 3,fW f∣fW g*x→fW f∣x := by
 have hfPrime :Prime f :=UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
 have hreg:P7 (af 3) [f,g] := by
   rw [isWeaklyRegular_cons_iff,isWeaklyRegular_singleton_iff]
   refine ⟨mul_right_injective₀ hf.ne_zero,?_⟩
   apply (TH _ _).mpr
   intro x hx
   exact (aOO f x).mpr
     ((hfPrime.dvd_mul.mp ((aOO f (g*x)).mp hx)).resolve_left hg)
 let _:yU ao[X] cH :=qY.toAlgebra
 let _:Module.IsTorsionFree ao[X] cH :=
   Module.isTorsionFree_iff_algebraMap_injective.mpr Yk
 have :Module.Flat (af 3) (eT 3) :=
   Module.Flat.of_linearEquiv
     (Algebra.IsPushout.equiv ao[X] (af 3) cH (eT 3)).symm.toLinearEquiv
 have hgeo:=hreg.of_flat (S:=eT 3)
 change P7 (eT 3) [fW f,fW g] at hgeo
 rw [isWeaklyRegular_cons_iff,isWeaklyRegular_singleton_iff] at hgeo
 intro x hx
 exact (aOO _ _).mp
   (Ww hgeo.2 ((aOO _ _).mpr hx))
end
end dnc
end
section
set_option maxRecDepth 1500
namespace bRq
noncomputable section
open Polynomial aR dN rW
open scoped BigOperators
private def Sp:jo[X] :=
 ∑ j:Fin bf,t9 j.val (lV j)
private def awO:af 4 →+* jo[X] :=
 yB (u8 nq)
  (fun i:Fin 4=>pQ i.val Sp)
private def Oe :jo[X] →+* mK :=
 GY (t3 ni) (nq rI)
private theorem bpK (i:ℕ) :
  Oe (pQ i Sp)=J1 rI i:= by
 classical
 simp only [Sp,u5 ,J1]
 refine qx rfl fun j _ => ?_
 rw [zKa]
 simp only [Oe,x7,zFK,
  oz ,Ts ,G9,vw]
 ac_rfl
private theorem a3L (R:af 4) :
    Oe (awO R)=mS (bC R) := by
  change (Oe.comp awO) R =
    (mS.comp (t3 j8)) R
  apply t4
  apply Ea
  · intro a
    simp only [pU,awO,NW,KI,
      mS]
    change Polynomial.eval₂ (t3 ni) (nq rI)
        (a.map nq)=nq (j8 a)
    have hm: (t3 ni).comp (nq:ao →+* jo) =
        (nq:c9 →+* mK).comp ni:= by
      ext b
      simp
    rw [zem,hm,← Y4]
    have hx :GY ni rI=j8:= by
      apply C5
      · intro b
        exact F9 _ _
      · exact zC9 _ _
    change nq ((GY ni rI) a)= _
    rw [hx]
  · intro i
    simpa only [pU,awO,Lf ,G9,
      mS] using bpK i.val
private def azQ {n:ℕ} (a :Fin n→ao) :ao[X] :=
 ∑ j:Fin n,t9 j.val (a j)
private theorem cb2 {n:ℕ} (a :Fin n→ao) (i:Fin n) :
   (azQ a).coeff i.val=a i:= by
 classical
 rw [azQ,zaW,Finset.sum_eq_single i]
 · exact coeff_monomial_same _ _
 · intro j _ hj
   exact coeff_monomial_of_ne _ (fun he=>hj (Fin.ext he.symm))
 · simp
private theorem eMg (a :Fin bf→ao) :
  (azQ a).natDegree<bf := by
 apply (UP _ _ (n:=bf - 1) ?_).trans_lt
  (by decide :bf - 1<bf)
 intro j _
 exact (natDegree_monomial_le _).trans (by have :=j.isLt; omega)
private theorem cZH (a :Fin bf→ao) (R:af 4) :
    (awO R).map (p5 a)=cK R (azQ a) := by
  have hU:Sp.map (p5 a)=azQ a := by
    simp [Sp,azQ,NY]
  change ((u8 (p5 a)).comp awO) R =
    p5 (jet (azQ a)) R
  apply t4
  apply Ea
  · intro b
    simp only [pU,awO,NW,
      FQ,yo ,sI]
    have h: (p5 a).comp (nq:ao →+* jo) =
        RingHom.id ao:=xW fun x=>FQ x
    rw [h,Xx]
  · intro i
    simp only [pU,awO,Lf ,Gr,
      yo ,← zvb,hU,jet]
private def a4m (a :Fin bf→ao) :mK →+* GeoField :=
 p5 (ni ∘ a)
private theorem cS9 (a :Fin bf→ao) :
  (a4m a).comp (t3 ni) =
    ni.comp (p5 a) := by
 apply Ea <;> intro b <;> simp [a4m]
private theorem ed5 (a :Fin bf→ao) :
   (a4m a).comp Oe =
     j8.comp (u8 (p5 a)) := by
 apply C5
 · intro b
   simp only [pU,Oe,x7,
     F9,yo ,sS]
   exact t4 (cS9 a) b
 · simp [Oe,a4m,rI]
private theorem d5A {A:kT} {a :Fin bf→ao}
  (ha :a∈VO ao A) :gN A≤ sH (a4m a) := by
 apply Ideal.map_le_iff_le_comap.mpr
 intro b hb
 change ((a4m a).comp (t3 ni)) b=0
 rw [cS9,pU]
 have h:p5 a b=0:=ha b hb
 rw [h,p6]
private theorem eMl {A:kT} {g:af 4}
  (hg:bC g∈lA A) {a :Fin bf→ao}
  (ha :a∈VO ao A) :cK g (azQ a)=0:= by
 change mS (bC g)∈gN A at hg
 rw [← a3L] at hg
 have hz : ((a4m a).comp Oe) (awO g)=0 :=
  d5A ha hg
 rw [ed5,pU,yo ,
  cZH] at hz
 have hinj:p9 j8 :=
  (cy lN c9).injective.comp (xL ao[X] lN)
 exact hinj (hz.trans (p6 _).symm)
private theorem eeb {A:kT} (hA:A.IsPrime) (T:jo[X])
  (hT : ∀ a∈VO ao A,T.map (p5 a)=0) :
  Oe T∈gN A:= by
 have hc (n:ℕ) :T.coeff n∈A:= by
  rw [← hA.radical,← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K:=ao)]
  intro a ha
  change p5 a (T.coeff n)=0
  rw [← zg ,hT a ha,coeff_zero]
 rw [lz Oe T.as_sum_range,u5]
 apply Ideal.sum_mem
 intro n _
 rw [Oe,x7,zFK]
 exact zx6 _ _ (zh _ (hc n))
private def exponent:ℕ:=2*bf
private def ayl (g:af 4) (j:Fin bf) :af 4 :=
 nq (lI (↑j.val.factorial:ao)⁻¹) *
  (wB g^(2*(bf - j.val))*su g j.val)
private theorem duy (g:af 4) (S:ao[X]) (hg:cK g S=0)
    (j:Fin bf) :
    cK (ayl g j) S=cK (wB g) S^exponent*pQ j.val S:= by
  have hOrd:derivative^[j.val] S=lI (j.val.factorial:ao)*pQ j.val S:= by
    have h:=congrFun (factorial_smul_hasseDeriv (R:=ao) (k :=j.val)) S
    change j.val.factorial•(pQ j.val S)=derivative^[j.val] S at h
    simpa only [nsmul_eq_mul,C_eq_natCast] using h.symm
  have hFact : (j.val.factorial:ao)≠0 :=
    lB.ahA (j.isLt.trans (by decide :bf<K1.p))
  have hinv :lI (↑j.val.factorial:ao)⁻¹ *
      lI (↑j.val.factorial:ao)=1 := by
    rw [← oz ,Du hFact,map_one]
  let E :=p5 (jet S:Fin 4→ao[X])
  change E (_ *(_^_ *_))= _
  rw [oz ,oz ,vw ,FQ]
  change _ *(cK (wB g) S^(2*(bf - j.val)) *
    cK (su g j.val) S)= _
  rw [arh _ _ hg,hOrd]
  calc
    _=(lI (↑j.val.factorial:ao)⁻¹*lI (↑j.val.factorial:ao)) *
        ((cK (wB g) S^(2*(bf - j.val)) *
          cK (wB g) S^(2*j.val))*pQ j.val S) := by ac_rfl
    _ = _:= by
      rw [hinv,xm,← pow_add,← Nat.mul_add,zxt j.isLt.le,exponent]
private def bPd {L:ℕ} (b:Fin L→af 4) (i:Fin L) :af 4 :=
 (wR (-MvPolynomial.C (oj:ao[X]))
   (∑ j:Fin L,t9 j.val (b j))).coeff i.val
private theorem duF {L:ℕ} (b:Fin L→af 4) {S:ao[X]}
   (hd:S.natDegree<L) (d:ao[X])
   (hb : ∀ j,cK (b j) S=d*pQ j.val S) (i:Fin L) :
   cK (bPd b i) S=lI (S.coeff i.val)*d:= by
 let E :=p5 (jet S:Fin 4→ao[X])
 let T:=wR (oj:ao[X]) (S.map (lI:ao →+* ao[X]))
 have hcoeff (n:ℕ) :T.coeff n=pQ n S:= by
   change (wR _ _).coeff n= _
   rw [taylor_coeff,zvb,eval_map,eval₂_C_X]
 have hT:T.natDegree<L:= by
   change (wR _ _).natDegree<_
   rw [natDegree_taylor]
   exact natDegree_map_le.trans_lt hd
 have hsum: (∑ j:Fin L,t9 j.val (pQ j.val S))=T:= by
   simp only [← hcoeff]
   rw [Ok (fun n:ℕ=>t9 n (T.coeff n))]
   exact (T.as_sum_range' _ hT).symm
 have hmap : (∑ j:Fin L,t9 j.val (b j)).map E =
     lI d*T:= by
   rw [← hsum,ze,NY]
   refine qx rfl fun j _ => ?_
   calc
     _=t9 j.val (cK (b j) S) :=SL E
     _=t9 j.val (d*pQ j.val S) :=lz (t9 j.val) (hb j)
     _ = _:=Polynomial.C_mul_monomial.symm
 change E (bPd b i)= _
 rw [bPd,← zg ,zla,map_neg,
   FQ,hmap,taylor_mul,taylor_C]
 dsimp only [T]
 rw [taylor_taylor,neg_add_cancel,
   taylor_zero,Polynomial.coeff_C_mul,zg ,Iw]
private theorem d3i (i:Fin bf) (D U:af 4) (n:ℕ) :
  Oe (lI (lV i)*awO D^n-awO U) =
   lV i*mS (bC D)^n - mS (bC U) := by
 have hx :Oe (lI (lV i))=lV i:= by
  rw [Oe,x7,F9,G9]
 simp only [Av,oz ,vw ,a3L,hx]
private theorem fU4 (g D U:af 4) (i:Fin bf) (n:ℕ)
   (hU : ∀ S:ao[X],S.natDegree<bf→cK g S=0 →
     cK U S=lI (S.coeff i.val)*cK D S^n)
   {A:kT} (hp:A.IsPrime) (hg:bC g∈lA A) :
   lV i*mS (bC D)^n - mS (bC U) ∈
     gN A:= by
 let T:jo[X] :=
   lI (lV i)*awO D^n-awO U
 have hEq:Oe T =
     lV i*mS (bC D)^n - mS (bC U) :=
   d3i i D U n
 rw [← hEq]
 apply eeb hp
 intro a ha
 change (u8 (p5 a)) T=0
 simp only [T,Av,oz ,vw ,yo ,sS ,
   Gr,cZH]
 rw [hU _ (eMg a) (eMl hg ha),cb2,sub_self]
theorem proof :bas.c2 := by
 intro g i
 let u:=bPd (ayl g) i
 refine ⟨bC u,exponent,fun A hp _ hg _ => ?_⟩
 apply fU4 g (wB g) u i exponent _ hp hg
 intro S hd hS
 exact duF (ayl g) hd _
  (duy g S hS) i
end
end bRq
end
section
namespace bav
open aR Dr aiK Kd lB
open ap8 (aES aQe)
open scoped BigOperators Pointwise
private theorem dEQ {p q:ox} (hp:bF p) (hq:bF q) :
    pz p+capExponents q=pz (p.plus q) := by
  ext e
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    simp only [OW,J4 ,Dv] at *
    omega
  · intro he
    obtain ⟨hpb,hpj⟩:=hp
    obtain ⟨hqb,hqj⟩:=hq
    rw [OW] at he
    simp only [J4] at he
    let z :=min (e 3) (2*p.t)
    let z' := e 3 - z
    have hz :z+z' = e 3∧z≤2*p.t∧z' ≤ 2*q.t:= by dsimp [z,z']; omega
    let w:=2*p.j-3*z
    let w' := 2*q.j-3*z'
    have hw:w+3*z=2*p.j∧w' + 3*z' = 2*q.j:= by
      dsimp [w,w']
      omega
    have hhalf : (w+w')/2=w/2+w' / 2 := by
      by_cases h:e 3≤2*p.t
      · have hz' : z' = 0:= by dsimp [z,z']; omega
        omega
      · have hze :z=2*p.t:=min_eq_right (by omega)
        omega
    let y :=min (e 2) (w/2)
    let y' := e 2 - y
    have hy :y+y' = e 2∧2*y≤w∧2*y' ≤ w' := by dsimp [y,y']; omega
    let x :=min (e 1) (w - 2*y)
    let x' := e 1 - x
    have hx :x + x' = e 1∧x+2*y≤w∧x' + 2*y' ≤ w' := by
      dsimp [x,x']
      omega
    let u:=min (e 0) (2*p.b-(x+y+z))
    let u' := e 0 - u
    have hu:u+u' = e 0∧u + x+y+z≤2*p.b ∧
        u' + x' + y' + z' ≤ 2*q.b:= by
      dsimp [u,u']
      omega
    let a :Fin 4 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![u,x,y,z]
    let b:Fin 4 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![u',x',y',z']
    refine ⟨a,(OW p a).mpr ?_,b,(OW q b).mpr ?_,?_⟩
    · change u + x+y+z≤2*p.b∧x+2*y+3*z≤2*p.j∧z≤2*p.t
      omega
    · change u' + x' + y' + z' ≤ 2*q.b∧x' + 2*y' + 3*z' ≤ 2*q.j∧z' ≤ 2*q.t
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact hz.1
private theorem bwG {ι:Type} [t7 ι] (fF:ι→ ox)
   (e :Kb fF →₀ ℕ) (i:ι) :
   oy (step ∘ Fd fF) e i≠0 ↔
     ∃ v :Kb fF,v.1=i∧e v≠0:= by
 classical
 simp only [SW,Finsupp.sum,Zh,Sd ,
   Fd,step,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,Nat.cast_id]
 rw [← Nat.pos_iff_ne_zero,Finset.sum_pos_iff]
 constructor
 · rintro ⟨v,_,hv⟩
   by_cases hvi:v.1=i
   · exact ⟨v,hvi,SD (by simpa [hvi] using hv)⟩
   · rw [Ye (Ne.symm hvi)] at hv
     simp at hv
 · rintro ⟨v,hvi,hv⟩
   exact ⟨v,Finsupp.mem_support_iff.mpr hv,by simpa [hvi] using Nq hv⟩
private theorem bKP {ι:Type} [t7 ι] (fF:ι→ ox) :
   Yz fF 0=0:= by
 ext m
 simp only [KH,Yz,Qx]
 constructor
 · rintro ⟨e,hdeg,hexp⟩
   have he :e=0:= by
     ext v
     rw [Finsupp.zero_apply]
     by_contra hv
     have hslot:=(bwG fF e v.1).mpr ⟨v,rfl,hv⟩
     simp [hdeg] at hslot
   simpa [he] using hexp.symm
 · rintro rfl
   exact ⟨0,p6 _,p6 _⟩
private theorem ccO {ι:Type} [t7 ι] (fF:ι→ ox)
    (a :ι→ℕ) (i:ι) :
    Yz fF (a+step i) =
      Yz fF a+capExponents (fF i) := by
  ext m
  constructor
  · rintro ⟨e,hdeg,hexp⟩
    have hne :oy (step ∘ Fd fF) e i≠0:= by
      simp [hdeg,step]
    obtain ⟨v,hvi,hv⟩:=(bwG fF e i).mp hne
    let e' := e-Finsupp.single v 1
    have hdeg' : oy (step ∘ Fd fF) e' + step i=a+step i:= by
      have h:=Zg (w:=step ∘ Fd fF) hv
      calc
        _=oy (step ∘ Fd fF) e := by
          simpa only [e',Sd ,Fd,hvi] using h
        _ = _:=hdeg
    refine ⟨oy (fun u:Kb fF=>u.2.val) e',
      ⟨e',add_right_cancel hdeg',rfl⟩,v.2.val,?_,?_⟩
    · simpa only [hvi] using v.2.property
    · exact (Zg hv).trans hexp
  · rintro ⟨m',⟨e,hdeg,hexp⟩,w,hw,rfl⟩
    let v :Kb fF:=⟨i,⟨w,hw⟩⟩
    refine ⟨e+Finsupp.single v 1,?_,?_⟩
    · rw [oY ,qG,II,hdeg]
      rfl
    · simp only [oY ,qG,II,hexp,v]
private theorem bWh:pz ⟨0,0,0⟩=0:= by
 ext m
 simp only [OW,KH,Nat.mul_zero]
 constructor
 · intro hm
   have h:=hm.1
   ext k
   fin_cases k
   · change m 0=0; omega
   · change m 1=0; omega
   · change m 2=0; omega
   · change m 3=0; omega
 · rintro rfl
   simp
theorem awr {ι:Type} [oK ι] (s :ι→ ox)
  (hs : ∀ i,bF (s i)) (a :ι→ℕ) :bF (ku s a) := by
 refine ⟨uW (fun i _=>qU (a i) (hs i).1),?_⟩
 change 3*(∑ i,a i*(s i).t) ≤ ∑ i,a i*(s i).j
 rw [ze]
 refine uW fun i _ => ?_
 rw [WK 3]
 exact qU (a i) (hs i).2
theorem gLV {ι:Type} [oK ι] [t7 ι]
    (s :ι→ ox) (hs : ∀ i,bF (s i)) (a :ι→ℕ) :
    Yz s a=pz (ku s a) := by
  induction a using WellFounded.induction (measure (fun b:ι→ℕ => ∑ i,b i)).wf with
  | h a ih =>
    by_cases ha :a=0
    · rw [ha,bKP]
      simpa [ku] using bWh.symm
    · obtain ⟨i,hi⟩ : ∃ i,a i≠0:= by
        by_contra! h
        exact ha (funext h)
      let b:=a - step i
      have hab:b+step i=a := by
        funext k
        change a k - step i k+step i k=a k
        apply zxt
        by_cases hki:k=i
        · subst k
          simpa [step] using Nat.one_le_iff_ne_zero.mpr hi
        · simp [step,Ye hki]
      have hone : (∑ k,step i k)=1 := by
        rw [Fintype.sum_eq_single i]
        · simp [step]
        · intro k hk
          simp [step,Ye hk]
      have hsum: (∑ k,a k)=(∑ k,b k)+1 := by
        rw [← hab]
        simp only [Vq,zfW,hone]
      have hlt: (∑ k,b k) < ∑ k,a k := by omega
      rw [← hab,ccO,aES,aQe,ih b hlt,
        dEQ (awr s hs b) (hs i)]
end bav
end
section
namespace bav
noncomputable section
open aR dN Dr Kd lB MvPolynomial Filter
open ap8 (BZ bgE aES)
open scoped BigOperators
variable {ι:Type} [oK ι]
private theorem dsz (J:aU n5) (q:ox) (hq:vj q) (n:ℕ) :
   Qy (J.comap (monomialMap c9 (pz q)).toRingHom) n =
     Sn J (pz (q.scale n)) := by
 rw [bzA.proof,bzz.proof (fun _:Unit=>q) (fun _=>hq)]
 simp [ku,vi]
private theorem cpi (fF:ι→ ox) (n:ℕ) (v :ι→ℕ) :
  ku fF (fun i=>n*v i)=(ku fF v).scale n:= by
 simp [ku,vi ,uh,ze]
private theorem aCx (p:ox) (hp:vj p) :
  vh (monomialMap c9 (pz p)) := by
 apply monomialMap_surjective
 intro i
 have ⟨hb,hj,ht⟩:=hp
 fin_cases i <;>
  norm_num [aiK.OW,EK] <;> omega
private theorem aXZ (J:aU n5) {p q:ox} (h:aO p q) :
  Sn J (pz p)≤Sn J (pz q) := by
 have hsub:pz p⊆pz q:= fun _ he =>
  ⟨he.1.trans (qU _ h.1),he.2.1.trans (qU _ h.2.1),
    he.2.2.trans (qU _ h.2.2)⟩
 have :Hw c9 (yJ c9 (pz q)) :=
  Module.Finite.of_basis (zzc c9 _)
 exact Submodule.finrank_mono (Submodule.map_mono (restrictSupport_mono c9 hsub))
private theorem cpk (p q:ox) (hq:vj q) :
   ∃ C:ℕ,∀ n,aO (q.scale n) (p.plus (q.scale n)) ∧
     aO (p.plus (q.scale n)) (q.scale (n+C)) := by
 let C:=p.b+p.j+p.t
 have ⟨hb,hj,ht⟩:=hq
 have bound (a b:ℕ) (ha :a≤C) (hpos :0<b) (n:ℕ) :
     a+n*b≤(n+C)*b:= by
   rw [UY ,NX a]
   exact R9 (ha.trans (Nat.le_mul_of_pos_right _ hpos)) _
 refine ⟨C,fun n=>⟨⟨Pv _ _,Pv _ _,Pv _ _⟩,
   ⟨bound p.b q.b (by dsimp [C]; omega) (by omega) n,
    bound p.j q.j (by dsimp [C]; omega) (by omega) n,
    bound p.t q.t (by dsimp [C]; omega) ht n⟩⟩⟩
theorem gLW (fF:ι→ ox) (J:aU n5) (base :ι)
    (hs : ∀ i,bF (fF i)) (hbase :0<(fF base).t)
    (P:nX ι ℚ) (u:ι→ℕ)
    (hu : ∀ a≥u,p5 (fun i=>(a i:ℚ)) P =
      (Sn J (pz (ku fF a)) :ℚ))
    (v :ι→ℕ) (hv :0<v base) (d:ℕ) (hd:JQ J≤d) :
    (BZ P u v).natDegree≤JQ J ∧
    (BZ P u v).coeff d=capCoeff J d (ku fF v) := by
  let q:=ku fF v
  have hch:bF q:=awr fF hs v
  have htop:0<q.t :=
    (WY hv hbase).trans_le
      (Pc (f := fun i=>v i*(fF i).t)
        (fun _ _=>In _) (vk base))
  have hq:vj q:=⟨hch.1,hch.2,htop⟩
  let I:=J.comap (monomialMap c9 (pz q)).toRingHom
  let Q:=yl I
  have hfil (n:ℕ) :Qy I n=Sn J (pz (q.scale n)) :=
    dsz J q hq n
  have hQ:Q.natDegree=JQ J :=
    natDegree_affineHilbertPolynomial_comap_of_surjective _ (aCx q hq) J
  obtain ⟨C,hC⟩:=cpk (ku fF u) q hq
  have hR (n:ℕ) : (BZ P u v).eval (n:ℚ) =
      (Sn J (pz ((ku fF u).plus (q.scale n))) :ℚ) := by
    rw [bgE]
    change p5 (fun i=>(((u+fun j=>n*v j) i:ℕ) :ℚ)) P= _
    rw [hu (u+fun i=>n*v i) (fun i=>zi _ _),aES,cpi]
  have hshift:Tendsto (fun n:ℕ=>n+C) pG atTop :=
    tendsto_atTop_mono (fun n=>zi n C) tendsto_id
  have hlo : ∀ᶠ n:ℕ in pG,Q.eval (n:ℚ)≤(BZ P u v).eval (n:ℚ) := by
    filter_upwards [zaM I] with n hn
    rw [show Q.eval (n:ℚ)=(Qy I n:ℚ) from hn,hfil n,hR]
    exact_mod_cast aXZ J (hC n).1
  have hhi : ∀ᶠ n:ℕ in pG,
      (BZ P u v).eval (n:ℚ)≤(wR (C:ℚ) Q).eval (n:ℚ) := by
    filter_upwards [hshift.eventually (zaM I)] with n hn
    rw [Polynomial.taylor_eval,← Nat.cast_add,show Q.eval ((n+C:ℕ) :ℚ) =
      (Qy I (n+C) :ℚ) from hn,hfil (n+C),hR]
    exact_mod_cast aXZ J (hC n).2
  have hT: (wR (C:ℚ) Q).natDegree=JQ J :=
    (Polynomial.natDegree_taylor Q _).trans hQ
  have hdeg: (BZ P u v).natDegree≤JQ J :=
    (Polynomial.natDegree_le_of_eventually_eval_natCast_le
      (Eventually.of_forall fun n=> by rw [hR]; positivity) hhi).1.trans_eq hT
  have hl:=zKB
    (hQ.trans_le hd) (hdeg.trans hd) hlo
  have hh:=zKB
    (hdeg.trans hd) (hT.trans_le hd) hhi
  rw [Polynomial.coeff_taylor_of_natDegree_le _ (hQ.trans_le hd)] at hh
  exact ⟨hdeg,wA hh hl⟩
end
end bav
end
section
namespace bRd
noncomputable section
open Polynomial aR jA
private def aO8 (p:ao[X]) :ao[X][X] :=p.map C
@[simp] private theorem eIr (p:ao[X]) (z :ao) :
   (aO8 p).map (qM z)=p:= by
  rw [aO8,sI]
  have h: (qM z).comp C=LQ ao:= by
   ext x
   simp
  rw [h,Xx]
@[simp] private theorem gRo (p:ao[X]) :
   (aO8 p).map (cy ao[X] kS)=jH p:= by
  rw [aO8,jH,sI,
   ← Zt,← zYY ao ao[X] kS]
private theorem ce1 {F:Type*} [zc F] {H A:F[X]}
  (hH :H.Monic) {n:ℕ} (hA:A.natDegree≤n) (hc:xI A H) :
  H.resultant A H.natDegree n≠0:= by
 have e :=resultant_add_right_deg H A H.natDegree A.natDegree
  (n - A.natDegree) th
 rw [GR hA,coeff_natDegree,hH.leadingCoeff,KA,xm] at e
 rw [e]
 exact ((zgx hH).mpr hc.symm).ne_zero
private theorem coJ {F:Type*} [zc F] {H A U V:F[X]} {d:F}
  (hd:d≠0) (h:H*U + A*V=C d) :xI A H := by
 refine ⟨C d⁻¹*V,C d⁻¹*U,?_⟩
 calc
  _=C d⁻¹*(H*U + A*V) := by ring
  _=1 := by rw [h,← C_mul,Du hd,C_1]
private theorem aQ3 {F:Type*} [zc F] {H A B N :F[X]} {d:F}
    (hd:d≠0) (h:H∣A*N+C d*B) :
    H∣A*(C d⁻¹*N)+B:= by
  have hunit :C d⁻¹*C d=(1 :F[X]) := by
    rw [← C_mul,Du hd,C_1]
  calc
    H∣C d⁻¹*(A*N+C d*B) :=h.mul_left _
    _=A*(C d⁻¹*N)+B:= by
      calc
        _=A*(C d⁻¹*N)+(C d⁻¹*C d)*B:= by ring
        _ = _:= by rw [hunit,xm]
theorem proof :jA.c1 := by
 intro Γ s P
 let H :=aO8 P.H
 let A:=aO8 P.c*(aO8 P.a₀+C (oj:ao[X])*aO8 P.a₁)
 let B:=C (oj:ao[X])*aO8 P.q
 let den:=H.resultant A H.natDegree A.natDegree
 have hH :H.Monic:=P.monic.map C
 have hdeg:H.natDegree=P.H.natDegree :=Z0 C_injective _
 have hpos :0<H.natDegree := by rw [hdeg]; exact P.small.1
 have hHne :H≠1 := by
   intro e
   simp [e] at hpos
 have hregular (z :ao) (hc:xI (P.a₀+C z*P.a₁) P.H) :den.eval z≠0:= by
   let e :=qM z
   have heH :H.map e=P.H :=eIr _ _
   have heA:A.map e=P.c*(P.a₀+C z*P.a₁) := by
     simp [A,e]
   have hedeg: (H.map e).natDegree=H.natDegree := by rw [heH,hdeg]
   change e (H.resultant A H.natDegree A.natDegree)≠0
   rw [← resultant_map_map,← hedeg]
   exact ce1 (hH.map e) RC (by
     rw [heH,heA]
     exact P.c_unit.mul_left hc)
 have hzero :den.eval 0≠0:=hregular 0 (by simpa using P.a₀_unit)
 have hden:den≠0:= by
   intro hz
   exact hzero (by simp [hz])
 obtain ⟨U,V,_,_,hbezout⟩:=zKy H A th th
   (Gi (SD hpos))
 change H*U + A*V=C den at hbezout
 let num :=(-B*V) %ₘ H
 have hsmall:num.natDegree<P.H.natDegree := by
   rw [← hdeg]
   exact Yo _ hH hHne
 have hcleared:H∣A*num+C den*B:= by
   obtain ⟨W,hW⟩:=dvd_modByMonic_sub (-B*V) H
   refine ⟨A*W+B*U,?_⟩
   change num-(-B*V)=H*W at hW
   linear_combination A*hW - B*hbezout
 let f :=cy ao[X] kS
 have hf :f den≠0 :=
   (Bf f (xL ao[X] kS)).mpr hden
 refine ⟨{ numerator :=num
           denominator :=den
           at_zero :=hzero
           small:=hsmall
           generic_unit := ?_
           generic_congruence := ?_
           regular := fun γ hγ=>hregular (P.z γ) (P.regular γ hγ)
           quotient := ?_ }⟩
 · have hm:=lz (u8 f) hbezout
   simp only [yo ,z7,v8 ,sS] at hm
   have hc:=coJ hf hm
   simpa [H,A,f] using hc
 · have hm:=RP f hcleared
   simp only [z7,v8 ,sS] at hm
   have hc:=aQ3 hf hm
   simpa [H,A,B,f,ahH] using hc
 · intro γ hγ
   let z :=P.z γ
   let e :=qM z
   have hz :e den≠0:=hregular z (P.regular γ hγ)
   have hm:=RP e hcleared
   simp only [z7,v8 ,sS] at hm
   have hc:P.H∣P.c*(P.a₀+C z*P.a₁)*Tj num den z+C z*P.q:= by
     simpa [H,A,B,e,Tj] using aQ3 hz hm
   have hu:=(P.c_unit.mul_left (P.regular γ hγ)).symm
   have hd:P.H∣extend (s γ) - Tj num den z := by
     apply hu.dvd_of_dvd_mul_left
     simpa [mul_sub,z] using dvd_sub (P.residue γ hγ) hc
   obtain ⟨T,hT⟩:=hd
   refine ⟨T,?_,sub_eq_iff_eq_add.mp hT⟩
   by_cases hTzero :T=0
   · simp [hTzero]
   have hres : (Tj num den z).natDegree<P.H.natDegree :=
     ((natDegree_C_mul_le _ _).trans RC).trans_lt hsmall
   have hS: (extend (s γ)).natDegree≤131071+P.H.natDegree := by
     simpa only [extend,natDegree_map] using P.degree γ hγ
   have hb:=(natDegree_sub_le (extend (s γ)) (Tj num den z)).trans
     (max_le hS (by omega))
   rw [hT,P.monic.natDegree_mul' hTzero] at hb
   omega
end
end bRd
end
section
namespace as5
open Jq MvPolynomial
open scoped BigOperators
private theorem dVm {p q:Form} (hp:OQ p)
   (hq:OQ q) : (p+q).totalDegree=max p.totalDegree q.totalDegree := by
 classical
 rcases lt_trichotomy p.totalDegree q.totalDegree with h | h | h
 · rw [totalDegree_add_eq_right_of_totalDegree_lt h,max_eq_right h.le]
 · rw [← h,max_self]
   refine wA ((totalDegree_add p q).trans_eq (by rw [← h,max_self])) ?_
   by_cases he :p=0
   · simp [he]
   obtain ⟨a,ha,hd⟩:=p.support.exists_mem_eq_sup (by simpa using he)
     (fun m:jJ=>m.degree)
   change p.totalDegree=a.degree at hd
   have hpa :0<p.coeff a :=
     GB (hp a hd.le) (Ne.symm (mem_support_iff.mp ha))
   have hqa :=hq a (h.symm.trans_le hd.le)
   have hsum:a∈(p+q).support :=mem_support_iff.mpr (by
     change p.coeff a+q.coeff a≠0
     exact (add_pos_of_pos_of_nonneg hpa hqa).ne')
   exact hd.le.trans (le_totalDegree hsum)
 · rw [ztH h,max_eq_left h.le]
private theorem top_add {p q:Form} (hp:OQ p) (hq:OQ q) :
  OQ (p+q) := by
 intro a ha
 rw [dVm hp hq] at ha
 change 0≤p.coeff a+q.coeff a
 exact add_nonneg (hp a ((le_max_left _ _).trans ha)) (hq a ((le_max_right _ _).trans ha))
theorem bO6 {ι:Type} (S:nI ι) (f :ι→Form)
   (h : ∀ i∈S,OQ (f i)) :OQ (∑ i∈S,f i) := by
 classical
 induction S using Kl with
 | empty=>simp [OQ]
 | insert a S ha ih =>
   rw [Mk ha]
   exact top_add (h _ (Kc _ _))
     (ih fun i hi=>h i (IU hi))
private theorem top_mul {p q:Form} (hp:OQ p) (hq:OQ q) :
   OQ (p*q) := by
 classical
 by_cases hpn:p=0
 · simp [hpn,OQ]
 by_cases hqn:q=0
 · simp [hqn,OQ]
 intro a ha
 rw [totalDegree_mul_of_isDomain hpn hqn] at ha
 rw [coeff_mul]
 apply zlo
 intro bc hbc
 have hd:=lz Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hbc)
 rw [oY] at hd
 by_cases hb:p.totalDegree<bc.1.degree
 · rw [ Xp hb,zero_mul]
 by_cases hc:q.totalDegree<bc.2.degree
 · rw [ Xp hc,mul_zero]
 exact mul_nonneg (hp _ (by omega)) (hq _ (by omega))
private theorem bh2 {r :ℚ} (hr :0≤ r) :OQ (C r :Form) := by
 intro a _
 rw [coeff_C]
 split <;> simp_all
private theorem top_prod {ι:Type} (S:nI ι) (f :ι→Form)
   (h : ∀ i∈S,OQ (f i)) :OQ (∏ i∈S,f i) := by
 classical
 induction S using Kl with
 | empty=>simpa using (bh2 (r :=1) zero_le_one)
 | insert a S ha ih =>
   rw [zqX ha]
   exact top_mul (h _ (Kc _ _))
     (ih fun i hi=>h i (IU hi))
private theorem gCj (j:Fin 5) (r :ℚ) :OQ (lV j+C r :Form) := by
 classical
 intro a ha
 rw [ztH (by simp),totalDegree_X] at ha
 have hr : (C r :Form).totalDegree<a.degree := by
  simpa only [totalDegree_C] using Nat.lt_of_succ_le ha
 change 0≤(lV j:Form).coeff a+(C r :Form).coeff a
 rw [ Xp hr,G6,coeff_X]
 split <;> simp
noncomputable def bN5 (j:Fin 5) (d k :ℕ) :Form :=
 C ((d.factorial:ℚ)⁻¹) *
   ∏ r∈p7 d,(lV j+C ((r :ℚ)+1-(k :ℚ)))
theorem gsN (j:Fin 5) (d k :ℕ) :OQ (bN5 j d k) := by
 exact top_mul (bh2 (by positivity))
  (top_prod _ _ fun r _=>gCj j _)
private theorem dtn (d:ℕ) (z :ℚ) :
   (ascPochhammer ℚ d).eval z = ∏ r∈p7 d,(z+(r :ℚ)) := by
 induction d with
 | zero=>simp [ascPochhammer_zero]
 | succ d ih =>
   rw [ascPochhammer_succ_eval,Finset.prod_range_succ,ih]
theorem gsM (j:Fin 5) (d k :ℕ) (t:jJ) (h:k≤t j+d) :
  eval (fun i=>(t i:ℚ)) (bN5 j d k)=((t j+d - k).choose d:ℚ) := by
 rw [← zg1 ℚ d h]
 simp only [bN5,oz ,FQ,JW,oY ,Gr,zcb,
  Polynomial.eval_smul,LO,Polynomial.eval_comp,zvF,
  Polynomial.eval_sub,MO,Te,Polynomial.eval_one,dtn]
 congr 1
 exact Dz rfl fun _ _=> by ring
theorem gCm (f :Fin 5→Form) (h : ∀ i,OQ (f i)) :
  OQ (∏ i,f i) :=
 top_prod _ _ fun i _=>h i
end as5
end
section
namespace bjx
noncomputable section
open aR jA Polynomial
open scoped Polynomial
set_option maxRecDepth 4000
private abbrev Fiber :=t5 Lower
private abbrev UA:Lower →+* Fiber :=cy _ _
private abbrev aHD:ao →+* Lower :=MvPolynomial.C.comp DI
private theorem asy :p9 UA :=
 xL Lower Fiber
theorem bbK (F:ko) (a :ao[X]) :
   qN (pad F a)=qN F*a.map aHD:= by
 let e :=(xu iP (Fin 3)).toRingHom
 let l:=e.comp (GY nq (lV none))
 let r :=u8 (nq:iP →+* Lower)
 have h:l=r := by
   apply C5
   · intro x
     simp [l,r,e,MvPolynomial.optionEquivLeft_C]
   · simp [l,r,e,MvPolynomial.optionEquivLeft_X_none]
 change e (F*(GY nq (lV none)) (a.map DI))= _
 rw [oz]
 congr 1
 change l (a.map DI)= _
 rw [h,yo ,sI]
private theorem bYO {f g:Lower[X]} (hf :f≠0)
   (hfg:IsRelPrime f g) :xI (f.map UA) (g.map UA) := by
 classical
 let:NormalizedGCDMonoid Lower :=Nonempty.some z9
 apply IsRelPrime.isCoprime
 intro d hdf hdg
 have hd:d≠0:= by
   intro he
   exact (Polynomial.map_ne_zero_iff asy).mpr hf (zero_dvd_iff.mp (he ▸ hdf))
 let D:=IsLocalization.integerNormalization (Yc Lower) d
 obtain ⟨b,hb,hbD⟩:=IsLocalization.integerNormalization_spec (Yc Lower) d
 change D.map UA=b•d at hbD
 rw [Oc,Polynomial.algebraMap_apply] at hbD
 have hscale :vl (C (UA b)) :=
   isUnit_C.mpr ((Bf UA asy).mpr (G5 hb)).isUnit
 have hD:D.primPart.map UA∣d:= by
   apply (IsUnit.dvd_mul_left hscale).mp
   have hfac:=lz (Polynomial.map UA) D.eq_C_content_mul_primPart
   rw [v8] at hfac
   rw [← hbD,hfac]
   exact dvd_mul_left _ _
 have hu:vl D.primPart :=
   hfg (D.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hD.trans hdf))
     (D.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hD.trans hdg))
 have hdeg:d.natDegree=D.natDegree := by
   rw [← Z0 asy,hbD]
   rw [natDegree_C_mul ((Bf UA asy).mpr
     (G5 hb))]
 have he :d=C (d.coeff 0) :=eq_C_of_natDegree_eq_zero (by
   rw [hdeg,← D.natDegree_primPart,natDegree_eq_zero_of_isUnit hu])
 have hc:d.coeff 0≠0:= fun hz=>hd (he.trans (by simp [hz]))
 exact he.symm ▸ isUnit_C.mpr hc.isUnit
private theorem bpL (f :Fiber[X]) (hf :f≠0) (avoid :nI Fiber) :
  ∃ a :ao,let x :=UA (aHD a); f.eval x≠0∧x∉avoid := by
 classical
 let emb:ao→Fiber := fun a=>UA (aHD a)
 have he :p9 emb:= by
  intro a b h
  exact DI.injective ((MvPolynomial.C_injective (Fin 3) iP) (asy h))
 obtain ⟨_,⟨a,rfl⟩,ha⟩ :=
  (Set.infinite_range_of_injective he).exists_notMem_finset (f.roots.toFinset∪avoid)
 refine ⟨a,?_⟩
 change f.eval (emb a)≠0∧emb a∉avoid
 simp only [Finset.mem_union,Multiset.mem_toFinset,mem_roots hf,not_or] at ha
 exact ⟨ha.1,ha.2⟩
private theorem bnY (f :Fiber[X]) {a :Fiber} (h:f.eval a≠0) :
   xI ((oj:Fiber[X]) - C a) f :=
 ((monic_X_sub_C a).irreducible_of_degree_eq_one (degree_X_sub_C a)).coprime_iff_not_dvd.mpr
   (fun hd=>h (dvd_iff_isRoot.mp hd))
private theorem aL9 {F:ko} (hF:F≠0) :qN F≠0 :=
 (Bf (xu iP (Fin 3))
   (xu iP (Fin 3)).injective).mpr hF
end
end bjx
end
section
namespace bjx
noncomputable section
open aR jA Polynomial
open scoped Polynomial BigOperators Pointwise
set_option maxRecDepth 4000
private abbrev deg {σ:Type*} (w:σ→ℕ) (P:nX σ iP) :ℕ :=
 P.weightedTotalDegree w
private theorem cJK {σ ι:Type*} (w:σ→ℕ) {s :nI ι}
  {p:ι→nX σ iP} {B:ℕ} (h : ∀ i∈s,deg w (p i)≤B) :
  deg w (∑ i∈s,p i)≤B:= by
 classical
 apply (AddMonoidAlgebra.supDegree_sum_le (D:=oy w)).trans
 exact X4 h
private theorem dVa {σ ι:Type*} (w:σ→ℕ) (s :nI ι)
  (p:ι→nX σ iP) :
  deg w (∏ i∈s,p i) ≤ ∑ i∈s,deg w (p i) :=
 AddMonoidAlgebra.supDegree_prod_le (D:=oy w) (p6 _) (oY _)
private theorem dU8 {σ:Type*} (w:σ→ℕ) (p q:nX σ iP) :
  deg w (p*q)≤deg w p+deg w q :=
 AddMonoidAlgebra.supDegree_mul_le (D:=oy w) (oY _)
private theorem dU9 {σ:Type*} (w:σ→ℕ) (p:nX σ iP) :
  deg w (-p)=deg w p :=
 AddMonoidAlgebra.supDegree_neg (D:=oy w)
private theorem dU6 {σ:Type*} (w:σ→ℕ) (a :iP) :
  deg w (nq a)=0:= by
 classical
 change (nq a :nX σ iP).support.sup (oy w)=0
 rw [MvPolynomial.support_C]
 split <;> simp
private theorem dU7 (w:Fin 3→ℕ) (F:ko) (i:ℕ) :
  deg w ((qN F).coeff i)≤deg (fun o=>o.elim 0 w) F:= by
 apply X4
 intro m hm
 have hs :m.optionElim i∈F.support := by
  rw [zuk] at hm ⊢
  simpa only [qN,z9x] using hm
 have h:=z6P (fun o=>o.elim 0 w) hs
 rw [SW,Finsupp.sum_option_index_smul] at h
 simpa only [Option.elim_none,Option.elim_some,smul_zero,Gj,Finsupp.some_optionElim,
  SW] using h
private theorem aNa (w:Fin 3→ℕ) (F:ko) (a :ao[X]) (i:ℕ) :
  deg w ((qN (pad F a)).coeff i)≤deg (fun o=>o.elim 0 w) F:= by
 rw [bbK,Polynomial.coeff_mul]
 apply cJK
 intro j _
 rw [zg]
 refine (dU8 _ _ _).trans ?_
 change deg w ((qN F).coeff j.1) +
  deg w (nq (DI (a.coeff j.2)))≤_
 rw [dU6,G6]
 exact dU7 w F j.1
private theorem boN (w:Fin 3→ℕ) (f g:Lower[X]) (m n B D:ℕ)
   (hf : ∀ i,deg w (f.coeff i)≤B) (hg : ∀ i,deg w (g.coeff i)≤D) :
   deg w (f.resultant g m n)≤ m*D + n*B:= by
 classical
 let A:=f.sylvester g m n
 have hl (i:Fin (m+n)) (j:Fin m) :deg w (A i (j.castAdd n))≤D:= by
   simp only [A,sylvester,Matrix.of_apply,Fin.addCases_left]
   split
   · apply hg
   · simp [z4a]
 have hr (i:Fin (m+n)) (j:Fin n) :deg w (A i (j.natAdd m))≤B:= by
   simp only [A,sylvester,Matrix.of_apply,Fin.addCases_right]
   split
   · apply hf
   · simp [z4a]
 change deg w A.det≤_
 rw [Matrix.det_apply]
 apply cJK
 intro π _
 have hp:deg w (∏ i,A (π i) i)≤ m*D + n*B:= by
   apply (dVa w Kv _).trans
   rw [Fin.sum_univ_add]
   have h₁ : ∑ j:Fin m,deg w (A (π (j.castAdd n)) (j.castAdd n)) ≤ ∑ _j:Fin m,D :=
     uW fun j _=>hl _ j
   have h₂ : ∑ j:Fin n,deg w (A (π (j.natAdd m)) (j.natAdd m)) ≤ ∑ _j:Fin n,B :=
     uW fun j _=>hr _ j
   simpa only [Mw ,S1 ,Pj,UZ]
     using zk h₁ h₂
 rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hh | hh <;>
   simpa [hh,dU9] using hp
end
end bjx
end
section
namespace as5
open Jq
open scoped BigOperators
abbrev Cell {σ:Type} (b:σ →₀ ℕ) :=(x :σ)→Fin (b x+1)
def clip {σ:Type} (b a :σ →₀ ℕ) :Cell b :=
 fun x=>⟨min (a x) (b x),SM (min_le_right _ _)⟩
noncomputable def base {σ:Type} [qy σ] {b:σ →₀ ℕ} (u:Cell b) :σ →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm fun x=>(u x).val
@[simp] theorem blO {σ:Type} [qy σ] {b:σ →₀ ℕ} (u:Cell b) (x :σ) :
   base u x=(u x).val :=rfl
private theorem c25 {σ:Type} [qy σ] {b:σ →₀ ℕ}
  {A:nI (σ →₀ ℕ)} (hA : ∀ d∈A,d≤b) (a :σ →₀ ℕ) :
  base (clip b a)∈zJ A↔a∈zJ A:= by
 change (∀ d∈A,¬ d≤base (clip b a))↔(∀ d∈A,¬ d≤a)
 have hd (d:σ →₀ ℕ) (hm:d∈A) :d≤base (clip b a)↔d≤a := by
  constructor
  · intro h x
    exact (h x).trans (Xo _ _)
  · intro h x
    exact le_min (h x) (hA d hm x)
 exact ⟨fun h d hm hle=>h d hm ((hd d hm).mpr hle),
  fun h d hm hle=>h d hm ((hd d hm).mp hle)⟩
theorem bPV {σ:Type} [oK σ] (s :σ→Fin 5) (a :σ →₀ ℕ)
   (j:Fin 5) :oy (jT s) a j =
     ∑ x∈Finset.univ.filter (fun x=>s x=j),a x := by
 rw [Fz ,Xu,Np]
 apply qx rfl
 intro x _
 by_cases h:s x=j
 · simp [jT,zY,h]
 · simp [jT,zY,h,Ne.symm h]
private theorem ea5 {σ:Type} [oK σ] (s :σ→Fin 5) (t:jJ) :
  {a :σ →₀ ℕ | oy (jT s) a=t}.Finite := by
 classical
 apply (Finsupp.finite_of_degree_le (σ:=σ) (∑ x :σ,t (s x))).subset
 intro a ha
 change oy (jT s) a=t at ha
 rw [Qx ,zFi]
 refine uW fun x _ => ?_
 rw [← ha,bPV]
 exact Pc (f := fun v=>a v) (fun _ _=>In _)
  (by simp)
def alB {σ:Type} (s :σ→Fin 5) {b:σ →₀ ℕ} (u:Cell b)
    (t:jJ) :Set (σ →₀ ℕ) :=
  {a | clip b a=u∧oy (jT s) a=t}
noncomputable def Ax {σ:Type} [oK σ] {b:σ →₀ ℕ}
  (A:nI (σ →₀ ℕ)) :nI (Cell b) := by
 classical
 exact Finset.univ.filter fun u=>base u∈zJ A
theorem dGp {σ:Type} [oK σ] {b:σ →₀ ℕ} {A C:nI (σ →₀ ℕ)}
  (h:zJ C⊆zJ A) :Ax (b:=b) C⊆Ax A:= by
 classical
 intro u hu
 simp only [Ax,zO0,vk,true_and] at hu ⊢
 exact h hu
theorem dej {σ:Type} [oK σ] (s :σ→Fin 5)
   (b:σ →₀ ℕ) (A:nI (σ →₀ ℕ)) (hA : ∀ d∈A,d≤b) (t:jJ) :
   DL s A t = ∑ u∈Ax (b:=b) A,(alB s u t).ncard:= by
 classical
 let S:=Ax (b:=b) A
 have heq : {a∈zJ A | oy (jT s) a=t} =
     ⋃ u∈(S:Set (Cell b)),alB s u t:= by
   ext a
   simp only [Qx ,Set.mem_iUnion,Finset.mem_coe,alB]
   constructor
   · rintro ⟨ha,ht⟩
     exact ⟨clip b a,by simpa [S,Ax] using (c25 hA a).mpr ha,rfl,ht⟩
   · rintro ⟨u,hu,rfl,ht⟩
     exact ⟨(c25 hA a).mp (by simpa [S,Ax] using hu),ht⟩
 have hf (u:Cell b) : (alB s u t).Finite :=
   (ea5 s t).subset fun _ ha=>ha.2
 have hd: (S:Set (Cell b)).PairwiseDisjoint (fun u=>alB s u t) := by
   intro u _ v _ huv
   exact Set.disjoint_left.mpr fun _ ha hb=>huv (ha.1.symm.trans hb.1)
 rw [DL,heq,
   (WD S).ncard_biUnion (fun u _=>hf u) hd,
   finsum_mem_eq_finite_toFinset_sum _ (WD S)]
 have hS: (WD S).toFinset=S:= by
   ext u
   rw [Set.Finite.mem_toFinset,Finset.mem_coe]
 rw [hS]
end as5
end
section
namespace as5
open Jq MvPolynomial
open scoped BigOperators
section
variable {σ:Type} [oK σ] {b:σ →₀ ℕ}
private theorem bXm (u:Cell b) (a :σ →₀ ℕ) :
   clip b a=u↔base u≤a ∧ ∀ x,(u x).val<b x→a x=base u x := by
 constructor
 · intro h
   have hx (x :σ) :min (a x) (b x)=(u x).val :=
     lz (fun v :Cell b=>(v x).val) h
   refine ⟨fun x=>(hx x).symm.le.trans (Xo _ _),fun x hlt => ?_⟩
   have hm:=hx x
   change a x=(u x).val
   rw [min_def] at hm
   split at hm <;> omega
 · rintro ⟨hle,hfix⟩
   funext x
   apply Fin.ext
   change min (a x) (b x)=(u x).val
   have hcap:=Ef (u x).isLt
   by_cases hlt: (u x).val<b x
   · have hfixx :a x=(u x).val :=hfix x hlt
     rw [hfixx,min_eq_left hcap]
   · have he : (u x).val=b x := by omega
     have hlex : (u x).val≤a x :=hle x
     rw [he,min_eq_right (he ▸ hlex)]
private def free (s :σ→Fin 5) (u:Cell b) (j:Fin 5) :nI σ :=
 Finset.univ.filter fun x=>s x=j∧(u x).val=b x
private theorem ahR {s :σ→Fin 5} {u:Cell b} {j:Fin 5} {x :σ} :
  x∈free s u j↔s x=j∧(u x).val=b x := by
 simp [free]
private noncomputable def offset (s :σ→Fin 5) (u:Cell b) :jJ :=
 oy (jT s) (base u)
omit [oK σ] in
private theorem cw7 {S:nI σ} {r :σ →₀ ℕ} (hs :r.support⊆S)
  {x :σ} (hx :x∉S) :r x=0 :=
 Finsupp.notMem_support_iff.mp (fun hm=>hx (hs hm))
private abbrev bQv [t7 σ] (s :σ→Fin 5) (u:Cell b) (t:jJ) :=
 ∀ j:Fin 5,(free s u j).finsuppAntidiag (t j - offset s u j)
private noncomputable def dhj [t7 σ] (s :σ→Fin 5) (u:Cell b)
    (t:jJ) (a :alB s u t) :bQv s u t:= by
  let r :=a.val - base u
  have hc:=(bXm u a.val).mp a.prop.1
  have hrt:r+base u=a.val :=tsub_add_cancel_of_le hc.1
  have hw:=lz (fun e :σ →₀ ℕ=>oy (jT s) e) hrt
  rw [oY ,a.prop.2] at hw
  intro j
  refine ⟨r.filter (fun x=>s x=j),Finset.mem_finsuppAntidiag.mpr ⟨?_,?_⟩⟩
  · have h:=lz (fun g:jJ=>g j) hw
    change oy (jT s) r j+offset s u j=t j at h
    have hrj:oy (jT s) r j=t j - offset s u j:= by omega
    rw [← hrj,bPV]
    calc
      _ = ∑ x∈free s u j,r x := by
        exact qx rfl fun x hx =>
          Finsupp.filter_apply_pos _ _ (ahR.mp hx).1
      _ = _:=Wl
        (fun x hx=>Finset.mem_filter.mpr ⟨vk _,(ahR.mp hx).1⟩)
        (fun x hx hn=> by
          have he : (u x).val≠b x := fun he =>
            hn (ahR.mpr ⟨(Finset.mem_filter.mp hx).2,he⟩)
          have hlt: (u x).val<b x :=
            GB (Ef (u x).isLt) he
          change (a.val - base u) x=0
          rw [VH,hc.2 x hlt,tsub_self])
  · intro x hx
    rw [Finsupp.support_filter,zO0] at hx
    refine ahR.mpr ⟨hx.2,?_⟩
    by_contra he
    have hlt: (u x).val<b x :=GB (Ef (u x).isLt) he
    exact (Finsupp.mem_support_iff.mp hx.1) (by
      change (a.val - base u) x=0
      rw [VH,hc.2 x hlt,tsub_self])
private noncomputable def eeo [t7 σ] (s :σ→Fin 5) (u:Cell b)
    (t:jJ) (ht : ∀ j,offset s u j≤t j) (v :bQv s u t) :alB s u t:= by
  let r :σ →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun x=>(v (s x)).val x)
  have hv (j:Fin 5) :=Finset.mem_finsuppAntidiag.mp (v j).prop
  refine ⟨base u+r,(bXm u _).mpr ⟨le_add_right th,?_⟩,?_⟩
  · intro x hx
    have hr :r x=0:=cw7 (hv (s x)).2 (fun h=>hx.ne (ahR.mp h).2)
    simp [hr]
  · rw [oY]
    ext j
    change offset s u j+Finsupp.weight (jT s) r j=t j
    rw [bPV]
    have hs : (∑ x∈Finset.univ.filter (fun x=>s x=j),r x) =
        ∑ x∈free s u j,(v j).val x := by
      calc
        _ = ∑ x∈Finset.univ.filter (fun x=>s x=j),(v j).val x := by
          apply qx rfl
          intro x hx
          change (v (s x)).val x=(v j).val x
          rw [(Finset.mem_filter.mp hx).2]
        _ = _:=(Wl
          (fun x hx=>Finset.mem_filter.mpr ⟨vk _,(ahR.mp hx).1⟩)
          (fun _ _ h=>cw7 (hv j).2 h)).symm
    rw [hs,(hv j).1]
    exact GR (ht j)
private noncomputable def bWA [t7 σ] (s :σ→Fin 5) (u:Cell b)
    (t:jJ) (ht : ∀ j,offset s u j≤t j) :alB s u t ≃ bQv s u t where
  toFun:=dhj s u t
  invFun:=eeo s u t ht
  left_inv a := by
    apply pL
    ext x
    change base u x+(dhj s u t a (s x)).val x=a.val x
    change base u x+((a.val - base u).filter fun y=>s y=s x) x=a.val x
    rw [zfF,ite_eq_left (rfl :s x=s x),VH]
    exact GR ((bXm u a.val).mp a.prop.1 |>.1 x)
  right_inv v := by
    funext j
    apply pL
    ext x
    let r :σ →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun y=>(v (s y)).val y)
    change ((base u+r - base u).filter fun y=>s y=j) x=(v j).val x
    rw [NX (base u) r,add_tsub_cancel_right,zfF]
    split
    · rename_i hx
      change (v (s x)).val x=(v j).val x
      rw [hx]
    · rename_i hx
      exact (cw7 (Finset.mem_finsuppAntidiag.mp (v j).prop).2
        (fun h=>hx (ahR.mp h).1)).symm
private theorem bWC (s :σ→Fin 5) (u:Cell b) (t:jJ)
  (ht : ∀ j,offset s u j≤t j) :
  (alB s u t).ncard = ∏ j,(free s u j).card.multichoose (t j - offset s u j) := by
 classical
 rw [← JM,Nj (bWA s u t ht),
  XB,Fintype.card_pi]
 simp only [Fintype.card_coe,Finset.card_finsuppAntidiag_nat_eq_multichoose]
noncomputable def ayh (s :σ→Fin 5) (u:Cell b) :Form :=
 ∏ j:Fin 5,if (free s u j).card=0 then 0
   else bN5 j ((free s u j).card - 1) (offset s u j)
theorem bCn (s :σ→Fin 5) (u:Cell b) :OQ (ayh s u) := by
 apply gCm
 intro j
 split
 · simp [OQ]
 · exact gsN _ _ _
private theorem eF8 (s :σ→Fin 5) (u:Cell b) (j:Fin 5) :
   offset s u j≤b.degree := by
 rw [offset,bPV,zFi]
 refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_ |>.trans ?_
 · exact fun _ _ _=>In _
 · exact uW fun x _=>Ef (u x).isLt
theorem cEu (s :σ→Fin 5) (u:Cell b) (t:jJ)
   (ht : ∀ j,b.degree<t j) :
   eval (fun j=>(t j:ℚ)) (ayh s u)=((alB s u t).ncard:ℚ) := by
 have ho (j:Fin 5) :offset s u j<t j:=(eF8 s u j).trans_lt (ht j)
 rw [bWC s u t (fun j=>(ho j).le),Nat.cast_prod,ayh,JW]
 refine Dz rfl fun j _ => ?_
 cases hk : (free s u j).card with
 | zero =>
   have hh:t j - offset s u j=(t j - offset s u j - 1)+1 := by
     have :=ho j
     omega
   rw [ite_eq_left rfl,p6,hh,zGT,Nat.cast_zero]
 | succ d =>
   have hh:=ho j
   rw [ite_eq_right (Nat.succ_ne_zero _),Nat.succ_sub_one,gsM _ _ _ _ (by omega),
     z4m]
   congr 1
   rw [show d.succ+(t j - offset s u j) - 1=t j+d - offset s u j by omega]
   exact Nat.choose_symm_of_eq_add (by omega :t j+d - offset s u j =
     d+(t j - offset s u j))
end
end as5
end
section
namespace bRA
noncomputable section
open agO
open scoped Pointwise
private theorem evS {L M:Type} [qJ L] [G2 L]
    [MS L] [Ring.KrullDimLE 1 L] [AddCommGroup M] [Module L M]
    {x d:L} (hx :x≠0) (hd:d≠0) (I:aU L) (hdI:d∈I)
    (f :I →ₗ[L] M) (hf : ∀ a :I,f (x•a)=0) :
    qm L (Dw f)≤LR L x := by
  let J:aU L:=x•I
  have hJI:J≤I:=Submodule.smul_le_self_of_tower x I
  let g: (L ⧸ J) →ₗ[L] (L ⧸ I) :=Submodule.factor hJI
  have hmul :qm L (L ⧸ J)=qm L (L ⧸ I)+Ring.ord L x :=
    ziu (Ideal.mulQuot x I) (Ideal.quotOfMul x I)
      (Ideal.mulQuot_injective I (mem_nonZeroDivisors_iff_ne_zero.mpr hx))
      (Ideal.quotOfMul_surjective I) (Ideal.exact_mulQuot_quotOfMul I)
  have hfactor :qm L (L ⧸ J) =
      qm L (uJ g)+Module.length L (L ⧸ I) :=
    ziu (uJ g).subtype g
      (Submodule.subtype_injective _) (zSx hJI)
      (LinearMap.exact_subtype_ker_map g)
  have hfinite :qm L (L ⧸ I) ≠ ⊤ := by
    have hle :lJ {d} ≤ I:=(G3 I).mpr hdI
    have hlen:qm L (L ⧸ I)≤LR L d :=
      VS (Submodule.factor hle) (zSx hle)
    exact (hlen.trans_lt (Ring.ord_lt_top (mem_nonZeroDivisors_iff_ne_zero.mpr hd))).ne
  have hkernel:qm L (uJ g)=LR L x := by
    apply ENat.add_left_injective_of_ne_top hfinite
    exact hfactor.symm.trans (hmul.trans (NX _ _))
  let p:I →ₗ[L] (L ⧸ J) :=J.mkQ.comp I.subtype
  have hp:Dw p≤uJ g:= by
    rintro _ ⟨a,rfl⟩
    rw [Kz]
    change I.mkQ (a :L)=0
    exact (ziM I).mpr a.property
  have hker :uJ p≤uJ f := by
    intro a ha
    rw [Kz] at ha ⊢
    have haJ: (a :L)∈J:=(ziM J).mp ha
    obtain ⟨b,hb,hba⟩:=(zeT (a :L) x I).mp haJ
    have hab:a=x•(⟨b,hb⟩:I) :=pL hba.symm
    rw [hab,hf]
  let q:=(uJ p).liftQ f hker
  calc
    qm L (Dw f)=qm L (Dw q) :=
      lz (fun N :u9 L M=>qm L N)
        (Submodule.range_liftQ _ f hker).symm
    _≤qm L (I ⧸ uJ p) :=
      VS q.rangeRestrict q.surjective_rangeRestrict
    _=qm L (Dw p) :=p.quotKerEquivRange.length_eq
    _≤qm L (uJ g) :=
      zdt (zwh hp) (zaX hp)
    _=LR L x :=hkernel
theorem proof :agO.c3:= by
 classical
 intro L _ _ _ _ _ x hx B s
 let Q:aU B:=lJ {cy L B x}
 have hlift (i:s) : ∃ b:B,mD Q b=(i:aLX x B) :=
   Et (I:= Q) (i:aLX x B)
 choose lift hlift using hlift
 obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples_of_finite
   (Yc L) (fun i:s=>(lift i:t5 L))
 let a :=cy L (t5 L) (d:L)
 have hd0: (d:L)≠0:=G5 d.property
 have ha0:a≠0:=(Bf _ (xL L (t5 L))).mpr hd0
 let t:L →ₗ[L] t5 L :=
   (LinearMap.mul L (t5 L) a⁻¹).comp (Algebra.ofId L (t5 L)).toLinearMap
 have ht (r :L) :t r=a⁻¹*cy L (t5 L) r :=rfl
 let I:aU L:=B.toSubmodule.comap t
 have hdI: (d:L)∈I:= by
   change t (d:L)∈B
   rw [ht,show cy L (t5 L) (d:L)=a from rfl,Du ha0]
   exact B.one_mem
 let j:I →ₗ[L] B:=B.toSubmoduleEquiv.toLinearMap.comp
   (t.restrict (p:=I) (q:=B.toSubmodule) (fun _ hr=>hr))
 let f :I →ₗ[L] aLX x B:=(Fa L Q).toLinearMap.comp j
 have hzero (r :I) :f (x•r)=0:= by
   change mD Q (j (x•r))=0
   rw [j.map_smul,G7,Oc]
   exact Ideal.mem_span_singleton.mpr ⟨j r,rfl⟩
 have hspan:Submodule.span L (s :Set (aLX x B))≤Dw f := by
   apply Submodule.span_le.mpr
   intro y hy
   let i:s :=⟨y,hy⟩
   obtain ⟨r,hr⟩:=hd i
   have hr' : t r=(lift i:t5 L) := by
     rw [ht,hr,Oc]
     change a⁻¹*(a*(lift i:t5 L))= _
     rw [← uh,Du ha0,xm]
   have hrI:r∈I:= by
     change t r∈B
     rw [hr']
     exact (lift i).property
   have hj:j ⟨r,hrI⟩=lift i:=pL hr'
   refine ⟨⟨r,hrI⟩,?_⟩
   change mD Q (j ⟨r,hrI⟩)=y
   rw [hj]
   exact hlift i
 exact (zdt (zwh hspan)
   (zaX hspan)).trans (evS hx hd0 I hdI f hzero)
end
end bRA
end
section
set_option backward.isDefEq.respectTransparency false
namespace cy2
noncomputable section
open cu gT pI Ty akQ
open scoped BigOperators
private theorem eAs {F:Type} [zc F] {φ:oq →+* lK F}
   {k :Fin 4} (bY:aSD F φ k) {J I:aU oq}
   [Hw F (Zj φ J)] (hI:I.IsPrime) (hIJ:J≤I)
   (hsurv :I.map φ ≠ ⊤) :I∈J.minimalPrimes := by
 refine ⟨⟨hI,hIJ⟩,?_⟩
 intro H hH hHI
 have hmap :H.map φ≤I.map φ:=Ideal.map_mono hHI
 have hHsurv :H.map φ ≠ ⊤ := ne_top_of_le_ne_top hsurv hmap
 obtain ⟨hHprime,hHcomap⟩:=bY.prime_over H hH.1 hHsurv
 have hIcomap :=(bY.prime_over I hI hsurv).2
 have hle :J.map φ≤H.map φ:=Ideal.map_mono hH.2
 let:Hw F (Zj φ H) :=
   Module.Finite.of_surjective (z5F F hle).toLinearMap
     (Ideal.Quotient.factor_surjective hle)
 let: (H.map φ).IsPrime :=hHprime
 let:IsArtinianRing (Zj φ H) :=IsArtinianRing.of_finite F _
 have hmax : (H.map φ).IsMaximal :=
   Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
 have heq :H.map φ=I.map φ:=hmax.eq_of_le hsurv hmap
 exact ((hIcomap.symm.trans (lz (Ideal.comap φ) heq.symm)).trans hHcomap).le
theorem proof :akQ.c1 := by
 classical
 intro F _ φ k bY P Q S d hfin hd hlocal
 let:yU oq (lK F) :=φ.toAlgebra
 let:Module.Flat oq (lK F) :=bY.flat
 let J:=a07 P Q
 let:Hw F (Zj φ J) :=hfin
 let T:=S.filter fun I=>pN I k≠0
 have active (I:T) :xN (I:aU oq) :=
   (hlocal I (Finset.mem_filter.mp I.property).1).choose
 let point :T ↪ Rm Ambient :=
   ⟨fun I=>⟨I,(active I).prime⟩,fun _ _ h=>pL (lz PrimeSpectrum.asIdeal h)⟩
 have rank_eq (I:T) :G1 F (Zj φ I)=pN I k :=
   (bY.finite_rank I (active I)).2
 have length_ge (I:T) : (d:ℕ∞)≤VC (point I) J:= by
   exact (hlocal I (Finset.mem_filter.mp I.property).1).choose_spec
     (Finset.mem_filter.mp I.property).2
 have survives (I:T) : (I:aU oq).map φ ≠ ⊤ := by
   intro htop
   let:zS (Zj φ I) :=Ideal.Quotient.subsingleton_iff.mpr htop
   exact (Finset.mem_filter.mp I.property).2
     ((rank_eq I).symm.trans (z6g F _))
 have minimal (I:T) : (point I).asIdeal∈J.minimalPrimes := by
   have hle :J≤(point I).asIdeal:= by
     by_contra hn
     have h:=length_ge I
     rw [baE.b71 hn] at h
     exact hd.not_ge (ENat.natCast_le_natCast.mp (show (d:ℕ∞)≤(0:ℕ) from h))
   exact eAs bY (active I).prime hle (survives I)
 let qs :=T.attach.map point
 have hmin (q:Rm oq) (hq:q∈qs) :q.asIdeal∈J.minimalPrimes := by
   obtain ⟨I,_,rfl⟩:=Finset.mem_map.mp hq
   exact minimal I
 have hweighted:=baE.gMl
   (S:=lK F) (k :=F) J qs hmin J th
 change (∑ q∈qs,VC q J *
   qm F (Zj φ q.asIdeal))≤qm F (Zj φ J)
   at hweighted
 rw [z1C F (Zj φ J),
   show qs=T.attach.map point from rfl,Finset.sum_map] at hweighted
 have hsum: (∑ I∈T.attach,(d:ℕ∞)*(pN (I:aU oq) k :ℕ∞)) ≤
     (G1 F (Zj φ J) :ℕ∞) := by
   refine (uW fun I _ => ?_).trans hweighted
   change _≤VC (point I) J*qm F (Zj φ I)
   let:Hw F (Zj φ I) :=(bY.finite_rank I (active I)).1
   rw [z1C,rank_eq I]
   exact mul_le_mul_left (length_ge I) _
 rw [zKD T (fun I=>(d:ℕ∞)*(pN I k :ℕ∞)),
   ← ze] at hsum
 have hmass : (∑ I∈T,pN I k)=mass S k :=Finset.sum_filter_ne_zero _
 rw [← SU,hmass,← RD] at hsum
 exact ENat.natCast_le_natCast.mp hsum
end
end cy2
end
section
namespace cyo
noncomputable section
open aR dN Dr aiK aRS MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private abbrev Generator {k :ℕ} (boxes :Fin k→ ox) :=
 (i:Fin k)× pz (boxes i)
private abbrev jT {k m:ℕ} {boxes :Fin k→ ox}
  (u:Fin m ≃ Generator boxes) (j:Fin m) :Fin k →₀ ℕ :=
 Pk (u j).1 1
private abbrev aeh {k m:ℕ} {boxes :Fin k→ ox}
  (u:Fin m ≃ Generator boxes) : (Fin m →₀ ℕ) →+ (Fin k →₀ ℕ) :=
 oy (jT u)
private abbrev bFC {k m:ℕ} {boxes :Fin k→ ox}
  (u:Fin m ≃ Generator boxes) : (Fin m →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
 oy (fun j=>(u j).2.val)
private def DM {k m:ℕ} {boxes :Fin k→ ox}
  (u:Fin m ≃ Generator boxes) :nX (Fin m) c9 →ₐ[c9] GeoJets :=
 aeval (fun j=>qz (u j).2.val 1)
private abbrev dO {k m:ℕ} {boxes :Fin k→ ox}
  (u:Fin m ≃ Generator boxes) :=
 weightedHomogeneousSubmodule c9 (jT u)
private theorem deE {k m:ℕ} {boxes :Fin k→ ox}
  (u:Fin m ≃ Generator boxes) (a :Fin m →₀ ℕ) (i:Fin k) :
  aeh u a i = ∑ j∈Finset.univ.filter (fun j=>(u j).1=i),a j:= by
 rw [Fz ,Np]
 simp [ Xu,EK,LO]
private theorem bCg {k :ℕ} (boxes :Fin k→ ox) :
  pz (xl boxes (0:Fin k→ℕ))=0:= by
 simpa [xl,vi] using
  (aIH ⟨3, 3,1⟩ ⟨by decide,by decide,by decide⟩ 0).symm
private theorem dfM {k :ℕ} (boxes :Fin k→ ox) (i:Fin k) (n:ℕ) :
  xl boxes (Pk i n)=(boxes i).scale n:= by
 simp [xl,EK,vi ,ite_mul]
private theorem bOv {k :ℕ} (boxes :Fin k→ ox)
    (hb : ∀ i,vj (boxes i)) (a :Fin k →₀ ℕ) (ha :a≠0) :
    vj (xl boxes a) := by
  obtain ⟨i,hi⟩ : ∃ i,a i≠0:= by
    by_contra! h
    exact ha (Finsupp.ext h)
  refine ⟨?_,?_,?_⟩
  · change (∑ j,a j*(boxes j).j) ≤ ∑ j,a j*(boxes j).b
    exact uW (fun j _=>qU (a j) (hb j).1)
  · change 3*(∑ j,a j*(boxes j).t) ≤ ∑ j,a j*(boxes j).j
    rw [ze]
    exact uW (fun j _=> by
      rw [WK]
      exact qU _ (hb j).2.1)
  · exact (WY (Nq hi) (hb i).2.2).trans_le
      (Pc (fun j _=>In (a j*(boxes j).t))
        (vk i))
private theorem cD6 {k :ℕ} (boxes :Fin k→ ox)
   (hb : ∀ i,vj (boxes i)) (a b:Fin k →₀ ℕ) :
   pz (xl boxes (⇑(a+b:Fin k →₀ ℕ))) =
     pz (xl boxes a)+capExponents (xl boxes b) := by
 by_cases ha :a=0
 · simp [ha,bCg]
 by_cases hb' : b=0
 · simp [hb',bCg]
 rw [anN (bOv boxes hb a ha) (bOv boxes hb b hb')]
 simp [xl,J4 ,UY ,zfW]
private theorem d5g {k m:ℕ} {boxes :Fin k→ ox}
   (u:Fin m ≃ Generator boxes) (hb : ∀ i,vj (boxes i))
   (a :Fin m →₀ ℕ) :bFC u a∈pz (xl boxes (aeh u a)) := by
 induction a using FK with
 | zero=>simp [bCg]
 | add a b ha hb' =>
   rw [oY ,oY ,cD6 boxes hb (aeh u a) (aeh u b)]
   exact Set.add_mem_add ha hb'
 | single j n =>
   rw [qG,qG,zrt,
     dfM,← aIH _ (hb (u j).1)]
   exact zfk (u j).2.property
private theorem d4b {k m:ℕ} {boxes :Fin k→ ox}
    (u:Fin m ≃ Generator boxes) (hb : ∀ i,vj (boxes i)) (w:Fin k →₀ ℕ) :
    ∀ x∈pz (xl boxes w),
      ∃ a,aeh u a=w∧bFC u a=x := by
  induction w using FK with
  | zero =>
    intro x hx
    change x∈pz (xl boxes (0:Fin k→ℕ)) at hx
    rw [bCg,KH] at hx
    exact ⟨0,p6 _,(p6 _).trans hx.symm⟩
  | add v w hv hw =>
    intro x hx
    rw [cD6 boxes hb v w] at hx
    obtain ⟨y,hy,z,hz,rfl⟩:=hx
    obtain ⟨a,ha,hay⟩:=hv y hy
    obtain ⟨b,hb',hbz⟩:=hw z hz
    exact ⟨a+b,by rw [oY ,ha,hb'],by rw [oY ,hay,hbz]⟩
  | single i n =>
    simp only [dfM,← aIH _ (hb i)]
    induction n with
    | zero =>
      intro x hx
      rw [zero_smul,KH] at hx
      exact ⟨0,by simp,(p6 _).trans hx.symm⟩
    | succ n ih =>
      intro x hx
      rw [succ_nsmul] at hx
      obtain ⟨y,hy,z,hz,rfl⟩:=hx
      obtain ⟨a,ha,hay⟩:=ih y hy
      let j:=u.symm ⟨i,⟨z,hz⟩⟩
      have hj:u j=⟨i,⟨z,hz⟩⟩:=u.apply_symm_apply _
      refine ⟨a+Finsupp.single j 1,?_,?_⟩
      · rw [oY ,ha,qG,II]
        simp only [jT,hj,← Finsupp.single_add]
      · rw [oY ,hay,qG,II,hj]
private theorem dgA {k m:ℕ} {boxes :Fin k→ ox}
   (u:Fin m ≃ Generator boxes) (a :Fin m →₀ ℕ) :
   DM u (qz a 1)=qz (bFC u a) 1 := by
 induction a using FK with
 | zero=>simp
 | add a b ha hb =>
   rw [← show monomial a (1 :GeoField)*monomial b 1=monomial (a+b) 1 by simp,
     oz ,ha,hb,zDU,Qw ,oY ]
 | single j n =>
   rw [← X_pow_eq_monomial,vw ,DM,aeval_X,monomial_pow,KA,
     qG]
private theorem eLd {k m:ℕ} {boxes :Fin k→ ox}
    (u:Fin m ≃ Generator boxes) (hb : ∀ i,vj (boxes i)) (w:Fin k →₀ ℕ) :
    (dO u w).map (DM u).toLinearMap =
      yJ c9 (pz (xl boxes w)) := by
  rw [show dO u w=yJ c9 {a | aeh u a=w} from
    zSq _ _ _]
  apply wA
  · rw [Submodule.map_le_iff_le_comap,
      NI c9 {a | aeh u a=w},zKY]
    rintro _ ⟨a,ha,rfl⟩
    change DM u (qz a 1)∈yJ c9 _
    rw [dgA]
    exact (monomial_mem_restrictSupport _).mpr (Gi
      (show bFC u a∈pz (xl boxes w) from
        (show aeh u a=w from ha) ▸ d5g u hb a))
  · rw [NI,zKY]
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨a,ha,hax⟩:=d4b u hb w x hx
    exact ⟨qz a 1,(monomial_mem_restrictSupport _).mpr (Gi ha),by
      change DM u (qz a 1)= _
      rw [dgA,hax]⟩
private theorem aXV {k m:ℕ} {boxes :Fin k→ ox}
    (u:Fin m ≃ Generator boxes) (hb : ∀ i,vj (boxes i)) (P:aU n5)
    (o:FR (Fin m)) :
    ∃ I:aU (nX (Fin m) c9),∀ w:Fin k →₀ ℕ,
      G1 c9 (alz P (xl boxes w)) =
        {a | a∈o.standardExponents I∧aeh u a=w}.ncard:= by
  let J:=P.comap (DM u).toRingHom
  let I:=(J.homogeneousCore (dO u)).toIdeal
  have hIJ:I≤J:=zFP (dO u) J
  have hI:I.IsHomogeneous (dO u) :=(J.homogeneousCore (dO u)).isHomogeneous
  refine ⟨I,fun w => ?_⟩
  let mk :=(Fa c9 P).toLinearMap
  let φ:=mk.comp (DM u).toLinearMap
  let T:=alz P (xl boxes w)
  let A := {a | a∈o.standardExponents I∧aeh u a=w}
  let S:=yJ c9 A
  have hmap : (dO u w).map φ=T:= by
    change (dO u w).map (mk.comp (DM u).toLinearMap) =
      (yJ c9 (pz (xl boxes w))).map mk
    rw [z1U,eLd u hb w]
  have hST:S≤dO u w:= by
    intro f hf a ha
    exact (hf (mem_support_iff.mpr ha)).2
  let L:S →ₗ[c9] T:=(φ.domRestrict S).codRestrict T (fun f =>
    hmap ▸ Submodule.mem_map.mpr ⟨f,hST f.2,rfl⟩)
  have hinj:p9 L:= by
    intro f g hfg
    have heq :φ f=φ g:=lz C4 hfg
    have hf : (f :nX (Fin m) c9)∈dO u w:=hST f.2
    have hg: (g:nX (Fin m) c9)∈dO u w:=hST g.2
    have hsub: (f :nX (Fin m) c9) - g∈J:= by
      change mD P (DM u f)=mD P (DM u g) at heq
      change DM u ((f :nX (Fin m) c9) - g)∈P
      rw [Av]
      exact Ideal.Quotient.eq.mp heq
    apply pL
    exact o.eq_of_mem_standardSpace_of_sub_mem
      (fun a ha=>(f.2 ha).1) (fun a ha=>(g.2 ha).1)
      (zFp ⟨w,(dO u w).sub_mem hf hg⟩ hsub)
  have hsurj:vh L:= by
    intro y
    have hy :y.val∈(dO u w).map φ:= by
      rw [hmap]
      exact y.property
    obtain ⟨f,hf,hfy⟩:=Submodule.mem_map.mp hy
    obtain ⟨q,hq,hfq,_⟩:=o.exists_mem_standardSpace_sub_mem I f
    let r :=Ar (jT u) w q
    have hr :r∈S:= by
      intro a ha
      have hw:r.IsWeightedHomogeneous (jT u) w :=
        zmP w q
      refine ⟨hq ?_,hw (mem_support_iff.mp ha)⟩
      change a∈(Ar (jT u) w q).support at ha
      rw [z66] at ha
      exact (Finset.mem_filter.mp ha).1
    have hfr :f - r∈I:= by
      have hc:=MK _ _ hI hfq w
      rwa [Av,XG (show
        f.IsWeightedHomogeneous (jT u) w from hf)] at hc
    have hzero :φ (f - r)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hfr)
    rw [Av,sub_eq_zero] at hzero
    exact ⟨⟨r,hr⟩,pL (hzero.symm.trans hfy)⟩
  change G1 c9 T=A.ncard
  rw [← (zD9 L ⟨hinj,hsurj⟩).finrank_eq,
    zUF (zzc c9 A),JM]
theorem proof :aRS.c1 := by
 classical
 intro P k boxes _ hb
 let _:oK (Generator boxes) :=Gk _
 let u:=(G8 (Generator boxes)).symm
 let slot:= fun j=>(u j).1
 let o:FR (Fin (Fintype.card (Generator boxes))) :=zwf
 obtain ⟨I,hI⟩:=aXV u hb P o
 obtain ⟨bad,hbad⟩:=o.exists_finset_standardExponents_iff I
 refine ⟨_,slot,bad,fun w => ?_⟩
 let v :Fin k →₀ ℕ:=Finsupp.equivFunOnFinite.symm w
 change G1 c9 (alz P (xl boxes v))=aAp slot bad w
 rw [hI v]
 unfold aAp
 congr 1
 ext a
 simp only [Qx ,hbad]
 apply and_congr_right'
 constructor
 · intro ha i
   rw [← deE u a i,ha]
   rfl
 · intro ha
   ext i
   rw [deE]
   exact ha i
end
end cyo
end
section
namespace dnf
noncomputable section
open Polynomial MvPolynomial aR Ex dN vS aA5
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem bcO {n:ℕ} (w:Fin n→ℕ) (a :ao[X]) (P:af n) :
  W w (nq a*P)≤W w P:= by
 simpa only [weightedTotalDegree_C,Gj] using
  Eg w (nq a) P
private theorem cve {n:ℕ} (w:Fin n→ℕ) (i:Fin n) :
  W w (lV i:af n)≤w i :=
 mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  (X_mem_restrictWeightedDegree _ _ _ th)
private theorem a2J {n:ℕ} (w:Fin n→ℕ) (P:af n) :
  W w (∑ m∈P.support,qz m (derivative (P.coeff m)))≤W w P:= by
 classical
 apply Finset.sup_mono
 intro m hm
 obtain ⟨j,hj,hmj⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
 have h:j=m:= by
  by_contra hne
  exact (MvPolynomial.mem_support_iff.mp hmj)
    (by rw [MvPolynomial.coeff_monomial,C9 hne])
 exact h ▸ hj
private theorem gqc {n:ℕ} (w:Fin n→ℕ) (i j:Fin n) (P:af n)
   (δ:ℕ) (h:w j≤w i+δ) :
   W w (lV j*yQ i P)≤W w P+δ:= by
 apply X4
 intro m hm
 rw [zuk,coeff_X_mul'] at hm
 split_ifs at hm with hj
 · have hn:m-Finsupp.single j 1+Finsupp.single i 1∈P.support := by
     rw [coeff_pderiv] at hm
     exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)
   have hw:=z6P w hn
   have he :=Zg (w:=w) (Finsupp.mem_support_iff.mp hj)
   rw [oY ,qG,II] at hw
   omega
 · exact (hm rfl).elim
private theorem al0 {n:ℕ} (w:Fin (n+1)→ℕ) (δ:ℕ)
    (hshift : ∀ i:Fin n,w i.succ≤w i.castSucc+δ) (P:af (n+1))
    {d:ℕ} (hP:W w P≤d) :
    W w ((∑ m∈P.support,qz m (derivative (P.coeff m))) +
      ∑ i:Fin n,nq (lI ((i.val+1 :ℕ) :ao)) *
        lV i.succ*yQ i.castSucc P)≤d+δ:= by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Ob
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((a2J w P).trans (hP.trans (zi _ _)))
  · apply zo3
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [uh]
    exact (bcO w _ _).trans
      ((gqc w _ _ P δ (hshift i)).trans (Nat.add_le_add_right hP δ))
private theorem azs (w:Fin 5→ℕ) (P:af 4) :
  W w (T9 P)=W (w ∘ uz) P :=
 weightedTotalDegree_rename_of_injective (Fin.castSucc_injective 4)
private theorem Ur (w:Fin 5→ℕ) {g:af 4} {B:ℕ}
  (hg:W (w ∘ uz) g≤B) :
  W w (T9 (wB g))≤B - w ((3:Fin 4).castSucc) := by
 rw [azs,wB]
 exact (zYB _ _ _).trans (zIu hg _)
private theorem cUe (w:Fin 5→ℕ) (δ:ℕ)
   (hshift : ∀ i:Fin 4,w i.succ≤w i.castSucc+δ)
   {g:af 4} {B:ℕ} (hg:W (w ∘ uz) g≤B)
   (hB:w ((3:Fin 4).castSucc)≤B) :
   W w (ao6 g)≤B+δ:= by
 have hshift' (i:Fin 3) :
     (w ∘ uz) i.succ≤(w ∘ uz) i.castSucc+δ:= by
   exact hshift i.castSucc
 have hlast :w (pC 4)≤w ((3:Fin 4).castSucc)+δ:=hshift 3
 unfold ao6
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
 apply Ob
 · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
   rw [azs]
   exact al0 _ δ hshift' g hg
 · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
   rw [uh]
   exact (bcO w _ _).trans ((Eg _ _ _).trans
     ((zk (Ur w hg) (cve w _)).trans (by omega)))
private theorem Vi (w:Fin 5→ℕ) (δ:ℕ)
    (hshift : ∀ i:Fin 4,w i.succ≤w i.castSucc+δ)
    (hlast :w (pC 4)=w ((3:Fin 4).castSucc)+δ)
    {g:af 4} {B:ℕ} (hg:W (w ∘ uz) g≤B)
    (hB:w ((3:Fin 4).castSucc)≤B) (k :ℕ) :
    W w (Ee g k)≤w (pC 4)+k*(B - w ((3:Fin 4).castSucc)+δ) := by
  let s :=B - w ((3:Fin 4).castSucc)
  have hS:W w (T9 (wB g))≤ s :=Ur w hg
  have hU:W w (bp7 g)≤B+δ+δ :=
    (bcO w _ _).trans (al0 w δ hshift _ (cUe w δ hshift hg hB))
  have hDS:W w (ay1 (T9 (wB g)))≤ s+δ :=
    al0 w δ hshift _ hS
  change W w (Ee g k)≤w (pC 4)+k*(s+δ)
  induction k with
  | zero =>
    simpa only [Ee,zero_mul,G6] using
      (bcO w _ _).trans (cve w (pC 4))
  | succ k ih =>
    let d:=w (pC 4)+k*(s+δ)
    rw [Ee,Nat.succ_mul,← Nat.add_assoc]
    change W w (_+_-_)≤d+(s+δ)
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sub_mem
    · apply Ob
      · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        have hDP:W w (ay1 (Ee g k))≤d+δ:=al0 w δ hshift _ ih
        exact (Eg _ _ _).trans
          ((zk hS hDP).trans (by omega))
      · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        have hP:W w (yQ (pC 4) (Ee g k))≤k*(s+δ) := by
          simpa only [z7K] using
            (zYB w (pC 4) (Ee g k)).trans
              (zIu ih (w (pC 4)))
        have hu:B+δ+δ=w (pC 4)+(s+δ) := by
          dsimp only [s]
          omega
        exact (Eg _ _ _).trans
          ((zk hU hP).trans (by rw [hu]; dsimp only [d]; omega))
    · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      apply (Eg _ _ _).trans
      rw [← Ts (nq:ao[X] →+* af 5)]
      exact (zk ((bcO w _ _).trans hDS) ih).trans (by omega)
private theorem ZB (w:Fin 5→ℕ) {g:af 4} {B:ℕ}
   (hg:W (w ∘ uz) g≤B) (k :ℕ) :
   W w (denominator g k)≤k*(B - w ((3:Fin 4).castSucc)) :=
 (weightedTotalDegree_pow_le _ _ _).trans (qU _ (Ur w hg))
private theorem ca9 (w:Fin 5→ℕ) (δ:ℕ)
    (hshift : ∀ i:Fin 4,w i.succ≤w i.castSucc+δ)
    (hlast :w (pC 4)=w ((3:Fin 4).castSucc)+δ)
    (hw : ∀ i:Fin 4,w i.castSucc≤w (pC 4))
    {g:af 4} {B:ℕ} (hg:W (w ∘ uz) g≤B)
    (hB:w ((3:Fin 4).castSucc)≤B) (k i:ℕ) (hi:i≤k+4) :
    W w (CJ g k i)≤w (pC 4)+k*(B - w ((3:Fin 4).castSucc)+δ) := by
  let s :=B - w ((3:Fin 4).castSucc)
  change W w (CJ g k i)≤w (pC 4)+k*(s+δ)
  unfold CJ
  split_ifs with hinit
  · apply (Eg _ _ _).trans
    have hx :W w (T9 (lV ⟨i,hinit⟩))≤w (pC 4) := by
      rw [azs]
      exact (cve _ _).trans (hw ⟨i,hinit⟩)
    exact zk ((bcO w _ _).trans hx)
      ((ZB w hg k).trans (qU _ (zi _ _)))
  · let a :=i-4
    have ha :a≤k := by dsimp [a]; omega
    apply (Eg _ _ _).trans
    calc
      _≤(w (pC 4)+a*(s+δ))+(k-a)*s :=
        zk (Vi w δ hshift hlast hg hB a)
          (ZB w hg (k-a))
      _≤(w (pC 4)+a*(s+δ))+(k-a)*(s+δ) :=
        R9 (qU _ (zi _ _)) _
      _ = _:= by rw [Nat.add_assoc,← UY ,GR ha]
private theorem aJI (w:Fin 5→ℕ) (δ:ℕ)
    (hshift : ∀ i:Fin 4,w i.succ≤w i.castSucc+δ)
    (hlast :w (pC 4)=w ((3:Fin 4).castSucc)+δ)
    (hw : ∀ i:Fin 4,w i.castSucc≤w (pC 4))
    {g:af 4} {B:ℕ} (hg:W (w ∘ uz) g≤B)
    (hB:w ((3:Fin 4).castSucc)≤B) :
    W w (ao6 g)≤B+δ ∧
      ∀ k :ℕ,let d:=w (pC 4)+k*(B - w ((3:Fin 4).castSucc)+δ)
        W w (denominator g k)≤d ∧ ∀ i≤k+4,W w (CJ g k i)≤d:= by
  refine ⟨cUe w δ hshift hg hB,fun k=>⟨?_,ca9 w δ hshift hlast hw hg hB k⟩⟩
  exact (ZB w hg k).trans
    ((qU _ (zi _ _)).trans (Pv _ _))
private def topWeight:Fin 5→ℕ:=G0 2 (Pi.single (3:Fin 4) 1)
private def auY:Fin 5→ℕ:=Pi.single (pC 4) 1
end
end dnf
end
