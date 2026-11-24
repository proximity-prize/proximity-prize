import ProximityPrize.SubmissionLower.H
import ProximityPrize.SubmissionLower.I
import ProximityPrize.SubmissionLower.Z
import ProximityPrize.SubmissionLower.J
set_option Elab.async false
open _root_ renaming AlgEquiv.apply_symm_apply→Aa,AlgEquiv.ofAlgHom→zp6,Algebra→ oq,Algebra.EssFiniteType→WK,Algebra.FormallyUnramified→HZ,Algebra.IsSeparable→XB,Algebra.IsUnramifiedAt→zjp,Algebra.TensorProduct.includeRight→Ww,Algebra.TensorProduct.tensorQuotientEquiv→zTd,Algebra.algebraMap→aU,Algebra.smul_def→VH,Bool.false_eq_true→zN5,Bornology.IsBounded→zg0,CommRing→ oD,DFunLike.congr_fun→zk,Disjoint→Lf,E6.BP→xu,ENNReal.ofReal→Hw,ENNReal.ofReal_mul→zwu,ENNReal.ofReal_ne_top→Up,ENNReal.toReal_mono→LO,ENNReal.toReal_mul→zFP,ENNReal.toReal_ofReal→Mz,ENat.toNat_natCast→zzq,Field→c9,Filter.Tendsto→th,Filter.eventually_ge_atTop→Kp,Fin.castSucc→Gn,Fin.castSucc_injective→Vs,Fin.castSucc_ne_last→zm4,Fin.last→u8,Fin.ofFn_take_eq_take_ofFn→zKJ,Fin.prod_univ_succ→zNH,Fin.sum_univ_four→x7,Fin.sum_univ_succ→LR,Finite→C4,Finset→n5,Finset.card_insert_of_notMem→zwo,Finset.filter_mem_eq_inter→zuy,Finset.induction_on→Df,Finset.le_sup→Vz,Finset.mul_sum→yl,Finset.prod_const→zJD,Finset.range→Gr,Finset.single_le_sum→zfK,Finset.sum_add_distrib→vG,Finset.sum_coe_sort→zNb,Finset.sum_congr→vw
open _root_ renaming Finset.sum_filter→zLJ,Finset.sum_insert→z8,Finset.sum_le_sum→wB,Finset.sum_mul→JW,Finset.sup_congr→S2,Finset.sup_le→Ok,Finset.univ→t9,Finset.univ_inter→Zh,Finsupp.add_apply→Cy,Finsupp.cons_succ→z9p,Finsupp.finsetSum_apply→ze7,Finsupp.mapDomain_apply_of_injective→zm3,Finsupp.prod_fintype→z6B,Finsupp.single→vi,Finsupp.single_apply→Kc,Finsupp.sum_fintype→G0,Finsupp.support_add_eq→zbA,Finsupp.weight→Kv,Finsupp.weight_apply→zDM,Finsupp.weight_single→UZ,Fintype.card→JQ,Fintype.card_fin→Pf,FractionRing→qJ,Function.Injective→p7,Function.Surjective→u5,Function.comp_apply→RD,Function.comp_def→zQM,Function.iterate_succ_apply'→zLk,Function.update→N0,Function.update_of_ne→zBg,Ideal→lz,Ideal.Quotient.eq_zero_iff_mem→zc,Ideal.Quotient.factor→Av,Ideal.Quotient.factor_mk→RC,Ideal.Quotient.factorₐ→z5F,Ideal.Quotient.mk→lV,Ideal.Quotient.mk_algebraMap→zOY,Ideal.Quotient.mk_surjective→uh,Ideal.Quotient.mkₐ→F9,Ideal.comap_map_of_surjective→SW,Ideal.comap_radical→zBJ,Ideal.exists_pow_le_of_le_radical_of_fg→zK9,Ideal.map_isMaximal_of_equiv→zfh,Ideal.map_map→zR,Ideal.map_mono→Pj,Ideal.map_pow→ Iw,Ideal.map_span→uJ,Ideal.map_sup→ II
open _root_ renaming Ideal.mem_map_of_mem→zf,Ideal.mem_span_singleton→QL,Ideal.mem_span_singleton_self→z5J,Ideal.mul_mono_right→zMu,Ideal.mul_top→G2,Ideal.ofList→zh,Ideal.pow_le_pow_right→zdr,Ideal.pow_mem_pow→Zt,Ideal.quotEquivOfEq→zC3,Ideal.quotientEquivAlg→zpY,Ideal.quotientEquivAlgOfEq→z9k,Ideal.quotientMap_injective→zmq,Ideal.radical_minimalPrimes→VS,Ideal.smul_eq_mul→G5,Ideal.span→ ov,Ideal.span_singleton_le_iff_mem→Qx,Ideal.span_singleton_mul_span_singleton→z9C,Ideal.subset_span→Dz,Insert.insert→EP,IntermediateField.adjoin→zvb,IsDomain→zE,IsFractionRing.injective→KA,IsFractionRing.lift→zIj,IsFractionRing.lift_algebraMap→zoc,IsIntegral.of_finite→zh6,IsLocalRing.ResidueField→FR,IsLocalRing.maximalIdeal→qz,IsLocalization→G9,IsLocalization.AtPrime.equivQuotMaximalIdeal→zx7,IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes→GR,IsLocalization.AtPrime.to_map_mem_maximal_iff→Nq,IsLocalization.algebraMap_mem_map_algebraMap_iff→zi,IsLocalization.flat→zsF,IsLocalization.map_units→Ze,IsNoetherian.noetherian→Te,IsScalarTower.algebraMap_apply→Ee,IsScalarTower.of_algebraMap_eq→zsL,IsScalarTower.toAlgHom→zE2,IsUnit→wR,LinearIndependent→z7,LinearMap.baseChange_eq_ltensor→Np,LinearMap.ker→Sd,LinearMap.mem_ker→zeS,LinearMap.mulLeft→Yc,List.Forall₂→Ye,List.getElem_ofFn→Z0,List.mem_ofFn'→UP
open _root_ renaming List.ofFn→sH,Localization.AtPrime→ oY,Localization.AtPrime.map_eq_maximalIdeal→ Il,Localization.AtPrime.under_maximalIdeal→zUp,Localization.Away→qx,Matrix.cons_val_zero→zbs,Matrix.toLin'→KH,Matrix.toLin'_apply→Xu,MeasureTheory.MeasureSpace.volume→ oj,MeasureTheory.measure_mono→Bf,MeasureTheory.measure_ne_top_of_subset→Xo,Metric.cthickening→KI,Module.Finite→ oz,Module.Finite.of_surjective→Ar,Module.Flat→WX,Module.Flat.lTensor_preserves_injective_linearMap→zc1,Module.finrank→pG,Module.length→Au,Module.length_eq_finrank→Zg,Module.length_eq_of_surjective→zAi,MulZeroClass.mul_zero→vj,MvPolynomial→cy,MvPolynomial.C→pQ,MvPolynomial.C_mul_monomial→Wl,MvPolynomial.X→lI,MvPolynomial.aeval→ oZ,MvPolynomial.affineDegree→u9,MvPolynomial.affineDegree_nonneg→zcN,MvPolynomial.affineHilbertFunction→Xp,MvPolynomial.affineHilbertPolynomial→G7,MvPolynomial.algHom_ext→Kh,MvPolynomial.algebraMap_eq→Mw,MvPolynomial.algebraTensorAlgEquiv→zoR,MvPolynomial.coeff_monomial→Yi,MvPolynomial.coeff_mul_X'→Yo,MvPolynomial.degreeOf_eq_sup→ IT,MvPolynomial.eval→xI,MvPolynomial.eval₂Hom→Et,MvPolynomial.eval₂Hom_C→UY,MvPolynomial.eval₂Hom_X'→Pv,MvPolynomial.exists_eval_affineHilbertPolynomial→zQf,MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus→zwb,MvPolynomial.finSuccEquiv→p5,MvPolynomial.finSuccEquiv_X_succ→Gk,MvPolynomial.finSuccEquiv_X_zero→TI,MvPolynomial.finSuccEquiv_apply→X4,MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree→Zi,MvPolynomial.homogeneousComponent→y5
open _root_ renaming MvPolynomial.homogeneousComponent_isHomogeneous→GY,MvPolynomial.homogeneousComponent_of_mem→SU,MvPolynomial.induction_on→LP,MvPolynomial.isLocalization→zEY,MvPolynomial.le_weightedTotalDegree→GF,MvPolynomial.map→ oy,MvPolynomial.map_injective→zNV,MvPolynomial.mem_support_coeff_finSuccEquiv→zjq,MvPolynomial.mk_mem_quotientDegreeLE→Pk,MvPolynomial.monomial→Kz,MvPolynomial.pderiv→qy,MvPolynomial.pderiv_mul→zg,MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one→zdH,MvPolynomial.principalCut_sum_affineDegree_retainedMinimalPrimes_le→zcE,MvPolynomial.quotientDegreeLE→z9,MvPolynomial.rename→G6,MvPolynomial.renameEquiv→Ml,MvPolynomial.ringHom_ext→t8,MvPolynomial.sumAlgEquiv→ZK,MvPolynomial.totalDegree_mul_of_isDomain→zzD,MvPolynomial.weightedTotalDegree→vh,MvPolynomial.weightedTotalDegree_mul→Pr,MvPolynomial.weightedTotalDegree_mul_le→FU,MvPolynomial.weightedTotalDegree_pderiv_le_sub→Fa,MvPolynomial.weightedTotalDegree_piSingle→z5e,MvPolynomial.zeroLocus→yJ,Nat.add_assoc→Vq,Nat.add_le_add→wA,Nat.add_mul→Ts,Nat.cast_add→GB,Nat.cast_mul→zd,Nat.cast_nonneg→zm,Nat.cast_ofNat→C9,Nat.cast_one→RP,Nat.cast_sub→zjK,Nat.cast_sum→SL,Nat.eq_zero_of_le_zero→Ob,Nat.floor_eq_on_Ico→zrg,Nat.floor_le→Sv,Nat.lt_floor_add_one→Rm,Nat.mul_add→Qy,Nat.mul_le_mul_left→SD,Nat.mul_le_mul_right→P7,Nat.pos_of_ne_zero→zOl,Nat.strong_induction_on→Zf,Nat.sub_add_cancel→zxt,Nat.sub_le_sub_right→G8,Pi.add_apply→TZ
open _root_ renaming Pi.smul_apply→Mj,Polynomial→nX,Polynomial.Bivariate.swap→Dv,Polynomial.Bivariate.swap_X→zPy,Polynomial.C→lJ,Polynomial.C_mul→MS,Polynomial.X→mD,Polynomial.X_mul_divX_add→zQv,Polynomial.aeval→Ea,Polynomial.aeval_C→SC,Polynomial.aeval_X→Xx,Polynomial.algebraMap_apply→WY,Polynomial.algebraMap_eq→zrE,Polynomial.coe_mapRingHom→zKC,Polynomial.coeff_C_mul_X→z8l,Polynomial.coeff_map→Y4,Polynomial.coeff_sub→PM,Polynomial.coeff_zero_eq_eval_zero→zTt,Polynomial.derivative→pL,Polynomial.derivative_mul→G1,Polynomial.evalRingHom→yQ,Polynomial.eval_C→zFf,Polynomial.hasseDeriv→v9,Polynomial.mapRingHom→xL,Polynomial.map_C→PA,Polynomial.map_add→zS4,Polynomial.map_injective→NW,Polynomial.map_map→zoi,Polynomial.map_mul→TH,Polynomial.map_one→zP0,RatFunc→pC,RatFunc.C→t4,RatFunc.X→Gi,Real.volume_Icc_pi→zk7,Real.volume_pi_Ico→zEj,RingHom.comap_ker→zEW,RingHom.comp_apply→EK,RingHom.comp_assoc→XG,RingHom.congr_fun→Ef,RingHom.ext→X8,RingHom.ker→sS,RingHom.ker_comp_of_injective→zGm,RingHom.ker_eq_comap_bot→Un,RingHom.ker_isMaximal_of_surjective→VC,RingHom.ker_isPrime→Pc,RingHom.mem_ker→Xg,RingHom.quotientKerEquivOfSurjective→zJi,RingTheory.Sequence.IsWeaklyRegular→FV
open _root_ renaming Set.Finite.mem_toFinset→zih,Set.add_mem_add→NX,Set.finsetSum_mem_finsetSum→zlD,Set.image_congr→S1,Set.image_singleton→Gj,Set.mem_univ→Mk,Set.ncard_coe_finset→Du,Set.ncard_le_ncard→SM,Set.nsmul_mem_nsmul→zfk,Set.range→vk,Set.range_comp→RJ,Squarefree→Vl,Submodule→Kl,Submodule.add_mem→zcy,Submodule.sub_mem→MK,Subtype.ext→vH,Subtype.val→Re,Sum.elim→G3,Tx.Supported→LQ,UniqueFactorizationMonoid→zsh,VG.Exponent→t5,XU.pointPrime→yo,aR.Shape→nI,aR.Shape.plus→yL,aR.Shape.scale→p9,ac0.projection→VO,add_le_add_right→JK,add_nsmul→NY,add_sub_cancel_left→zYK,add_zero→zS,charP_of_injective_ringHom→OJ,congrArg→ ox,congrFun→Nr,convex_convexHull→zvj,dN.GeoField→p6,dN.GeoJets→t3,dN.separant→ oK,div_eq_mul_inv→PD,div_le_div_of_nonneg_right→zrZ,dvd_mul_right→Qw,eventually_mem_nhdsWithin→MO,gT.Ambient→qU,inferInstance→xm,isSMulRegular_quotient_iff_mem_of_smul_mem→zHO,isUnit_of_dvd_unit→zNU,ite_eq_left→ IU,ite_eq_right→Eg,le_antisymm→wY
open _root_ renaming le_rfl→vZ,le_sup_left→Nj,lt_div_iff₀→WD,map_add→qG,map_mul→nq,map_natCast→G4,map_pow→xW,map_sub→uz,map_sum→sI,map_zero→qm,measurableSet_Ico→zQD,measurable_pi_apply→zk2,mem_of_isSMulRegular_quotient_of_smul_mem→zXB,min_eq_left→Wm,minpoly.isIntegrallyClosed_dvd→zPo,mul_add→ In,mul_assoc→pU,mul_comm→t6,mul_le_mul_of_nonneg_left→t7,mul_left_comm→JM,mul_nonneg→ze,nhdsWithin_le_nhds→Dw,nonZeroDivisors→FQ,not_lt_of_ge→XJ,nsmul_eq_mul→NZ,one_mul→yU,pow_ne_zero→J4,pow_succ→C5,pow_succ'→FK,reduceIte→Fz,smul_eq_mul→v8,sub_zero→NI,subset_convexHull→WW,sup_bot_eq→Oc,tendsto_const_div_atTop_nhds_zero_nat→ZJ,yz.aa1→vl,zP.Exponent→pz,zP.corner→uW,zP.ke→qM,zero_add→yB,zero_le_one→R9
set_option autoImplicit true
section
namespace cx6
noncomputable section
open aR B7 Ey axc ML
open scoped TensorProduct nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
private abbrev al1 :jo →+* mK :=
 oy (aU ao dF)
private def Pd (I:lz jo) :
  dF ⊗[ao] (jo ⧸ I) ≃ₐ[dF] mK ⧸ oV I:= by
 let e :=zoR (σ:=rS) ao dF
 let ι:jo →ₐ[ao] dF ⊗[ao] jo :=
  Ww
 have hcomp:e.toRingHom.comp ι.toRingHom=al1 := by
  apply X8
  intro p
  change e (1 ⊗ₜ[ao] p)= _
  simp [e]
 refine (zTd (R:=ao) dF _ dF I).trans
  (zpY _ _ e ?_)
 exact ((zR (I:=I) ι.toRingHom e.toRingHom).trans
  (ox (fun f=>I.map f) hcomp)).symm
private theorem eQv (I:lz jo) (p:jo) :
  Pd I (1 ⊗ₜ[ao] (lV I p)) =
   lV (oV I) (al1 p) := by
 simp [Pd]
private theorem ed1 (I:lz jo) (f :jo) :
  oV (ahw I f)=ahw (oV I) (al1 f) := by
 simp [oV,ahw,II,uJ]
private theorem ed0 (I:lz jo) (f :jo) :
    oV (VW I f)=VW (oV I) (al1 f) := by
  let A:=VW I f
  have hA : ∀ x :jo,x*f∈I↔x∈A :=
    fun _ ↦ arO.symm
  have hmul :oV A≤VW (oV I) (al1 f) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change al1 x∈VW (oV I) (al1 f)
    rw [arO,← nq]
    exact zf al1 ((hA x).mpr hx)
  let u: (mK ⧸ oV A) →ₗ[dF] mK ⧸ oV I :=
    ((oV A).restrictScalars dF).liftQ
      ((F9 dF (oV I)).toLinearMap ∘ₗ
        Yc dF (al1 f)) (fun x hx ↦ by
          change lV (oV I) (al1 f*x)=0
          rw [zc,t6]
          exact arO.mp (hmul hx))
  let v :=afC (k :=ao) hA
  have hv :p7 (v.baseChange dF) := by
    rw [Np]
    exact zc1 v (aUw hA)
  have hcompare (z :dF ⊗[ao] (jo ⧸ A)) :
      u (Pd A z)=Pd I (v.baseChange dF z) := by
    induction z using TensorProduct.inductionOn with
    | tmul c q =>
      obtain ⟨p,rfl⟩:=uh q
      rw [show c ⊗ₜ[ao] lV A p =
        c•(1 ⊗ₜ[ao] lV A p) by rw [TensorProduct.smul_tmul',v8 ,mul_one]]
      simp only [map_smul,eQv,LinearMap.baseChange_tmul,v,aNH]
      congr 1
      change lV (oV I) (al1 f*al1 p) =
        lV (oV I) (al1 (f*p))
      rw [nq al1]
    | add z w hz hw=>simp only [map_add,hz,hw]
  have hu:p7 u:= by
    intro x y hxy
    obtain ⟨z,rfl⟩:=(Pd A).surjective x
    obtain ⟨w,rfl⟩:=(Pd A).surjective y
    rw [hcompare,hcompare] at hxy
    exact ox (Pd A) (hv ((Pd I).injective hxy))
  refine wY hmul fun x hx ↦ ?_
  apply (zc (I:=oV A)).mp
  apply hu
  rw [qm]
  change lV (oV I) (al1 f*x)=0
  rw [zc,t6]
  exact arO.mp hx
set_option maxHeartbeats 1200000 in
private theorem efw (L:Fin 2→nW) (J:lz mK)
    (a :mK) (hfinite :oz MY (ay5 L J)) :
    oz MY (ay5 L (ahw J a)) ∧
      adI L J =
        adI L (ahw J a) +
          adI L (VW J a) := by
  let quotientModule (T:lz mK) :Module l5 (mK ⧸ T) :=
    Module.compHom (mK ⧸ T) (aWi L T).toRingHom
  let Q:=VW J a
  let T:=ahw J a
  have hA : ∀ x :mK,x*a∈J↔x∈Q :=
    fun _ ↦ arO.symm
  have hle :J≤T:=bIl J a
  let u: (mK ⧸ Q) →ₗ[l5] mK ⧸ J :=
    { (afC (k :=dF) hA).toAddMonoidHom with
      map_smul' := fun r x ↦ by
        obtain ⟨p,rfl⟩:=uh x
        let b:=tO (oZ L r)
        change lV J (a*(b*p)) =
          lV J (b*(a*p))
        rw [JM a b] }
  let v : (mK ⧸ J) →ₗ[l5] mK ⧸ T :=
    { (Av hle).toAddMonoidHom with
      map_smul' := fun r x ↦ by
        let b:=tO (oZ L r)
        change Av hle (lV J b*x) =
          lV T b* Av hle x
        rw [nq,RC] }
  have hu:p7 u:=aUw (k :=dF) hA
  have hv :u5 v :=Ideal.Quotient.factor_surjective hle
  have huv :Function.Exact u v :=bFP (k :=dF) hA
  let:WX l5 MY :=
    zsF MY (FQ l5)
  let u' := u.baseChange MY
  let v' := v.baseChange MY
  have hu' : p7 u' := by
    dsimp only [u']
    rw [Np]
    exact zc1 u hu
  have hv' : u5 v' := LinearMap.baseChange_surjective MY hv
  have huv' : Function.Exact u' v' := by
    dsimp only [u',v']
    rw [Np,Np]
    exact Module.Flat.lTensor_exact MY huv
  let:oz MY (ay5 L J) :=hfinite
  let:oz MY (ay5 L Q) :=Module.Finite.of_injective u' hu'
  let hT:oz MY (ay5 L T) :=Ar v' hv'
  refine ⟨hT,?_⟩
  have h:=Module.length_eq_add_of_exact u' v' hu' hv' huv'
  simpa only [Zg ,← ENat.natCast_add,ENat.natCast_inj,adI] using h.trans (add_comm _ _)
theorem proof :axc.c2 := by
  intro I f L hfinite
  let P (J Q:lz mK) :Prop :=
    oz MY (ay5 L J) ∧
      adI L (oV I) =
        adI L J+adI L Q
  change P (oV (ahw I f)) (oV (VW I f))
  rw [ed1,ed0]
  exact efw L (oV I) (al1 f) hfinite
end
end cx6
end
section
namespace cx5
noncomputable section
open MvPolynomial axc
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type*} [c9 k]
private theorem dz7 {I:lz (cy σ k)} {f p:cy σ k}
    {d N :ℕ} (hI:I.IsHomogeneous (homogeneousSubmodule σ k)) (hf :f.IsHomogeneous d)
    (hdN :d≤N) (hp:p.totalDegree≤N) (hpJ:p∈ahw I f) :
    ∃ q:cy σ k,q.totalDegree≤N - d ∧
      lV I (f*q)=lV I p:= by
  change p∈I ⊔ ov {f} at hpJ
  rw [sup_comm,Ideal.mem_span_singleton_sup] at hpJ
  obtain ⟨a,b,hb,heq⟩:=hpJ
  let q := ∑ i∈Gr (N - d+1),y5 i a
  have hq:q.totalDegree≤N - d:= by
    refine (totalDegree_finsetSum _ _).trans (Ok fun i hi ↦ ?_)
    exact (GY i a).totalDegree_le.trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hq_component (e :ℕ) (he :e≤N - d) :
      y5 e q=y5 e a := by
    simp only [q,sI,SU (GY _ _)]
    rw [Finset.sum_eq_single_of_mem e (Finset.mem_range.mpr (Nat.lt_succ_of_le he))]
    · rw [IU rfl]
    · intro i _ hi
      exact Eg (Ne.symm hi)
  have hqf : (q*f).totalDegree≤N :=
    (totalDegree_mul _ _).trans (by have :=hf.totalDegree_le; omega)
  have hdiff :p - q*f∈I:= by
    apply (mem_iff_homogeneousComponent_mem hI _).mpr
    intro e
    rw [uz]
    by_cases he :e≤N
    · rw [← heq,qG,YT.a2Q (p:=a) hf,
        YT.a2Q (p:=q) hf]
      have hb' := homogeneousComponent_mem_of_mem hI hb e
      by_cases hd:d≤e
      · simpa only [IU hd,hq_component (e - d) (by omega),zYK] using hb'
      · simpa only [Eg hd,yB,NI] using hb'
    · rw [homogeneousComponent_eq_zero _ _ (by omega :p.totalDegree<e),
        homogeneousComponent_eq_zero _ _ (by omega : (q*f).totalDegree<e),NI ]
      exact I.zero_mem
  refine ⟨q,hq,?_⟩
  have h:=Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
  rw [uz ,sub_eq_zero] at h
  simpa only [t6 q f] using h.symm
private theorem em0 [C4 σ]
    {I:lz (cy σ k)} {f :cy σ k} {d N :ℕ}
    (hI:I.IsHomogeneous (homogeneousSubmodule σ k)) (hf :f.IsHomogeneous d) (hdN :d≤N) :
    Xp I N =
      Xp (ahw I f) N +
        Xp (VW I f) (N - d) := by
  let J:=ahw I f
  let Q:=VW I f
  have hIJ:I≤J:=bIl I f
  have hann (x :cy σ k) :x*f∈I↔x∈Q :=
    arO.symm
  let π:=((z5F k hIJ).toLinearMap.domRestrict (z9 I N)).codRestrict
    (z9 J N) fun x ↦ by
      obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp x.property
      change Av hIJ x∈z9 J N
      rw [← hpx,RC]
      exact Pk hp
  have hπ:u5 π:= by
    intro y
    obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
    exact ⟨⟨lV I p,Pk hp⟩,vH hpy⟩
  let μ:=((ML.afC (k :=k) hann).domRestrict
    (z9 Q (N - d))).codRestrict (z9 I N) fun x ↦ by
      obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp x.property
      change ML.afC hann x∈z9 I N
      rw [← hpx,ML.aNH]
      exact Pk
        ((totalDegree_mul f p).trans (by have :=hf.totalDegree_le; omega))
  have hker : ∀ x,μ x∈Sd π:= by
    intro x
    rw [zeS]
    apply vH
    change Av hIJ (ML.afC (k :=k) hann x)=0
    exact (ML.bFP (k :=k) hann _).mpr ⟨x,rfl⟩
  let μker :=μ.codRestrict (Sd π) hker
  have hμinj:p7 μker := fun x y hxy ↦
    vH (ML.aUw hann
      (ox (fun z ↦ (z.val.val :MvPolynomial σ k ⧸ I)) hxy))
  have hμsurj:u5 μker := by
    intro z
    obtain ⟨p,hp,hpz⟩:=mem_quotientDegreeLE.mp z.val.property
    have hpJ:p∈J:= by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← RC hIJ,hpz]
      exact ox (fun x :z9 J N ↦ x.val) (LinearMap.mem_ker.mp z.property)
    obtain ⟨q,hq,hqp⟩:=dz7 hI hf hdN hp hpJ
    refine ⟨⟨lV Q q,Pk hq⟩,?_⟩
    apply vH
    apply vH
    change ML.afC (k :=k) hann (lV Q q)=z.val.val
    rw [ML.aNH,hqp,hpz]
  have hdim:=(LinearEquiv.ofBijective μker ⟨hμinj,hμsurj⟩).finrank_eq
  have hrank :=π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ,finrank_top,← hdim] at hrank
  exact hrank.symm
theorem proof :axc.c1 := by
 intro I f d hI hf _ _
 obtain ⟨TJ,hTJ⟩:=zQf (ahw I f)
 obtain ⟨TQ,hTQ⟩:=zQf (VW I f)
 symm
 apply eq_affineHilbertPolynomial_of_eval_eq (N₀:=max TJ (TQ+d))
 intro N hN
 have hTQd:=le_of_max_le_right hN
 have hdN :d≤N := by omega
 rw [Polynomial.eval_add,Polynomial.taylor_eval,← sub_eq_add_neg,← zjK hdN,
  hTJ N (le_of_max_le_left hN),hTQ (N - d) (by omega),
  em0 hI hf hdN,GB]
end
end cx5
end
section
namespace cx1
noncomputable section
open aR Pw
open scoped Polynomial
attribute [local instance] Polynomial.algebra in
private theorem ewi {A:Type} [oD A] [zE A]
    {I:Type} [C4 I] (g:I→(qJ A)[X]) :
    ∃ (a :A) (l:qx a →+* qJ A),
      a≠0∧p7 l ∧
      l.comp (aU A (qx a))=aU A (qJ A) ∧
      ∃ q:I→(qx a)[X],∀ i,(q i).map l=g i:= by
  classical
  let F:=qJ A
  let M:=FQ A
  let _:G9 (M.map (lJ:A →+* A[X])) F[X] :=
    Polynomial.isLocalization M F
  obtain ⟨⟨_,a,ha,rfl⟩,hclear⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (M.map (lJ:A →+* A[X])) g
  have ha0:=nonZeroDivisors.ne_zero ha
  let b:A →+* F:=aU A F
  have hb:p7 b:=KA A F
  have hunit :wR (b a) :=isUnit_iff_ne_zero.mpr (by
    simpa only [qm] using hb.ne ha0)
  let l:qx a →+* F:=IsLocalization.Away.lift a hunit
  have hl:l.comp (aU A (qx a))=b :=
    IsLocalization.Away.lift_comp a hunit
  have hlinj:p7 l:= by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers a) l]
    intro x y
    change aU A (qx a) x=aU A (qx a) y ↔
      (l.comp (aU A (qx a))) x =
        (l.comp (aU A (qx a))) y
    rw [hl,hb.eq_iff,
      (IsLocalization.injective (qx a)
        (powers_le_nonZeroDivisors_of_noZeroDivisors ha0)).eq_iff]
  let z :qx a :=IsLocalization.Away.invSelf a
  have hza :l z*b a=1 := by
    have h:=ox l (IsLocalization.Away.mul_invSelf (S:=qx a) a)
    rw [nq,map_one] at h
    rwa [t6,show l (aU A (qx a) a)=b a from
      zk hl a] at h
  refine ⟨a,l,ha0,hlinj,hl,?_⟩
  have hpre (i:I) : ∃ q: (qx a)[X],q.map l=g i:= by
    obtain ⟨r,hr⟩:=hclear i
    rw [VH] at hr
    change r.map b=((lJ a).map b)*g i at hr
    refine ⟨lJ z*r.map (aU A (qx a)),?_⟩
    rw [TH,PA,zoi,hl,hr,
      PA,← pU,← MS ,hza,Polynomial.C_1,yU]
  choose q hq using hpre
  exact ⟨q,hq⟩
private theorem descend {A:Type} [oD A] [zE A] {f :A[X]}
   (s :Factorization (f.map (aU A (qJ A)))) :
   ∃ a :A,a≠0 ∧
     Nonempty (Factorization (f.map (aU A (qx a)))) := by
 classical
 let F:=qJ A
 let I:=Fin s.n
 let J := {ij:I×I // ij.1≠ij.2} ⊕ I
 let left:J→ I:=G3 (fun ij=>ij.val.1) id
 let right:J→F[X] :=G3 (fun ij=>s.factor ij.val.2)
   (fun i=>(s.factor i).derivative)
 have hbez (j:J) : ∃ u v :F[X],u*s.factor (left j)+v*right j=1 := by
   cases j with
   | inl ij=>exact s.pairwise_coprime ij.property
   | inr i=>exact s.derivative_coprime i
 choose u v huv using hbez
 let g:I ⊕ (J ⊕ J)→F[X] :=G3 s.factor (G3 u v)
 obtain ⟨a,l,ha,hl,hcomp,lift,hlift⟩:=ewi g
 let q (i:I) :=lift (Sum.inl i)
 let U (j:J) :=lift (Sum.inr (Sum.inl j))
 let V (j:J) :=lift (Sum.inr (Sum.inr j))
 have hq (i:I) : (q i).map l=s.factor i:=hlift _
 have hU (j:J) : (U j).map l=u j:=hlift _
 have hV (j:J) : (V j).map l=v j:=hlift _
 refine ⟨a,ha,⟨{
   n:=s.n
   factor :=q
   multiplicity :=s.multiplicity
   product_eq := ?_
   monic:= fun i=>Polynomial.monic_of_injective hl (by rw [hq i]; exact s.monic i)
   multiplicity_bounds :=s.multiplicity_bounds
   pairwise_coprime := ?_
   derivative_coprime := ?_ }⟩⟩
 · apply NW l hl
   rw [zoi,hcomp]
   simpa only [Polynomial.map_prod,Polynomial.map_pow,hq] using s.product_eq
 · intro i k hik
   let j:J:=Sum.inl ⟨(i,k),hik⟩
   have hj:u j*s.factor i+v j*s.factor k=1 :=huv j
   refine ⟨U j,V j,NW l hl ?_⟩
   simpa only [zS4,TH,zP0,hq,hU,hV] using hj
 · intro i
   let j:J:=Sum.inr i
   have hj:u j*s.factor i+v j*(s.factor i).derivative=1 :=huv j
   refine ⟨U j,V j,NW l hl ?_⟩
   simpa only [zS4,TH,zP0,
     ← Polynomial.derivative_map,hq,hU,hV] using hj
theorem proof :Pw.c2 := by
 intro A _ _ _ f hf hd
 let F:=qJ A
 let b:A →+* F:=aU A F
 let geomToFrac:=b.comp (aU ao A)
 let _:CharP ao K1.p:=OJ embed.injective K1.p
 let _:CharP F K1.p:=OJ geomToFrac.injective K1.p
 have hdeg: (f.map b).natDegree≤133671 :=Polynomial.natDegree_map_le.trans hd
 let s :=E7.bFT (p:=K1.p) (hf.map b)
  (hdeg.trans_lt (by decide)) (by decide)
 apply descend (f :=f)
 exact {
  n:=s.count
  factor :=s.factor
  multiplicity :=s.multiplicity
  product_eq :=s.product_eq
  monic:=s.monic
  multiplicity_bounds := fun i=>⟨s.positive i,(s.le_degree i).trans hdeg⟩
  pairwise_coprime := fun _ _ hij=>s.coprime _ _ hij
  derivative_coprime :=s.separable }
end
end cx1
end
section
namespace ban
noncomputable section
open B7 Ey Pw MvPolynomial
open scoped Polynomial
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000
private theorem ew0 {k :Type} [c9 k]
  (e :cy (Fin 3) k ≃ₐ[k] cy (Fin 3) k)
  (he : ∀ i,(e (lI i)).IsHomogeneous 1) (f :cy (Fin 3) k) (n:ℕ) :
  y5 n (e f)=e (y5 n f) := by
 conv_lhs=>rw [← sum_homogeneousComponent (φ:=f),sI,sI]
 conv_rhs=>rw [← sum_homogeneousComponent (φ:=f),sI,sI]
 refine vw rfl fun i _ => ?_
 rw [SU
  (cYf e he (GY i f)),
  SU (homogeneousComponent_mem i f)]
 split_ifs <;> simp
private theorem aOf {k :Type} [c9 k]
    (I:lz (cy (Fin 3) k)) [I.IsPrime]
    (hI : ∀ {p},p∈I → ∀ n,y5 n p∈I)
    (L:Fin 2→cy (Fin 3) k) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hf : ((F9 k I).comp (oZ L)).Finite)
    (hi:p7 ((F9 k I).comp (oZ L))) :
    ∃ p:cy (Fin 3) k,p≠0∧I=ov {p} ∧
      p.totalDegree=aOH (R:=cy (Fin 2) k) (S:=cy (Fin 3) k ⧸ I)
        ((F9 k I).comp (oZ L)).toRingHom:= by
  classical
  let J:=cy (Fin 3) k
  let R:=cy (Fin 2) k
  let Q:=J ⧸ I
  let mk :J →ₐ[k] Q:=F9 k I
  let g:R →ₐ[k] Q:=mk.comp (oZ L)
  let a :oq R Q:=g.toRingHom.toAlgebra
  letI:oq R Q:=a
  letI:SMul R Q:=a.toSMul
  letI:Module R Q:=a.toModule
  haveI:oz R Q:=hf
  haveI:FaithfulSMul R Q:=(faithfulSMul_iff_algebraMap_injective R Q).mpr hi
  haveI:IsScalarTower k R Q :=
    zsL (fun r=>(g.commutes r).symm)
  obtain ⟨e,heL,he⟩:=d4o L hL (fun a b hab =>
    hi (ox mk hab))
  let F:J ≃ₐ[k] R[X] :=p5 k 2
  let z :Q:=mk (e (lI 0))
  let θ:R[X] →ₐ[R] Q:=Ea z
  have hθ: (θ.restrictScalars k).comp F.toAlgHom=mk.comp e.toAlgHom:= by
    apply Kh
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change θ (p5 k 2 (lI 0))=z
      rw [TI]
      exact Xx z
    · change θ (p5 k 2 (lI j.succ))=mk (e (lI j.succ))
      rw [Gk,heL]
      change Ea z (lJ (lI j))=mk (L j)
      rw [SC]
      change g (lI j)=mk (L j)
      exact ox mk (MvPolynomial.aeval_X L j)
  have happly (p:J) :θ (F p)=mk (e p) :=zk hθ p
  have hmem (p:J) :θ (F p)=0↔e p∈I:= by
    rw [happly]
    exact zc
  have hsurj:u5 θ:= by
    intro x
    have hmks :u5 mk :=uh
    obtain ⟨y,hy⟩:=hmks x
    refine ⟨F (e.symm y),?_⟩
    simpa only [happly,Aa] using hy
  let P:=minpoly R z
  have hInt:IsIntegral R z :=zh6 R z
  have hP:P.Monic:=minpoly.monic hInt
  have hker :sS θ.toRingHom=ov {P} := minpoly.ker_eval hInt
  let p:=F.symm P
  have hp:p≠0:= by
    intro h
    apply hP.ne_zero
    simpa only [p,Aa ,qm] using ox F h
  have hpI:e p∈I:=(hmem p).mp (by
    simpa only [p,Aa] using minpoly.aeval R z)
  have hgen:I=ov {e p} := by
    apply wY
    · intro f hf
      have hf' : θ (F (e.symm f))=0:=(hmem _).mpr (by simpa using hf)
      obtain ⟨t,ht⟩:=zPo hInt hf'
      refine Ideal.mem_span_singleton.mpr ⟨e (F.symm t),?_⟩
      calc
        f=e (F.symm (F (e.symm f))) := by simp
        _=e (F.symm (P*t)) := by rw [ht]
        _=e p*e (F.symm t) := by simp only [p,nq]
    · exact (Qx I).mpr hpI
  let n:=P.natDegree
  let p' := y5 n p
  have hp'I:e p' ∈ I:= by
    rw [show e p' = y5 n (e p) from (ew0 e he p n).symm]
    exact hI hpI n
  have hlead: (F p').coeff n = 1 := by
    have hcoeff : (F p).coeff n = 1 := by
      simpa only [p,Aa] using hP.coeff_natDegree
    ext a
    change ((p5 k 2 p').coeff n).coeff a=(1 :R).coeff a
    rw [finSuccEquiv_coeff_coeff,show p' = y5 n p from rfl,
      coeff_homogeneousComponent,← finSuccEquiv_coeff_coeff,show
        p5 k 2 p=F p from rfl,hcoeff]
    by_cases ha :a=0
    · subst a
      simp [Finsupp.cons_zero_eq_single_zero]
    · simp [coeff_one,Ne.symm ha]
  have hdeg: (F p').natDegree≤n:= by
    change (p5 k 2 p').natDegree≤n
    rw [natDegree_finSuccEquiv]
    exact (degreeOf_le_totalDegree _ _).trans (GY n p).totalDegree_le
  have hP' : (F p').Monic:=Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdeg hlead
  have hdvd:P∣F p' := zPo hInt ((hmem p').mpr hp'I)
  have hpp:p' = p:=F.injective <| by
    rw [show F p=P from F.apply_symm_apply P]
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hP hP' hdvd hdeg
  have hhom:p.IsHomogeneous n:=hpp ▸ GY n p
  have hep:e p≠0:= by
    intro h
    apply hp
    apply e.injective
    rw [h,qm]
  have ht: (e p).totalDegree=n :=
    (cYf e he hhom).totalDegree hep
  let E :AdjoinRoot P ≃ₐ[R] Q :=
    (z9k R hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  have hr :aOH (R:=R) (S:= Q) g.toRingHom=n :=
    E.symm.toLinearEquiv.finrank_eq.trans (AdjoinRoot.powerBasis' hP).finrank
  exact ⟨e p,hep,hgen,ht.trans hr.symm⟩
private theorem c3r {A:Type} [oD A] [zE A] [oq dF A]
    (d:Fin 3→A) (L:Fin 2→nW) :
    azK (adv d L) =
      aOH (R:=l5) (S:=bah d) (afO L (adu d)).toRingHom *
        aOH (R:=bah d) (S:=A[X]) (brj d).toRingHom:= by
  let Q:=bah d
  let j:Q →ₐ[dF] A[X] :=brj d
  let g:l5 →ₐ[dF] Q:=afO L (adu d)
  have hj:p7 j:=cVS d
  have hc := @eJz Q A[X]
    (inferInstanceAs (oD (bah d))) (inferInstanceAs (oD A[X]))
    (inferInstanceAs (zE A[X]))
    (inferInstanceAs (oq dF (bah d))) (inferInstanceAs (oq dF A[X]))
    g j hj
  exact hc
theorem proof :Pw.c6:= by
 intro A _ _ _ d L M hL hfin hM hi
 have hiM:p7 (afO M (adu d)) :=
  fun p q hpq=>hi (ox (brj d) hpq)
 have hiL:=epP hL hM hiM
 have hiL' : p7 (adv d L) := by
  rw [dOP]
  exact (cVS d).comp hiL
 haveI: (adu d).IsPrime :=Pc (ab4 d)
 obtain ⟨p,hp,hpI,hpR⟩:=aOf (adu d) (cHE d)
  L hL.1 hL.2 hiL
 obtain ⟨q,hq,hqI,hqR⟩:=aOf (adu d) (cHE d)
  M hM.1 hM.2 hiM
 have hassoc:Associated p q:=Ideal.span_singleton_eq_span_singleton.mp (hpI.symm.trans hqI)
 obtain ⟨u,hu⟩:=hassoc
 have hdeg:q.totalDegree=p.totalDegree := by
  rw [← hu,zzD hp (Units.ne_zero u),
    (isUnit_iff_totalDegree_of_isReduced.mp u.isUnit).2,zS]
 have hrank :azK (adv d M)=azK (adv d L) := by
  rw [c3r,c3r]
  simp only [afO]
  rw [← hpR,← hqR,hdeg]
 letI:=hfin
 letI:=eJx (adv d L) hiL'
 have hpos :0<azK (adv d M) := by
  rw [hrank]
  exact Module.finrank_pos
 exact ⟨FiniteDimensional.of_finrank_pos hpos,hrank⟩
end
end ban
end
section
namespace VG
noncomputable section
open aR Tx XU aqa MvPolynomial
open zP hiding auv
open scoped BigOperators Pointwise
@[simp] theorem bI5 {s :nI} {a :t5} :
   a∈PS s↔dM (s.scale 2) a :=
  zih _
theorem cSw {s :nI} {f :gQ} (h:LQ s f) {a :t5}
  (ha :a∈f.support) :dM s a := by
 obtain ⟨hb,hj,ht⟩:=h a ha
 rw [G0 a (fun _ n=>n) (fun _=>rfl)] at hb
 rw [G0 a (fun i n=>i.val*n) (fun _=>Nat.mul_zero _)] at hj
 exact ⟨hb,hj,ht⟩
theorem gNl (s :nI) :0∈PS s := by
 simp [dM]
theorem cpF {s :nI} (hc:lB.bF s)
   (ht:0<s.t) (j:Fin 4) :vi j 1∈PS s := by
 have hb:3≤ s.b:= by have :=hc.1; have :=hc.2; omega
 have hj:3≤ s.j:= by have :=hc.2; omega
 have hj' : j.val≤3:= by omega
 rw [bI5]
 refine ⟨?_,?_,?_⟩
 · simpa [Kc,p9] using (show 1≤2*s.b by omega)
 · simpa [Kc,p9,mul_ite] using
     (show j.val≤2*s.j by omega)
 · by_cases h:j=3
   · subst j
     simpa [p9] using (show 1≤2*s.t by omega)
   · simp [h,p9]
theorem bOk {s :nI} {f :gQ} (h:LQ s f) :
   (f^2).support⊆PS s := by
 classical
 intro e he
 rw [pow_two] at he
 obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (support_mul f f he)
 obtain ⟨ha₀,ha₁,ha₃⟩:=cSw h ha
 obtain ⟨hb₀,hb₁,hb₃⟩:=cSw h hb
 rw [bI5]
 refine ⟨?_,?_,?_⟩
 · simpa [p9,Cy ,vG,two_mul] using
     wA ha₀ hb₀
 · simpa [p9,Cy ,In,vG,two_mul] using
     wA ha₁ hb₁
 · simpa [p9,Cy ,two_mul] using wA ha₃ hb₃
theorem dSt (F G L D:gQ) :
   qM (![F,G,L,D] :Fin 4→ gQ) =
     XU.ke (ov {F,G,L}) D:= by
 unfold qM XU.ke
 rw [← Ideal.span_union]
 congr 1
 ext f
 simp [or_left_comm,or_comm]
theorem bKz (y :oe) :
  yz.oF y=Ol y := by
 ext f
 exact (mem_vanishingIdeal_singleton_iff y f).trans RingHom.mem_ker.symm
theorem a6E (J:lz gQ) (y :oe) :
  yz.Ny J y=ajK (yo y) J:= by
 let r :PrimeSpectrum gQ:=⟨yz.oF y,xm⟩
 change ajK r J=ajK (yo y) J
 rw [show r=yo y from PrimeSpectrum.ext (bKz y)]
theorem c4n {J:lz gQ} {y :oe}
   (h:Ol y∈J.minimalPrimes) :
   (J.map (aU gQ (MZ y))).radical =
     qz (MZ y) := by
 rw [GR
   (MZ y) (yo y).asIdeal J h,Il]
theorem c4j {J:lz gQ} {y :oe}
  (h:Ol y∈J.minimalPrimes) :
  ajK (yo y) J ≠ ⊤ := by
 let R:=MZ y
 let I:=J.map (aU gQ R)
 have hmin:qz R∈I.minimalPrimes := by
  rw [← VS ,c4n h]
  exact ⟨⟨xm,vZ⟩,fun _ hP _=>hP.2⟩
 let:IsArtinianRing (R ⧸ I) :=
  IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
 change Au R (R ⧸ I) ≠ ⊤
 rw [zAi (uh (I:=I))]
 exact Module.length_ne_top_iff.mpr ((isArtinianRing_iff_isFiniteLength (R ⧸ I)).mp xm)
theorem gut {f :Fin 4→ gQ} {y :oe}
  (h:Ol y∈(qM f).minimalPrimes) :
  Ol y∈(qM (fun i=>f i^2)).minimalPrimes := by
 simpa only [qM,← VS
  (I:=ov (vk fun i=>f i^2)),
  cek f (fun _=>2) (fun _=> by decide),VS] using h
theorem guu {f :Fin 4→ gQ} {y :oe}
    (h:Ol y∈(qM f).minimalPrimes)
    (hreg : ∀ (g:Fin 4→MZ y),
      (ov (vk g)).radical=qz (MZ y) →
      ∀ i x,g i*x∈K7 g i→x∈K7 g i) :
    ajK (yo y) (qM (fun i=>f i^2)) =
      16*ajK (yo y) (qM f) := by
  let R:=MZ y
  let a :Fin 4→R:= fun i=>aU gQ R (f i)
  have hmap (g:Fin 4→ gQ) :
      (qM g).map (aU gQ R) =
        ov (vk fun i=>aU gQ R (g i)) := by
    rw [qM,uJ,← RJ]
    rfl
  have hrad: (ov (vk a)).radical=qz R:= by
    rw [← hmap f]
    exact c4n h
  have hcancel (e :Fin 4→ℕ) (he : ∀ j,0<e j) (i:Fin 4) (x :R)
      (hx :a i*x∈K7 (fun j=>a j^e j) i) :
      x∈K7 (fun j=>a j^e j) i:= by
    let d (j:Fin 4) :ℕ:=if j=i then 1 else e j
    let g (j:Fin 4) :R:=a j^d j
    have hd (j:Fin 4) :0<d j:= by by_cases hj:j=i <;> simp [d,hj,he j]
    have hg: (ov (vk g)).radical=qz R :=
      (cek a d hd).trans hrad
    have hgi:g i=a i:= by simp [g,d]
    have hr :K7 g i=K7 (fun j=>a j^e j) i:= by
      unfold K7
      congr 1
      exact S1 fun j hj=> by
        have hji:j≠i:=hj
        simp [g,d,hji]
    rw [← hr] at hx ⊢
    exact hreg g hg i x (by simpa only [hgi] using hx)
  have hp:=c46 a (fun _=>2) (fun _=> by decide) hcancel
  change yC ((qM (fun i=>f i^2)).map (aU gQ R)) =
    16*yC ((qM f).map (aU gQ R))
  rw [hmap,hmap]
  simpa only [xW,zJD,Finset.card_univ,Pf ,
    C9,show 2^4=(16:ℕ) by decide] using hp
private theorem eur {s :nI} {F:gQ} (ht:s.t=0)
  (hF:LQ s F) : (3:Fin 4)∉F.vars := by
 intro h
 obtain ⟨a,ha,hav⟩:=(mem_vars_iff_mem_support _).mp h
 exact (Finsupp.mem_support_iff.mp hav) (Ob (ht ▸ (hF a ha).2.2))
theorem eFw {f :Fin 4→ gQ} {s :Fin 4→nI}
    (ht : ∀ i,(s i).t=0) (hf : ∀ i,LQ (s i) (f i)) (y :oe) :
    Ol y∉(qM f).minimalPrimes := by
  classical
  intro h
  let φ:gQ →+* nX we.cH :=
    Et lJ (fun j=>if j=3 then mD else lJ (y j))
  have hφ: (yQ (y 3)).comp φ=eval y := by
    apply t8
    · intro c
      simp [φ]
    · intro j
      by_cases hj:j=3 <;> simp [φ,hj]
  have hle :sS φ≤Ol y := by
    intro z hz
    change eval y z=0
    rw [← hφ,EK,RingHom.mem_ker.mp hz,qm]
  have hfφ:qM f≤ sS φ:= by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hz :=RingHom.mem_ker.mp (h.le (Dz (Set.mem_range_self i)))
    change φ (f i)=0
    have heq :φ (f i)=lJ (eval y (f i)) := by
      apply hom_congr_vars (f₂:=Polynomial.C.comp (eval y)) _ _ rfl
      · ext c
        simp [φ]
      · intro j hj _
        have hj' : j≠3:= fun e=>eur (ht i) (hf i) (e ▸ hj)
        simp [φ,hj']
    rw [heq,hz,qm]
  have heq :sS φ=Ol y :=
    hle.antisymm (h.2 ⟨Pc φ,hfφ⟩ hle)
  have hx :lI (3:Fin 4)-MvPolynomial.C (y 3)∈Ol y := by
    change eval y (lI 3-MvPolynomial.C (y 3))=0
    simp
  rw [← heq] at hx
  have hn:=RingHom.mem_ker.mp hx
  exact Polynomial.X_sub_C_ne_zero (y 3) (by simpa [φ,uz] using hn)
end
end VG
end
section
namespace VG
noncomputable section
open aR lB XU
open zP (LK)
open MeasureTheory
open scoped BigOperators Pointwise
private theorem aOL (s :nI) (x :QC) :
  x∈nD s↔(∀ i,0≤x i)∧x 0 + x 1 + x 2 + x 3≤ s.b ∧
    x 1+2*x 2 + 3*x 3≤ s.j∧x 3≤ s.t:= by
 norm_num [nD,x7]
private theorem dPD (s :nI) :Convex ℝ (nD s) := by
 intro x hx y hy a b ha hb hab
 obtain ⟨hx,hxb,hxj,hxt⟩:=(aOL s x).mp hx
 obtain ⟨hy,hyb,hyj,hyt⟩:=(aOL s y).mp hy
 apply (aOL s _).mpr
 simp only [TZ,Mj,v8]
 refine ⟨fun i=>add_nonneg (ze ha (hx i)) (ze hb (hy i)),?_,?_,?_⟩
 · nlinarith [t7 hxb ha,t7 hyb hb,
    ox (fun t:ℝ=>t*s.b) hab]
 · nlinarith [t7 hxj ha,t7 hyj hb,
    ox (fun t:ℝ=>t*s.j) hab]
 · nlinarith [t7 hxt ha,t7 hyt hb,
    ox (fun t:ℝ=>t*s.t) hab]
private def param (s :nI) (u:Fin 4→ℝ) :QC :=
 let z :=u 3*s.t
 let x₂:=u 2*((s.j:ℝ)-3*z)
 let x₁:=u 1*(2*((s.j:ℝ)-3*z) - 2*x₂)
 ![u 0*(2*(s.b:ℝ) - x₁ - x₂ - 2*z),x₁,x₂,2*z]
private theorem eJR (s :nI) (u:Fin 4→ℝ) (i:Fin 4) :
  param s u=(1 - u i)•param s (N0 u i 0) +
   u i•param s (N0 u i 1) := by
 funext j
 fin_cases i <;> fin_cases j <;>
  simp [param,TZ,v8 ,N0] <;> ring
private theorem dP4 (s :nI) (hs :bF s) (u:Fin 4→ℝ)
    (hu : ∀ i,u i=0∨u i=1) :param s u∈LK (PS s) := by
  have hbinary (i:Fin 4) : ∃ v :ℕ,(v :ℝ)=u i∧v≤1 := by
    rcases hu i with hi | hi
    · exact ⟨0,by simpa using hi.symm,R9⟩
    · exact ⟨1,by simpa using hi.symm,vZ⟩
  choose v hv using hbinary
  let z :=v 3*s.t
  let r :=s.j-3*z
  let x₂:=v 2*r
  let x₁:=v 1*(2*r - 2*x₂)
  have hz :z≤ s.t:= by simpa [z] using P7 s.t (hv 3).2
  have hzr :3*z≤ s.j:=(SD _ hz).trans hs.2
  have h₂:x₂≤ r := by simpa [x₂] using P7 r (hv 2).2
  have h₂' : 2*x₂≤2*r :=SD _ h₂
  have h₁:x₁≤2*r - 2*x₂:= by
    simpa [x₁] using P7 (2*r - 2*x₂) (hv 1).2
  have hindex :x₁+2*x₂+3*(2*z)≤2*s.j:= by dsimp only [r] at *; omega
  have hsum:x₁ + x₂+2*z≤2*s.b:= by have :=hs.1; omega
  let x₀:=v 0*(2*s.b-(x₁ + x₂+2*z))
  have h₀:x₀≤2*s.b-(x₁ + x₂+2*z) := by
    simpa [x₀] using P7 (2*s.b-(x₁ + x₂+2*z)) (hv 0).2
  let w:Fin 4→ℕ := ![x₀,x₁,x₂,2*z]
  let e :Exponent:=Finsupp.equivFunOnFinite.symm w
  have he (i:Fin 4) :e i=w i :=
    Nr (Finsupp.equivFunOnFinite.apply_symm_apply w) i
  apply WW ℝ _
  refine ⟨e,bI5.mpr ?_,?_⟩
  · simp only [dM,x7,he,w,zbs,
      p9,Fin.val_zero,Nat.zero_mul,yB]
    change x₀ + x₁ + x₂+2*z≤2*s.b ∧
      1*x₁+2*x₂+3*(2*z)≤2*s.j∧2*z≤2*s.t
    omega
  · have hz' : (z :ℝ)=u 3*s.t:= by simp only [z,Nat.cast_mul,(hv 3).1]
    have hr' : (r :ℝ)=s.j-3*(u 3*s.t) := by
      simp only [r,zjK hzr,zd ,C9 ,hz']
    have h₂' : (x₂:ℝ)=u 2*(s.j-3*(u 3*s.t)) := by
      simp only [x₂,zd ,(hv 2).1,hr']
    have h₁' : (x₁:ℝ)=u 1*(2*(s.j-3*(u 3*s.t)) -
        2*(u 2*(s.j-3*(u 3*s.t)))) := by
      have hsub:2*x₂≤2*r :=SD  _ h₂
      simp only [x₁,zd ,zjK hsub,C9 ,(hv 1).1,hr',h₂']
    funext i
    change (e i:ℝ)=param s u i
    rw [he]
    fin_cases i
    · change (x₀:ℝ)= _
      simp only [x₀,zd ,zjK hsum,C9 ,GB ,
        (hv 0).1,h₁',h₂',hz']
      change _=u 0*(2*(s.b:ℝ)-_-_-_)
      ring
    · exact h₁'
    · exact h₂'
    · change (↑(2*z) :ℝ)=2*(u 3*s.t)
      rw [zd ,C9 ,hz']
private theorem dRJ (s :nI) (hs :bF s) (T:n5 (Fin 4)) (u:Fin 4→ℝ)
    (hside : ∀ i∈T,0≤u i∧u i≤1)
    (hcorner : ∀ i∉T,u i=0∨u i=1) :
    param s u∈LK (PS s) := by
  classical
  induction T using Df generalizing u with
  | empty=>exact dP4 s hs u (fun i=>hcorner i (by simp))
  | @insert i T hi ih =>
      have updated (b:ℝ) (hb:b=0∨b=1) :
          param s (N0 u i b)∈LK (PS s) := by
        apply ih
        · intro j hj
          have hji:j≠i:= fun e=>hi (e ▸ hj)
          simpa [zBg hji] using hside j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hji:j=i
          · subst j
            simpa using hb
          · rw [zBg hji]
            exact hcorner j (by simp [hji,hj])
      have hui:=hside i (Finset.mem_insert_self i T)
      rw [eJR s u i]
      exact zvj ℝ _ (updated 0 (Or.inl rfl)) (updated 1 (Or.inr rfl))
        (sub_nonneg.mpr hui.2) hui.1 (sub_add_cancel 1 (u i))
private theorem aND {x d:ℝ} (hx :0≤x) (hxd:x≤d) :
   ∃ u:ℝ,(0≤u∧u≤1)∧u*d=x := by
 by_cases hd:d=0
 · exact ⟨0,⟨vZ,R9⟩,by linarith⟩
 · have hd' : 0<d:=lt_of_le_of_ne (hx.trans hxd) (Ne.symm hd)
   exact ⟨x/d,⟨div_nonneg hx hd'.le,(div_le_one hd').mpr hxd⟩,div_mul_cancel₀ x hd⟩
theorem bry (s :nI) (hs :bF s) :
    LK (PS s)=nD (s.scale 2) := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (dPD _)
    rintro _ ⟨e,he,rfl⟩
    obtain ⟨hb,hj,ht⟩:=bI5.mp he
    refine (aOL _ _).mpr ⟨fun _=>zm _,?_,?_,?_⟩
    · simp only [x7] at hb
      change (e 0:ℝ)+e 1+e 2+e 3≤_
      exact_mod_cast hb
    · have hindex :e 1+2*e 2 + 3*e 3≤(s.scale 2).j:= by
        simpa [x7] using hj
      change (e 1 :ℝ)+2*e 2 + 3*e 3≤_
      exact_mod_cast hindex
    · exact Nat.cast_le.mpr ht
  · intro x hx
    obtain ⟨hx,hb,hj,ht⟩:=(aOL _ _).mp hx
    simp only [p9,zd ,C9] at hb hj ht
    obtain ⟨u₃,hu₃,h₃⟩:=aND (div_nonneg (hx 3) (by norm_num : (0:ℝ)≤2))
      (show x 3/2≤ s.t by linarith)
    obtain ⟨u₂,hu₂,h₂⟩:=aND (hx 2)
      (show x 2≤ s.j-3*(u₃*s.t) by linarith [hx 1])
    obtain ⟨u₁,hu₁,h₁⟩:=aND (hx 1)
      (show x 1≤2*(s.j-3*(u₃*s.t)) - 2*(u₂*(s.j-3*(u₃*s.t))) by
        rw [h₂]
        linarith)
    obtain ⟨u₀,hu₀,h₀⟩:=aND (hx 0)
      (show x 0≤2*(s.b:ℝ)-(u₁*(2*(s.j-3*(u₃*s.t)) -
        2*(u₂*(s.j-3*(u₃*s.t)))))-(u₂*(s.j-3*(u₃*s.t))) -
          2*(u₃*s.t) by
        rw [h₁,h₂,h₃]
        linarith)
    let u:Fin 4→ℝ := ![u₀,u₁,u₂,u₃]
    have heq :param s u=x := by
      funext i
      fin_cases i
      · exact h₀
      · exact h₁
      · exact h₂
      · change 2*(u₃*s.t)=x 3
        linarith
    rw [← heq]
    apply dRJ s hs t9
    · intro i _
      fin_cases i
      · exact hu₀
      · exact hu₁
      · exact hu₂
      · exact hu₃
    · simp
theorem bB6 (s :nI) :nD (s.scale 2)=(2 :ℝ)•nD s := by
 ext x
 constructor
 · intro hx
   obtain ⟨hx,hb,hj,ht⟩:=(aOL _ _).mp hx
   simp only [p9,zd ,C9] at hb hj ht
   refine ⟨fun i=>x i/2,(aOL _ _).mpr ?_,?_⟩
   · exact ⟨fun i=>div_nonneg (hx i) (by norm_num),by linarith,by linarith,by linarith⟩
   · funext i
     change 2*(x i/2)=x i
     ring
 · rintro ⟨u,hu,rfl⟩
   obtain ⟨hu,hb,hj,ht⟩:=(aOL _ _).mp hu
   apply (aOL _ _).mpr
   simp only [Mj,v8 ,p9,zd ,C9]
   exact ⟨fun i=>ze (by norm_num) (hu i),by linarith,by linarith,by linarith⟩
end
end VG
end
section
namespace VG
noncomputable section
open aR lB XU
open zP (LK)
open MeasureTheory
open scoped BigOperators Pointwise
private def bhD (B:Fin 4→Set QC) (I:n5 (Fin 4))
   (F:Set QC→ℝ) (x :Set QC) :ℝ :=
 ∑ T∈I.powerset,(-1 :ℝ)^(I.card - T.card)*F (x + ∑ j∈T,B j)
private theorem bOs (B:Fin 4→Set QC)
   {i:Fin 4} {I:n5 (Fin 4)} (hi:i∉I)
   (F:Set QC→ℝ) (x :Set QC) :
   bhD B (EP i I) F x =
     bhD B I (aTq F (B i)) x := by
 classical
 unfold bhD
 rw [Finset.sum_powerset_insert hi,← vG]
 apply vw rfl
 intro T hT
 have hsub:=Finset.mem_powerset.mp hT
 have TA:= fun h=>hi (hsub h)
 have hle :=Finset.card_le_card hsub
 rw [zwo hi,zwo TA,
   z8 TA,show I.card+1 - T.card=I.card - T.card+1 by omega,
   show I.card+1-(T.card+1)=I.card - T.card by omega,
   show x+(B i + ∑ j∈T,B j)=(x + ∑ j∈T,B j)+B i by ac_rfl,
   C5 ,aTq]
 ring
theorem c0t (p q r s :nI) :
   vl ![nD p,nD q,nD r,nD s] =
     aTr p q r s := by
 classical
 let B:Fin 4→Set QC := ![nD p,nD q,nD r,nD s]
 have heq :vl B=bhD B t9 a2a 0:= by
   simp [vl,bhD,a2a]
 change vl B= _
 rw [heq,show (t9 :n5 (Fin 4))=EP 0 (EP 1 (EP 2 (EP 3 ∅))) by decide]
 rw [bOs B (show (0:Fin 4)∉insert 1 (insert 2 (insert 3 ∅)) by decide),
   bOs B (show (1 :Fin 4)∉EP  2 (EP  3 ∅) by decide),
   bOs B (show (2 :Fin 4)∉EP  3 ∅ by decide),
   bOs B (show (3:Fin 4)∉(∅ : n5  (Fin 4)) by decide)]
 simp [bhD,aTr,B,Set.singleton_zero]
private theorem dYx (s t:Set QC) :
   (2 :ℝ)•(s+t)=(2 :ℝ)•s+(2 :ℝ)•t:= by
 ext x
 constructor
 · rintro ⟨_,⟨u,hu,v,hv,rfl⟩,rfl⟩
   exact ⟨2•u,⟨u,hu,rfl⟩,2•v,⟨v,hv,rfl⟩,(smul_add (2 :ℝ) u v).symm⟩
 · rintro ⟨_,⟨u,hu,rfl⟩,_,⟨v,hv,rfl⟩,rfl⟩
   exact ⟨u+v,⟨u,hu,v,hv,rfl⟩,smul_add (2 :ℝ) u v⟩
private theorem dYy (B:Fin 4→Set QC) (T:n5 (Fin 4)) :
   (∑ i∈T,(2 :ℝ)•B i)=(2 :ℝ)•(∑ i∈T,B i) := by
 induction T using Df with
 | empty=>simp [← Set.singleton_zero]
 | @insert i T hi ih=>rw [Finset.sum_insert hi,Finset.sum_insert hi,ih,dYx]
private theorem eAK (B:Fin 4→Set QC) :
   vl (fun i=>(2 :ℝ)•B i) =
     16*vl B:= by
 unfold vl
 rw [yl]
 apply vw rfl
 intro T _
 rw [dYy,Measure.addHaar_smul_of_nonneg _ (by norm_num : (0:ℝ)≤2),
   Module.finrank_fintype_fun_eq_card,Pf ,zFP]
 norm_num
 ring
theorem eAL {p q H :nI} (hp:bF p)
   (hq:bF q) (hH :bF H) :
   vl (fun i=>LK (Eb p q H i)) =
     16*aTr p q q H := by
 let B:Fin 4→Set QC := ![nD p,nD q,nD q,nD H]
 have he : (fun i=>LK (Eb p q H i))=fun i=>(2 :ℝ)•B i:= by
   funext i
   fin_cases i
   · exact (bry p hp).trans (bB6 p)
   · exact (bry q hq).trans (bB6 q)
   · exact (bry q hq).trans (bB6 q)
   · exact (bry H hH).trans (bB6 H)
 rw [he,eAK]
 exact ox (16 * ·) (c0t p q q H)
theorem dEH {p q H :nI} (hp:p.t=0) (hq:q.t=0) (hH :H.t=0) :
    aTr p q q H=0:= by
  classical
  let B:Fin 4→Set QC := ![nD p,nD q,nD q,nD H]
  let E :Set QC := {x | x 3=0}
  have hcap (s :nI) (hs :s.t=0) :nD s⊆E := by
    intro x hx
    have ht:=hx.2.2.2
    rw [hs,Nat.cast_zero] at ht
    exact wY ht (hx.1 3)
  have hB (i:Fin 4) :B i⊆E := by
    fin_cases i
    · exact hcap p hp
    · exact hcap q hq
    · exact hcap q hq
    · exact hcap H hH
  have hsum (T:n5 (Fin 4)) : (∑ i∈T,B i)⊆E := by
    induction T using Df with
    | empty=>simp [E,← Set.singleton_zero]
    | @insert i T hi ih =>
        rw [z8 hi]
        rintro _ ⟨u,hu,v,hv,rfl⟩
        change u 3+v 3=0
        rw [show u 3=0 from hB i hu,show v 3=0 from ih hv,yB]
  have hE :oj E=0:= by
    rw [volume_pi]
    exact Measure.pi_hyperplane (fun _=>oj) 3 0
  rw [← c0t]
  change vl B= _
  unfold vl
  apply Finset.sum_eq_zero
  intro T _
  rw [measure_mono_null (hsum T) hE,ENNReal.toReal_zero,vj]
end
end VG
end
section
namespace VG
noncomputable section
open aR lB Tx XU
open aqa (K7)
open zP (fZ HG TX LK)
open MeasureTheory Filter
open scoped BigOperators Pointwise Topology
def c1 :Prop :=
  ∀ (y :oe) (g:Fin 4→MZ y),
    (ov (vk g)).radical=qz (MZ y) →
    ∀ i x,g i*x∈K7 g i→x∈K7 g i
def c2 :Prop :=
  ∀ (p q H :nI),bF p→bF q→bF H →
    let A:=Eb p q H
    oz (fZ A) (HG A) →
    ∀ (f :Fin 4→ gQ),(∀ i,(f i).support⊆A i) →
      ∀ points :n5 oe,
        (∀ y∈points,yz.oF y∈(qM f).minimalPrimes) →
        (∑ y∈points,(yz.Ny (qM f) y).toNat) ≤
          pG (fZ A) (HG A)
def c3:Prop :=
  ∀ (p q H :nI),bF p→bF q→bF H →
    (0<p.t∨0<q.t∨0<H.t) →
    let A:=Eb p q H
    oz (fZ A) (HG A) ∧
      ∃ b:ℕ,∀ n:ℕ,
        (pG (fZ A) (HG A) :ℝ)*(n:ℝ)^4 =
          ∑ S∈(t9 :n5 (Fin 4)).powerset,
            (-1 :ℝ)^(4 - S.card)*(TX A (uW b n S) :ℝ)
def c4 :Prop :=
  ∀ (p q H :nI),bF p→bF q→bF H →
    ∀ (b:ℕ) (S:n5 (Fin 4)),
      let A:=Eb p q H
      th (fun n:ℕ=>(TX A (uW b n S) :ℝ)/(n:ℝ)^4)
        atTop (𝓝 (volume (∑ i∈S,LK (A i))).toReal)
private theorem efU (hdiag:c4) {p q H :nI}
    (hp:bF p) (hq:bF q) (hH :bF H) (b:ℕ)
    (h : ∀ n:ℕ,(pG (fZ (Eb p q H))
        (HG (Eb p q H)) :ℝ)*(n:ℝ)^4 =
        ∑ S∈(t9 :n5 (Fin 4)).powerset,
          (-1 :ℝ)^(4 - S.card)*(TX (Eb p q H) (uW b n S) :ℝ)) :
    (pG (fZ (Eb p q H)) (HG (Eb p q H)) :ℝ) =
      16*aTr p q q H := by
  rw [← eAL hp hq hH]
  unfold vl
  apply tendsto_nhds_unique (l:=(atTop:Filter ℕ))
    (f := fun n:ℕ => ∑ S∈(t9 :n5 (Fin 4)).powerset,
      (-1 :ℝ)^(4 - S.card)*((TX (Eb p q H) (uW b n S) :ℝ)/(n:ℝ)^4))
  · apply tendsto_const_nhds.congr'
    filter_upwards [Kp (1 :ℕ)] with n hn
    have hn' : (n:ℝ)^4≠0:=J4 _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
    symm
    calc
      _=(∑ S∈(t9 :n5 (Fin 4)).powerset,
          (-1 :ℝ)^(4 - S.card)*(TX (Eb p q H) (uW b n S) :ℝ)) /
            (n:ℝ)^4 := by simp only [Finset.sum_div,mul_div_assoc]
      _ = _:= by rw [← h n,mul_div_cancel_right₀ _ hn']
  · exact tendsto_finsetSum _ fun S _=>(hdiag p q H hp hq hH b S).const_mul _
theorem dDP (h:zP.c2) :c3:= by
 intro p q H hp hq hH htop
 apply h
 · intro i
   fin_cases i <;> exact gNl _
 · intro j
   rcases htop with ht | ht | ht
   · exact ⟨0,cpF hp ht j⟩
   · exact ⟨1,cpF hq ht j⟩
   · exact ⟨3,cpF hH ht j⟩
theorem of_children (hregular :c1) (hspec :c2) (hhilb:c3) (hdiag:c4) :
    XU.c3:= by
  classical
  intro p q H hp hq hH F G L D hF hG hL hD m points hpoints
  let f :Fin 4→ gQ := ![F,G,L,D]
  let g:Fin 4→ gQ:= fun i=>f i^2
  let J:=qM f
  let J' := qM g
  have hpoints' (y :oe) (hy :y∈points) :bRb J m y := by
    simpa only [J,f,dSt] using hpoints y hy
  by_cases htop:0<p.t∨0<q.t∨0<H.t
  · have hsupp (i:Fin 4) : (g i).support⊆Eb p q H i:= by
      fin_cases i
      · exact bOk hF
      · exact bOk hG
      · exact bOk hL
      · exact bOk hD
    have hmin (y :oe) (hy :y∈points) :
        Ol y∈J'.minimalPrimes :=gut (hpoints' y hy).1
    have hlen (y :oe) (hy :y∈points) :
        16*m≤(yz.Ny J' y).toNat := by
      have hm: (↑(16*m) :ℕ∞)≤ajK (yo y) J' := by
        rw [zd ,C9,guu (hpoints' y hy).1 (hregular y)]
        exact t7 (hpoints' y hy).2 zero_le
      rw [← a6E] at hm
      have hfin:=c4j (hmin y hy)
      rw [← a6E] at hfin
      simpa only [zzq] using ENat.toNat_le_toNat hm hfin
    obtain ⟨hfinite,b,hb⟩:=hhilb p q H hp hq hH htop
    have hbnd:=hspec p q H hp hq hH hfinite g hsupp points
      (fun y hy=> by simpa only [bKz] using hmin y hy)
    have hn:16*m*points.card ≤
        pG (fZ (Eb p q H)) (HG (Eb p q H)) := by
      calc
        _ = ∑ _y∈points,16*m:= by simp [Nat.mul_comm]
        _≤_:=(wB hlen).trans hbnd
    have hr :=(Nat.cast_le (α:=ℝ)).mpr hn
    rw [efU hdiag hp hq hH b hb] at hr
    push_cast at hr ⊢
    linarith
  · have hpt:p.t=0:= by omega
    have hqt:q.t=0:= by omega
    have hHt:H.t=0:= by omega
    let s :Fin 4→Shape := ![p,q,q,H]
    have hz (i:Fin 4) : (s i).t=0:= by fin_cases i <;> assumption
    have hfit (i:Fin 4) :LQ  (s i) (f i) := by fin_cases i <;> assumption
    have hempty :points = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun y hy =>
      eFw hz hfit y (hpoints' y hy).1
    simp [hempty,dEH hpt hqt hHt]
end
end VG
end
section
namespace axi
open Tx (gQ)
open zP (fZ ve)
open scoped Polynomial
noncomputable section
abbrev Affine (k :Type) [oD k] :=cy (Fin 4) k
abbrev Family (k :Type) [oD k] :=Affine k[X]
def DX {R:Type} [oD R] (f :Fin 4→Affine R) :lz (Affine R) :=
 ov (vk f)
def wN {k :Type} [c9 k] (y :Fin 4→k) :lz (Affine k) :=
 sS (xI y)
instance gRy {k :Type} [c9 k] (y :Fin 4→k) :
 (wN y).IsPrime :=Pc _
def Cm {R:Type} [oD R] (I P:lz R) [P.IsPrime] :lz R :=
 let ι:=aU R (oY P)
 (I.map ι).comap ι
def IS {k :Type} [oD k] :Family k →+* Affine k :=
 oy (yQ 0)
def ZO {k :Type} [c9 k] (y :Fin 4→k) :lz (Family k) :=
 (wN y).comap IS
instance gQu {k :Type} [c9 k] (y :Fin 4→k) :
 (ZO y).IsPrime :=Ideal.comap_isPrime _ _
def bfv {k :Type} [c9 k] (I:lz (Affine k)) (points :n5 (Fin 4→k)) :
    lz (Affine k) :=
  ⨅ y : ↥points,Cm I (wN y.1)
abbrev lN (k :Type) [c9 k] :=qJ (nX k)
def bqz {k :Type} [c9 k] :Family k →+* Affine (lN k) :=
 oy (aU k[X] (lN k))
abbrev a90 {k :Type} [c9 k] (F:Fin 4→Family k) :=
 Affine (lN k) ⧸ DX (fun i=>bqz (F i))
def aMZ (A:Fin 4→n5 pz) (f :Fin 4→ gQ) (i:Fin 4) :
    Family (fZ A) :=
  pQ (1-Polynomial.X) *
     oy (Polynomial.C.comp (aU _ (fZ A))) (f i) +
    pQ mD *oy lJ (ve A i)
end
end axi
end
section
namespace axi
open Tx (gQ)
open zP (xB fZ ve HG)
open MvPolynomial
open scoped Polynomial TensorProduct
noncomputable section
def aPw (R S:Type) [oD R] [oD S] [oq R S]
    (I:lz (Affine R)) :
    S ⊗[R] (Affine R ⧸ I) ≃ₐ[S] Affine S ⧸ I.map (map (aU R S)) := by
  let e :S ⊗[R] Affine R ≃ₐ[S] Affine S:=zoR R S
  have hmap :e.toRingHom.comp (Ww (A:=S) (R:=R)).toRingHom =
      map (σ:=Fin 4) (aU R S) := by
    apply X8
    intro p
    change e (1 ⊗ₜ[R] p)= _
    simp [e]
  refine (zTd S (Affine R) S I).trans
    (zpY _ _ e ?_)
  change I.map (map (aU R S)) =
    (I.map (Ww (A:=S) (R:=R)).toRingHom).map e.toRingHom
  rw [zR,hmap]
theorem bpr {R S:Type} [oD R] [oD S]
  (g:R →+* S) (f :Fin 4→Affine R) :
  (DX f).map (map g)=DX (fun i=>map g (f i)) := by
 rw [DX,DX,uJ,← RJ]
 rfl
private def bcA (A:Fin 4→n5 pz) (f :Fin 4→ gQ) :
  xB A →+* (fZ A)[X] :=
 Et (Polynomial.C.comp (aU _ (fZ A))) fun s =>
  (1-Polynomial.X)*lJ (aU _ _ ((f s.1).coeff s.2.1)) +
    mD *lJ (aU (xB A) _ (lI s))
private theorem d2E (A:Fin 4→n5 pz) (f :Fin 4→ gQ) :
   (yQ 1).comp (bcA A f) =
     aU (xB A) (fZ A) := by
 apply t8
 · intro a
   simp [bcA]
   rw [Ee we.cH (xB A),
     Mw]
 · intro i
   simp [bcA]
private def b7K (A:Fin 4→n5 pz) (f :Fin 4→ gQ) :
    fZ A →+* lN (fZ A) :=
  zIj
    (g:=(aU (fZ A)[X] _).comp (bcA A f)) <| by
      intro x y h
      have h' := KA (fZ A)[X]
        (lN (fZ A)) h
      apply KA (xB A) (fZ A)
      rw [← d2E A f]
      exact ox (yQ 1) h'
theorem dMS (A:Fin 4→n5 pz) (f :Fin 4→ gQ)
  (i:Fin 4) :
  IS (aMZ A f i)=map (aU _ (fZ A)) (f i) := by
 have hC: (yQ (0:fZ A)).comp lJ =
    RingHom.id _:= by
  ext a
  simp
 simp [IS,aMZ,map_map,← XG,hC]
private theorem dMR (A:Fin 4→n5 pz) (f :Fin 4→ gQ)
    (hs : ∀ i,(f i).support⊆A i) (i:Fin 4) :
    map (b7K A f) (ve A i)=bqz (aMZ A f i) := by
  classical
  have hsum:f i = ∑ a : ↥(A i),Kz a.1 ((f i).coeff a.1) := by
    rw [zNb (A i) (fun a=>Kz a ((f i).coeff a))]
    exact (f i).as_sum.trans (Finset.sum_subset (hs i) fun a _ ha=> by
      simp [notMem_support_iff.mp ha])
  have h :
      (∑ a : ↥(A i),Kz a.1
        (bcA A f (lI ⟨i,a⟩)))=aMZ A f i:= by
    conv_rhs =>
      unfold aMZ
      rw [hsum,ve]
    simp only [sI,map_monomial,yl,← vG,
      bcA,Pv,EK]
    apply vw rfl
    intro a _
    rw [qG,Wl,Wl]
  unfold bqz
  rw [← h]
  simp only [ve,sI,map_monomial]
  apply vw rfl
  intro a _
  congr 1
  unfold b7K
  exact zoc _ _
private theorem dyx (R S:Type) [c9 R] [c9 S] [oq R S]
    (J:lz (Affine R)) (h:oz R (Affine R ⧸ J)) :
    oz S (Affine S ⧸ J.map (map (aU R S))) ∧
      pG S (Affine S ⧸ J.map (map (aU R S))) =
        pG R (Affine R ⧸ J) := by
  let e :=aPw R S J
  let:oz R (Affine R ⧸ J) :=h
  exact ⟨Ar e.toLinearMap e.surjective,
    e.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange⟩
theorem ewS (A:Fin 4→n5 pz) (f :Fin 4→ gQ)
    (hs : ∀ i,(f i).support⊆A i)
    (hfinite :oz (fZ A) (HG A)) :
    oz (lN (fZ A)) (a90 (aMZ A f)) ∧
      pG (lN (fZ A)) (a90 (aMZ A f)) =
        pG (fZ A) (HG A) := by
  let K:=fZ A
  let L:=lN K
  let:oq (fZ A) (lN (fZ A)) :=
    (b7K A f).toAlgebra
  let J:=DX (ve A)
  have hJ:J.map (map (aU K L)) =
      DX (fun i=>bqz (aMZ A f i)) := by
    rw [bpr]
    congr 1
    funext i
    exact dMR A f hs i
  have hf :=dyx K L J hfinite
  rw [hJ] at hf
  exact hf
end
end axi
end
section
namespace axi
open wH (cH)
open Tx (gQ oe)

open yz (oF Ny)
open zP (fZ HG ke)
open scoped Polynomial TensorProduct
noncomputable section
def c1 :Prop :=
  ∀ (k :Type) [c9 k] [oq cH k] (f :Fin 4→ gQ)
    (y :oe),oF y∈(ke f).minimalPrimes →
    let P:=wN (fun i=>aU cH k (y i))
    let I:=DX (fun i=>oy (aU cH k) (f i))
    P∈I.minimalPrimes ∧
      oz k (Affine k ⧸ Cm I P) ∧
      pG k (Affine k ⧸ Cm I P) =
        (Ny (ke f) y).toNat
def c2 :Prop :=
  ∀ (k :Type) [c9 k] (F:Fin 4→Family k) (y :Fin 4→k),
    wN y∈(DX (fun i=>IS (F i))).minimalPrimes →
    ∀ r :Family k,
      pQ mD *r∈Cm (DX F) (ZO y) →
      r∈Cm (DX F) (ZO y)
private theorem gM8 {k :Type} [c9 k] (v :Affine k) :
  IS (oy lJ v)=v := by
 have h: (yQ (0:k)).comp lJ=RingHom.id k := by
  ext a
  simp
 simp [IS,MvPolynomial.map_map,h,MvPolynomial.map_id]
private theorem gNn {k :Type} [c9 k] (F:Fin 4→Family k)
   (y :Fin 4→k) {r :Family k}
   (h:r∈Cm (DX F) (ZO y)) :
   IS r∈Cm (DX (fun i=>IS (F i)))
     (wN y) := by
 let P:=ZO y
 let Q:=wN y
 change aU (Family k) (oY P) r ∈
   (DX F).map (aU (Family k) (oY P)) at h
 change aU (Affine k) (oY Q) (IS r) ∈
   (DX (fun i=>IS (F i))).map (aU (Affine k) (oY Q))
 obtain ⟨s,hs,hsr⟩ :=
   (zi P.primeCompl
     (oY P) (DX F) r).mp h
 apply (zi Q.primeCompl
   (oY Q) _ _).mpr
 refine ⟨IS s,hs,?_⟩
 change IS s* IS r∈DX (fun i=>IS (F i))
 rw [← nq,← show (DX F).map IS =
     DX (fun i=>IS (F i)) from bpr _ F]
 exact zf _ hsr
private theorem ezE (hreg:c2) (k :Type) [c9 k]
    (F:Fin 4→Family k) (points :n5 (Fin 4→k))
    (hisol : ∀ y∈points,wN y∈(DX (fun i=>IS (F i))).minimalPrimes)
    (hmarked:oz k
      (Affine k ⧸ bfv (DX (fun i=>IS (F i))) points))
    (hfinite :oz (lN k) (a90 F)) :
    pG k (Affine k ⧸ bfv (DX (fun i=>IS (F i))) points) ≤
      pG (lN k) (a90 F) := by
  classical
  let L:=lN k
  let J:=DX F
  let B:=Family k ⧸ J
  let I:=bfv (DX (fun i=>IS (F i))) points
  let E :=Affine k ⧸ I
  let N :=pG k E
  let:oz k E :=hmarked
  let b:=Module.finBasis k E
  choose v hv using (fun i:Fin N=>uh (b i))
  let u:Fin N→Family k := fun i=>oy lJ (v i)
  let rel : (Fin N→k[X])→Family k := fun c =>
    ∑ i,pQ (c i)*u i
  have specialize (c:Fin N→k[X])
      (hc : ∀ y∈points,rel c∈Cm J (ZO y)) :
      ∀ i,(c i).coeff 0=0:= by
    have hmem:IS (rel c)∈I :=
      Ideal.mem_iInf.mpr fun y=>gNn F y.1 (hc y.1 y.2)
    have hz :=Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hterm (i:Fin N) :
        lV I (IS (pQ (c i)*u i)) =
          (c i).coeff 0•b i:= by
      have hC:IS (pQ (c i))=pQ ((c i).coeff 0) := by
        simp [IS,zTt]
      have hu:IS (u i)=v i:=gM8 (v i)
      rw [nq,hC,hu,nq,← Mw ,
        zOY,← VH,hv]
    have hz' : ∑ i,(c i).coeff 0•b i=0:= by
      simpa only [rel,sI,← nq,hterm] using hz
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ hz'
  have allCoeffs (n:ℕ) (c:Fin N→k[X])
      (hc : ∀ y∈points,rel c∈Cm J (ZO y)) :
      ∀ i,(c i).coeff n=0:= by
    induction n generalizing c with
    | zero=>exact specialize c hc
    | succ n ih =>
      have hdiv (i:Fin N) :mD *(c i).divX=c i:= by
        simpa [specialize c hc i] using zQv (c i)
      have hrel :pQ mD *rel (fun i=>(c i).divX)=rel c:= by
        simp only [rel,yl,← pU,← nq,hdiv]
      have hc' : ∀ y∈points,rel (fun i=>(c i).divX) ∈
          Cm J (ZO y) := by
        intro y hy
        apply hreg k F y (hisol y hy)
        rw [hrel]
        exact hc y hy
      intro i
      simpa only [Polynomial.coeff_divX] using ih _ hc' i
  have hind:z7 k[X] (fun i=>(lV J (u i) :B)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hj:rel c∈J:= by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hm (i:Fin N) :lV J (pQ (c i)*u i) =
          c i•lV J (u i) := by
        rw [nq,← Mw ,zOY,
          ← VH]
      simpa only [rel,sI,hm] using hc
    have hl (y :Fin 4→k) (_:y∈points) :
        rel c∈Cm J (ZO y) :=zf _ hj
    ext n
    rw [Polynomial.coeff_zero]
    exact allCoeffs n c hl i
  let lift:B →ₗ[k[X]] L ⊗[k[X]] B:=TensorProduct.mk k[X] L B 1
  have hind' := hind.of_isLocalizedModule L (FQ (k[X])) lift
  have hJ:J.map (oy (aU k[X] L)) =
      DX (fun i=>bqz (F i)) :=bpr _ F
  let e :L ⊗[k[X]] B ≃ₐ[L] a90 F :=
    (aPw (k[X]) L J).trans (z9k L hJ)
  let:oz L (a90 F) :=hfinite
  let:oz L (L ⊗[k[X]] B) :=
    Ar e.symm.toLinearMap e.symm.surjective
  have hn:=hind'.fintype_card_le_finrank
  rw [e.toLinearEquiv.finrank_eq,Pf] at hn
  exact hn
private theorem c6T {k :Type} [c9 k] (y :Fin 4→k) :
  (wN y).IsMaximal :=
 VC (xI y) fun a =>
  ⟨pQ a,MvPolynomial.eval_C a⟩
private theorem fTD {k :Type} [c9 k] :
  p7 (wN (k :=k)) := by
 intro y z h
 funext i
 have hm:lI i-MvPolynomial.C (y i)∈wN y := by
  simp [wN,Xg]
 rw [h] at hm
 exact (sub_eq_zero.mp (by simpa [wN,Xg] using hm)).symm
private theorem cYs {k :Type} [c9 k] (I:lz (Affine k))
  (y :Fin 4→k) (hy :wN y∈I.minimalPrimes) :
  (Cm I (wN y)).radical=wN y := by
 let P:=wN y
 let S:=oY P
 let m:=aU (Affine k) S
 change ((I.map m).comap m).radical=P
 rw [← zBJ,
  GR S P I hy,
  Il]
 exact zUp
private theorem ezD (k :Type) [c9 k] (I:lz (Affine k))
    (points :n5 (Fin 4→k))
    (hisol : ∀ y∈points,wN y∈I.minimalPrimes)
    (hfinite : ∀ y∈points,oz k (Affine k ⧸ Cm I (wN y))) :
    oz k (Affine k ⧸ bfv I points) ∧
      pG k (Affine k ⧸ bfv I points) =
        ∑ y∈points,pG k (Affine k ⧸ Cm I (wN y)) := by
  classical
  let J (y : ↥points) :=Cm I (wN y.1)
  have hcoprime :Pairwise (fun x y=>IsCoprime (J x) (J y)) := by
    intro x y hxy
    rw [Ideal.isCoprime_iff_sup_eq,← Ideal.radical_eq_top,Ideal.radical_sup,
      cYs I x.1 (hisol x.1 x.2),
      cYs I y.1 (hisol y.1 y.2)]
    have hx :=c6T x.1
    have hy :=c6T y.1
    have hne :wN x.1≠wN y.1 :=
      fun h=>hxy (vH (fTD h))
    rw [hx.coprime_of_ne hy hne,Ideal.radical_top]
  let e : (Affine k ⧸ bfv I points) ≃ₐ[k] (∀ y : ↥points,Affine k ⧸ J y) :=
    { Ideal.quotientInfRingEquivPiQuotient J hcoprime with
      commutes' := fun _=>rfl }
  let : ∀ y : ↥points,oz k (Affine k ⧸ J y) := fun y=>hfinite y.1 y.2
  refine ⟨Ar e.symm.toLinearMap e.symm.surjective,?_⟩
  rw [e.toLinearEquiv.finrank_eq,Module.finrank_pi_fintype]
  exact zNb points
    (fun y=>pG k (Affine k ⧸ Cm I (wN y)))
private theorem dMT (hpoints :c1) (hreg:c2)
    (A:Fin 4→n5 pz)
    (hfinite :oz (fZ A) (HG A))
    (f :Fin 4→ gQ) (hs : ∀ i,(f i).support⊆A i) (points :n5 oe)
    (hisol : ∀ y∈points,oF y∈(ke f).minimalPrimes) :
    (∑ y∈points,(Ny (ke f) y).toNat) ≤
      pG (fZ A) (HG A) := by
  classical
  let k :=fZ A
  let F:=aMZ A f
  obtain ⟨hgen,hrank⟩:=ewS A f hs hfinite
  let mark (y :oe) :Fin 4→k := fun i=>aU cH k (y i)
  let points' := points.image mark
  have hzero : (fun i=>IS (F i)) =
      fun i=>oy (aU cH k) (f i) :=
    funext (dMS A f)
  let I:=DX (fun i=>IS (F i))
  let I₀:=DX (fun i=>oy (aU cH k) (f i))
  have hI:I=I₀:=ox DX hzero
  have hlocal (y :oe) (hy :y∈points) :
      wN (mark y)∈I.minimalPrimes ∧
      oz k (Affine k ⧸ Cm I (wN (mark y))) ∧
      pG k (Affine k ⧸ Cm I (wN (mark y))) =
        (Ny (ke f) y).toNat := by
    rw [hI]
    exact hpoints k f y (hisol y hy)
  have hiso' (y :Fin 4→k) (hy :y∈points') :wN y∈I.minimalPrimes := by
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy
    exact (hlocal z hz).1
  have hfin' (y :Fin 4→k) (hy :y∈points') :
      oz k (Affine k ⧸ Cm I (wN y)) := by
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy
    exact (hlocal z hz).2.1
  obtain ⟨hmarked,hlen⟩:=ezD k I points' hiso' hfin'
  have hinj:p7 mark := by
    intro y z h
    funext i
    exact (aU cH k).injective (Nr h i)
  rw [show points' = points.image mark from rfl,
    Finset.sum_image (fun _ _ _ _ h=>hinj h)] at hlen
  have hlength :
      (∑ y∈points,pG k (Affine k ⧸ Cm I (wN (mark y)))) =
        ∑ y∈points,(Ny (ke f) y).toNat :=
    vw rfl (fun y hy=>(hlocal y hy).2.2)
  have hbound:=ezE hreg k F points' hiso' hmarked hgen
  rwa [hlen,hlength,hrank] at hbound
theorem of_children (hpoints :c1) (hreg:c2) :VG.c2 := by
 intro p q H _ _ _ A hfinite f hs points hisol
 exact dMT hpoints hreg A hfinite f hs points hisol
end
end axi
end
section
namespace aA9
noncomputable section
open zP aaq
def c1 :Prop :=
  ∀ (A:Fin 4→n5 pz),(∀ i,0∈A i) →
    (∀ j:Fin 4,∃ i,vi j 1∈A i)→byY A
def c2 :Prop :=
  ∀ (A:Fin 4→n5 pz),(∀ i,0∈A i)→byY A →
    ∃ b:ℕ,∀ (i:Fin 4) (d:Degree),(∀ j,b≤d j) →
      ∀ p∈dO A (shift d i 1),p∈mo A (i.val+1) →
        ∃ r∈dO A d,p - ve A i*r∈mo A i.val
theorem of_children (hc:c1) (hg:c2) :VG.c3:= by
 apply VG.dDP
 apply aaq.of_children
 · exact fun _ hzero=>b4E hzero
 · exact fun _ hzero i p=>efX hzero i p
 · exact fun A hzero hcoords=>hg A hzero (hc A hzero hcoords)
end
end aA9
end
section
namespace bzN
open axi (Affine wN Cm)
open MvPolynomial
noncomputable section
variable {R:Type} [oD R]
private theorem bI9 (I P:lz R) [P.IsPrime] (x :R) :
  x∈Cm I P ↔ ∃ u∈P.primeCompl,u*x∈I :=
 zi P.primeCompl (oY P) I x
theorem cez {k :Type} [c9 k] (y :Fin 4→k) :
  (wN y).IsMaximal :=
 VC (eval y) fun a=>⟨C a,eval_C a⟩
private theorem dPC (I P:lz R) [P.IsPrime] (hP:P∈I.minimalPrimes) :
  (Cm I P).radical=P:= by
 let S:=oY P
 let m:=aU R S
 change ((I.map m).comap m).radical=P
 rw [← zBJ,GR S P I hP,
  Il]
 exact zUp
private theorem dN9 (I P:lz R) [P.IsPrime]
   (J:lz R) (hfg:J.FG) (hJ:J≤Cm I P) :
   ∃ u:P.primeCompl,ov { (u:R) } * J≤I:= by
 induction J,hfg using Submodule.fg_induction with
 | singleton x =>
   obtain ⟨u,hu,hux⟩:=(bI9 I P x).mp (hJ (Dz (by simp)))
   refine ⟨⟨u,hu⟩,?_⟩
   rwa [z9C,Qx]
 | sup J₁ J₂ _ _ ih₁ ih₂ =>
   obtain ⟨u,hu⟩:=ih₁ (le_sup_left.trans hJ)
   obtain ⟨v,hv⟩:=ih₂ (le_sup_right.trans hJ)
   refine ⟨u*v,?_⟩
   rw [Submonoid.coe_mul,← z9C,Ideal.mul_sup]
   apply sup_le
   · rw [t6 (ov {(u:R)}) (ov {(v :R)}),pU]
     exact Ideal.mul_le_right.trans' (Ideal.mul_mono vZ hu)
   · rw [pU]
     exact Ideal.mul_le_right.trans' (Ideal.mul_mono vZ hv)
private theorem gGZ {P Q:lz R} [P.IsMaximal] {n:ℕ}
  (hn:P^n≤Q) {u:R} (hu:u∉P) :
  wR (lV Q u) := by
 exact (Ideal.Quotient.isUnit_mk_pow_of_notMem (I:=P) (n:=n) hu).map (Av hn)
private theorem cM5 {k L:Type} [c9 k] [c9 L]
   (g:k →+* L) (y :Fin 4→k) :
   (eval (fun i=>g (y i))).comp (map g)=g.comp (eval y) := by
 apply t8
 · intro a
   simp
 · intro i
   simp
private theorem b8F {k L:Type} [c9 k] [c9 L]
    (g:k →+* L) (y :Fin 4→k) :
    (wN y).map (map g)=wN (fun i=>g (y i)) := by
  let Q:=(wN y).map (map g)
  let z :Fin 4→L:= fun i=>g (y i)
  refine wY (Ideal.map_le_iff_le_comap.mpr ?_) ?_
  · intro p hp
    change (eval y) p=0 at hp
    change eval z (map g p)=0
    exact (zk (cM5 g y) p).trans (by simp [hp])
  · have h:lV Q =
        ((lV Q).comp C).comp (eval z) := by
      apply t8
      · intro a
        simp
      · intro i
        change lV Q (lI i)=lV Q (C (eval z (lI i)))
        rw [eval_X,← sub_eq_zero,← uz ,zc]
        have hi:lI i - C (y i)∈wN y := by
          change eval y (lI i - C (y i))=0
          simp
        simpa [z] using zf (map g) hi
    intro p hp
    change eval z p=0 at hp
    change p∈Q
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [zk h p]
    simp [hp]
theorem dPB {k L:Type} [c9 k] [c9 L]
    (g:k →+* L) (y :Fin 4→k) (I:lz (Affine k))
    (hy :wN y∈I.minimalPrimes) :
    let P:=wN (fun i=>g (y i))
    P∈(I.map (map g)).minimalPrimes ∧
      Cm (I.map (map g)) P=(Cm I (wN y)).map (map g) := by
  classical
  let p:=wN y
  let P:=wN (fun i=>g (y i))
  let m:Affine k →+* Affine L:=map g
  let J:=I.map m
  let Q:=Cm I p
  let Q' := Q.map m
  let:P.IsMaximal:=cez (fun i=>g (y i))
  have hP:p.map m=P:=b8F g y
  have hrad:Q.radical=p:=dPC I p hy
  obtain ⟨n,hn⟩ : ∃ n:ℕ,p^n≤Q :=
    zK9 (le_of_eq hrad.symm) (Te _)
  have hpow:P^n≤Q' := by
    rw [← hP,← Iw]
    exact Pj hn
  have hQ:Q' ≤ P:= by
    rw [← hP]
    apply Pj
    exact hrad ▸ Ideal.le_radical
  have hJ:J≤Q' := Pj (fun _ hx=>zf _ hx)
  obtain ⟨u,hu⟩:=dN9 I p Q (Te _) vZ
  have huP:m (u:Affine k)∈P.primeCompl:= by
    have hu0:eval y (u:Affine k)≠0:=u.prop
    change eval (fun i=>g (y i)) (m (u:Affine k))≠0
    rw [show eval (fun i=>g (y i)) (m (u:Affine k))=g (eval y (u:Affine k)) from
      zk (cM5 g y) (u:Affine k)]
    exact fun h=>hu0 (g.injective (h.trans (qm g).symm))
  have heq :Cm J P= Q' := by
    refine wY ?_ ?_
    · intro x hx
      obtain ⟨v,hv,hvx⟩:=(bI9 J P x).mp hx
      have hzero :lV Q' v* lV Q' x=0:= by
        rw [← nq,zc]
        exact hJ hvx
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        ((gGZ hpow hv).mul_left_cancel (hzero.trans (vj _).symm))
    · intro x hx
      apply (bI9 J P x).mpr
      refine ⟨m (u:Affine k),huP,?_⟩
      have hu' := Pj (f :=m) hu
      rw [Ideal.map_mul,uJ,Gj] at hu'
      exact hu' (Ideal.mul_mem_mul (Dz (by simp)) hx)
  refine ⟨⟨⟨xm,hJ.trans hQ⟩,?_⟩,heq⟩
  intro T hT hTP x hx
  apply hT.1.mem_of_pow_mem n
  apply (show Q' ≤ T from ?_) (hpow (Zt hx n))
  intro v hv
  have hv' : v∈Cm J P:=heq.symm ▸ hv
  obtain ⟨w,hw,hwv⟩:=(bI9 J P v).mp hv'
  exact (hT.1.mem_or_mem (hT.2 hwv)).resolve_left (fun hwT=>hw (hTP hwT))
end
end bzN
end
section
namespace bzO
open axi
open Ideal IsLocalRing MvPolynomial RingTheory.Sequence
open scoped Pointwise Polynomial
private noncomputable abbrev parameter (k :Type) [oD k] :Family k :=
 pQ mD
private theorem cw3 {k :Type} [c9 k] (v :Affine k) :
  IS (oy lJ v)=v :=
 MvPolynomial.map_leftInverse (fun _:k=>zFf) v
private theorem bQa {k :Type} [c9 k] :
  u5 (IS (k :=k)) :=
 fun v=>⟨oy lJ v,cw3 v⟩
private theorem cWC {k :Type} [c9 k] :
    sS (IS (k :=k))=ov {parameter k} := by
  classical
  apply wY
  · intro f hf
    have hz :IS f=0:=hf
    have hx (m:Fin 4 →₀ ℕ) :mD *(f.coeff m).divX=f.coeff m:= by
      have he : (f.coeff m).coeff 0=0:= by
        rw [zTt]
        have hh:=ox (fun p:Affine k=>p.coeff m) hz
        simpa only [IS,MvPolynomial.coeff_map,AddMonoidAlgebra.coeff_zero,
          Finsupp.zero_apply,Polynomial.coe_evalRingHom] using hh
      simpa only [he,Polynomial.C_0,zS] using zQv (f.coeff m)
    rw [QL]
    refine ⟨∑ m∈f.support,Kz m (f.coeff m).divX,?_⟩
    simp only [parameter,yl,Wl,hx,
      MvPolynomial.support_sum_monomial_coeff]
  · rw [Qx ,Xg]
    simp [parameter,IS]
private theorem a9t {k :Type} [c9 k] {s :Set (Fin 4)} {i:Fin 4}
  (hi:i∉s) (p:Affine k)
  (hp:lI i*p∈span (lI '' s)) :
  p∈span (lI '' s) := by
 rw [mem_ideal_span_X_image] at hp ⊢
 intro m hm
 have hcoeff :=coeff_X_mul m i p
 have hmem:vi i 1+m∈(lI i*p).support :=
  mem_support_iff.mpr (hcoeff.trans_ne (mem_support_iff.mp hm))
 obtain ⟨j,hj,hne⟩:=hp _ hmem
 have hij:i≠j:= fun e=>hi (e.symm ▸ hj)
 exact ⟨j,hj,by simpa [Cy ,Kc,hij] using hne⟩
private noncomputable abbrev coord (k :Type) [c9 k] :Fin 4→Affine k :=
 lI
private theorem a9u (k :Type) [c9 k] :
   FV (Affine k) (sH (coord k)) := by
 classical
 refine ⟨?_⟩
 intro n hn
 have hn' : n<4 := by simpa using hn
 let s :Set (Fin 4) := {j | j.val<n}
 have hprev :zh ((sH (coord k)).take n) •
     (⊤ : Kl (Affine k) (Affine k))=span (coord k '' s) := by
   rw [G5 ,G2 ,← zKJ hn'.le]
   apply ox (ov :Set (Affine k)→ lz (Affine k))
   ext p
   change p∈sH (Fin.take n hn'.le (coord k))↔p∈coord k '' s
   rw [List.mem_ofFn]
   exact ⟨fun ⟨j,hj⟩=>⟨Fin.castLE hn'.le j,j.isLt,hj⟩,
     fun ⟨j,hj,he⟩=>⟨⟨j.val,hj⟩,he⟩⟩
 rw [hprev]
 simpa only [Z0] using
   (zHO (span (coord k '' s))
     (coord k ⟨n,hn'⟩)).mpr
     (a9t (s :=s) (i:=⟨n,hn'⟩) (Nat.lt_irrefl n))
private noncomputable def translation {k :Type} [c9 k] (y :Fin 4→k) :
  Affine k ≃ₐ[k] Affine k :=
 zp6 (oZ (fun i=>coord k i - C (y i)))
  (oZ (fun i=>coord k i+C (y i)))
  (Kh (fun i=> by simp [coord]))
  (Kh (fun i=> by simp [coord]))
private theorem gDT {k :Type} [c9 k] (y :Fin 4→k) :
   FV (Affine k) (sH fun i=>coord k i - C (y i)) := by
 let e :=(translation y).toRingEquiv
 let rs :=sH (coord k)
 have hcongr :Ye (fun (r s :Affine k) => ∀ x :Affine k,e (r•x)=s•e x)
     rs (rs.map e) :=
   List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x=>e.map_mul r x)
 have hwr :=(e.toAddEquiv.isWeaklyRegular_congr hcongr).mp (a9u k)
 simpa [rs,e,translation,coord,List.map_ofFn,zQM] using hwr
private theorem buP {k :Type} [c9 k] (y :Fin 4→k) :
    ∃ rs :List (oY (ZO y)),rs.length=5 ∧
      (∀ a∈rs,a∈qz (oY (ZO y))) ∧
      IsRegular (oY (ZO y)) rs := by
  let P:=ZO y
  let R:=oY P
  let ι:=aU (Family k) R
  let d:Fin 4→Family k := fun i=>oy lJ (coord k i - C (y i))
  let rs :=sH d
  let I:lz (Family k) :=parameter k•(⊤ : Kl (Family k) (Family k))
  have hI:I=sS (IS (k :=k)) := by
    change parameter k•(⊤ : Kl (Family k) (Family k))= _
    rw [← Submodule.ideal_span_singleton_smul,G5 ,G2 ,cWC]
  let e :Family k ⧸ I ≃+* Affine k :=
    (zC3 hI).trans
      (zJi bQa)
  have he (x :Family k) :e (lV I x)=IS x := by
    change (zJi bQa)
      (zC3 hI (lV I x))= _
    rw [Ideal.quotEquivOfEq_mk,RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hcongr :Ye (fun (r :Family k) (s :Affine k) =>
      ∀ x :Family k ⧸ I,e (r•x)=s•e x) rs (rs.map IS) := by
    refine List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun a _ x => ?_)
    obtain ⟨z,rfl⟩:=uh x
    change e (lV I (a*z))=IS a*e (lV I z)
    rw [he,he,nq]
  have hzero :rs.map IS=sH (fun i=>coord k i - C (y i)) := by
    simp only [rs,List.map_ofFn,zQM,d,cw3]
  have hreg:FV (Family k) (parameter k :: rs) := by
    rw [isWeaklyRegular_cons_iff]
    constructor
    · have ht:parameter k≠0:= fun h=>Polynomial.X_ne_zero
        (MvPolynomial.C_injective (Fin 4) k[X] (h.trans (qm pQ).symm))
      exact mul_right_injective₀ ht
    · change FV (Family k ⧸ I) rs
      apply (e.toAddEquiv.isWeaklyRegular_congr hcongr).mpr
      rw [hzero]
      exact gDT y
  have hm (x :Family k) (hx :x∈parameter k :: rs) :x∈P:= by
    rcases List.mem_cons.mp hx with rfl | hx
    · change xI y (IS (parameter k))=0
      simp [parameter,IS]
    · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
      change xI y
        (IS (oy lJ (coord k i - C (y i))))=0
      rw [cw3]
      simp [coord]
  refine ⟨(parameter k :: rs).map ι,by simp [rs],?_,
    hreg.isRegular_of_isLocalization_of_mem R P hm⟩
  intro x hx
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hx
  exact (Nq R P w).mpr (hm w hw)
theorem proof :axi.c2 := by
 classical
 intro k _ F y hmin r hr
 let P:=ZO y
 let R:=oY P
 let ι:=aU (Family k) R
 let J:=DX F
 let front:=sH fun i=>ι (F i)
 let t:=ι (parameter k)
 have hmap :J.map IS=DX (fun i=>IS (F i)) :=
   bpr _ F
 have hP:P∈(J ⊔ span {parameter k}).minimalPrimes := by
   have h:=Ideal.minimalPrimes_comap_of_surjective bQa (hmap.symm ▸ hmin)
   rw [SW _ bQa J,
     ← Un,cWC] at h
   exact h
 have hfront:zh front=J.map ι:= by
   change zh front=(span (vk F)).map ι
   rw [uJ,← RJ]
   exact ox span (Set.ext (UP (fun i=>ι (F i))))
 have hfull:zh (front ++ [t]) =
     (J ⊔ span {parameter k}).map ι:= by
   rw [Ideal.ofList_append,Ideal.ofList_singleton,hfront,II,
     uJ,Gj]
 have hrad: (zh (front ++ [t])).radical=qz R:= by
   rw [hfull,GR R P _ hP]
   exact Il
 obtain ⟨rs,hlen,hm,hreg⟩:=buP y
 have hparams :=bPS rs (front ++ [t])
   (by simpa [front] using hlen) hm hreg hrad
 have hlast :=((isWeaklyRegular_append_iff R front [t]).mp hparams).2
 have hc:=(isWeaklyRegular_singleton_iff _ _).mp hlast
 rw [G5 ,G2 ,hfront] at hc
 change ι r∈J.map ι
 apply zXB hc
 change t*ι r∈J.map ι
 rw [← nq]
 exact hr
end bzO
end
section
namespace baw
noncomputable section
open aR lB XU VG
open zP (TX LK)
open E6 (rU)
open scoped BigOperators Pointwise
theorem aOM (p:nI) (x :QC) :
  x∈nD p↔(∀ i,0≤x i)∧x 0 + x 1 + x 2 + x 3≤p.b ∧
    x 1+2*x 2 + 3*x 3≤p.j∧x 3≤p.t:= by
 norm_num [nD,x7]
theorem mem_support (p:nI) (e :t5) :
  e∈PS p↔(fun i=>e i)∈rU (p.scale 2) := by
 simp [VG.dM,rU,x7]
private theorem support_zero : (↑(PS ⟨0,0,0⟩) :Set t5)=0:= by
 ext e
 rw [Finset.mem_coe,mem_support]
 change (fun i=>e i)∈rU ⟨0,0,0⟩↔_
 rw [E6.bFF,Set.mem_singleton_iff,Set.mem_zero]
 exact ⟨fun h=>Finsupp.ext (Nr h),fun h=> by subst e; rfl⟩
private theorem dgi {p q:nI} (hp:bF p) (hq:bF q) :
   (↑(PS (p.plus q)) :Set t5) =
     (↑(PS p) :Set t5)+(↑(PS q) :Set t5) := by
 ext e
 rw [Finset.mem_coe,mem_support]
 rw [show (p.plus q).scale 2=(p.scale 2).plus (q.scale 2) by
   cases p
   cases q
   simp [yL,p9,Qy]]
 rw [E6.cNP _ _
   (xu hp 2) (xu hq 2)
   (by simp [p9]) (by simp [p9]) (by simp [p9])]
 constructor
 · rintro ⟨u,hu,v,hv,he⟩
   refine ⟨Finsupp.equivFunOnFinite.symm u,(mem_support _ _).mpr hu,
     Finsupp.equivFunOnFinite.symm v,(mem_support _ _).mpr hv,?_⟩
   ext i
   exact Nr he i
 · rintro ⟨u,hu,v,hv,rfl⟩
   exact ⟨fun i=>u i,(mem_support _ _).mp hu,fun i=>v i,(mem_support _ _).mp hv,rfl⟩
private theorem bhH {p:nI} (hp:bF p) (n:ℕ) :
    (↑(PS (p.scale n)) :Set t5)=n•(↑(PS p) :Set t5) := by
  induction n with
  | zero=>simpa [Shape.scale] using
      support_zero.trans (zero_smul ℕ (↑(PS p) :Set t5)).symm
  | succ n ih =>
      rw [show p.scale (n+1)=(p.scale n).plus p by
        cases p
        simp [p9,yL,Ts]]
      rw [dgi (xu hp n) hp,ih,succ_nsmul]
def ku (S:n5 (Fin 4)) (B:Fin 4→nI) :Shape :=
 ⟨∑ i∈S,(B i).b,∑ i∈S,(B i).j,∑ i∈S,(B i).t⟩
theorem awr {B:Fin 4→nI} (hB : ∀ i,bF (B i)) (S:n5 (Fin 4)) :
   bF (ku S B) := by
 constructor
 · exact wB fun i _=>(hB i).1
 · simp only [ku,yl]
   exact wB fun i _=>(hB i).2
private theorem ddH {S:n5 (Fin 4)} {i:Fin 4} (hi:i∉S)
  (B:Fin 4→nI) :
  ku (EP i S) B=(B i).plus (ku S B) := by
 simp [ku,yL,z8 hi]
private theorem support_sum (B:Fin 4→nI) (hB : ∀ i,bF (B i)) (S:n5 (Fin 4)) :
    (∑ i∈S,(↑(PS (B i)) :Set t5)) =
      (↑(PS (ku S B)) :Set t5) := by
  induction S using Df with
  | empty=>simpa [ku] using support_zero.symm
  | @insert i S hi ih =>
      rw [z8 hi,ih,ddH hi,
        dgi (hB i) (awr hB S)]
theorem dzz (B:Fin 4→nI) (hB : ∀ i,bF (B i)) (S:n5 (Fin 4)) :
    (∑ i∈S,LK (PS (B i)))=nD ((ku S B).scale 2) := by
  induction S using Df with
  | empty=>simpa [ku,Shape.scale,← Set.singleton_zero] using aTp.symm
  | @insert i S hi ih =>
      rw [z8 hi,ih,bry _ (hB i),ddH hi]
      rw [show ((B i).plus (ku S B)).scale 2 =
          ((B i).scale 2).plus ((ku S B).scale 2) by
        cases B i
        cases ku S B
        simp [yL,p9,Qy]]
      exact (cDV _ _
        (xu (hB i) 2)
        (xu (awr hB S) 2)).symm
private theorem gpZ (B:Fin 4→nI) (b n:ℕ) (S:n5 (Fin 4)) :
   ku t9 (fun i=>(B i).scale (uW b n S i)) =
     ((ku S B).scale n).plus ((ku t9 B).scale b) := by
 classical
 have split_sum (f :Fin 4→ℕ) :
     (∑ i,uW b n S i*f i)=n*(∑ i∈S,f i)+b*(∑ i,f i) := by
   simp only [uW,Ts ,ite_mul,Nat.zero_mul,vG,yl]
   rw [← zLJ,zuy,Zh,add_comm]
 unfold ku p9 yL
 rw [split_sum,split_sum,split_sum]
theorem d5e (B:Fin 4→nI) (hB : ∀ i,bF (B i)) (b n:ℕ)
   (S:n5 (Fin 4)) :
   TX (fun i=>PS (B i)) (uW b n S) =
     (PS (((ku S B).scale n).plus ((ku t9 B).scale b))).card:= by
 unfold TX
 simp_rw [← bhH (hB _) _]
 rw [support_sum _ (fun i=>xu (hB i) _),
   gpZ,Du]
end
end baw
end
section
namespace bjD
open wH Tx XU
open VG (MZ)
open aqa (K7)
open Ideal IsLocalRing MvPolynomial RingTheory.Sequence
open scoped Pointwise
private noncomputable abbrev coord:Fin 4→ gQ:=lI
private theorem a9t {s :Set (Fin 4)} {i:Fin 4} (hi:i∉s)
  (p:gQ) (hp:coord i*p∈span (coord '' s)) :p∈span (coord '' s) := by
 rw [mem_ideal_span_X_image] at hp ⊢
 intro m hm
 have hcoeff :=coeff_X_mul m i p
 have hmem:vi i 1+m∈(coord i*p).support :=
  mem_support_iff.mpr (hcoeff.trans_ne (mem_support_iff.mp hm))
 obtain ⟨j,hj,hne⟩:=hp _ hmem
 have hij:i≠j:= fun e=>hi (e.symm ▸ hj)
 exact ⟨j,hj,by simpa [Cy ,Kc,hij] using hne⟩
private theorem a9u:FV gQ (sH coord) := by
 classical
 refine ⟨?_⟩
 intro n hn
 have hn' : n<4 := by simpa using hn
 let s :Set (Fin 4) := {j | j.val<n}
 have hprev :zh ((sH coord).take n)•(⊤ : Kl gQ gQ) =
     span (coord '' s) := by
   rw [G5 ,G2 ,← zKJ hn'.le]
   apply ox (ov :Set gQ→ lz gQ)
   ext p
   change p∈sH (Fin.take n hn'.le coord)↔p∈coord '' s
   rw [List.mem_ofFn]
   constructor
   · rintro ⟨j,rfl⟩
     exact ⟨Fin.castLE hn'.le j,j.isLt,rfl⟩
   · rintro ⟨j,hj,rfl⟩
     exact ⟨⟨j.val,hj⟩,rfl⟩
 rw [hprev]
 simpa only [Z0] using
   (zHO (span (coord '' s)) (coord ⟨n,hn'⟩)).mpr
     (a9t (s :=s) (i:=⟨n,hn'⟩) (Nat.lt_irrefl n))
private noncomputable def translation (y :oe) :gQ ≃ₐ[cH] gQ :=
 zp6 (oZ (fun i=>coord i - C (y i))) (oZ (fun i=>coord i+C (y i)))
  (Kh (fun i=> by simp))
  (Kh (fun i=> by simp))
private theorem buP (y :oe) :
   ∃ rs :List (MZ y),rs.length=4 ∧
     (∀ a∈rs,a∈qz (MZ y))∧IsRegular (MZ y) rs := by
 let e :=(translation y).toRingEquiv
 let rs :=sH coord
 let p:=(yo y).asIdeal
 have hcongr :Ye (fun (r s :gQ) => ∀ x :gQ,e (r•x)=s•e x)
     rs (rs.map e) :=
   List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x=>e.map_mul r x)
 have hwr :FV gQ (rs.map e) :=
   (e.toAddEquiv.isWeaklyRegular_congr hcongr).mp a9u
 have hm (x :gQ) (hx :x∈rs.map e) :x∈p:= by
   obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hx
   obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hw
   change xI y (oZ (fun j=>coord j - C (y j)) (coord i))=0
   simp [coord]
 refine ⟨(rs.map e).map (algebraMap gQ (MZ y)),by simp [rs],?_,
   hwr.isRegular_of_isLocalization_of_mem (MZ y) p hm⟩
 intro x hx
 obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hx
 exact (Nq (MZ y) p w).mpr (hm w hw)
theorem proof :VG.c1 := by
 classical
 intro y g hrad i x hx
 let R:=MZ y
 let _:oq cH R :=
   ((aU gQ R).comp (aU cH gQ)).toAlgebra
 let e :=Equiv.swap (u8 3) i
 have hei:e (u8 3)=i:=Equiv.swap_apply_left _ _
 let f :Fin 4→R:=g ∘ e
 let front:List R:=sH fun j:Fin 3=>f j.castSucc
 have hfull:zh (sH f)=span (vk g) := by
   rw [← EquivLike.range_comp g e]
   exact ox span (Set.ext (UP f))
 have hfront:zh front=K7 g i:= by
   unfold K7
   apply ox (ov :Set R→ lz R)
   ext z
   change z∈sH (fun j:Fin 3=>f j.castSucc)↔z∈g '' {j | j≠i}
   rw [UP (fun j:Fin 3=>f j.castSucc)]
   constructor
   · rintro ⟨j,rfl⟩
     exact ⟨e j.castSucc,fun h=>zm4 j (e.injective (h.trans hei.symm)),rfl⟩
   · rintro ⟨j,hj,rfl⟩
     obtain ⟨l,rfl⟩:=e.surjective j
     rcases Fin.eq_castSucc_or_eq_last l with ⟨m,rfl⟩ | rfl
     · exact ⟨m,rfl⟩
     · exact (hj hei).elim
 obtain ⟨rs,hlen,hmem,hreg⟩:=buP y
 have hparams :=bPS (k :=cH) rs (sH f)
   (by simpa using hlen) hmem hreg (hfull ▸ hrad)
 rw [List.ofFn_succ',List.concat_eq_append] at hparams
 have hlast :=((isWeaklyRegular_append_iff R front [f (u8 3)]).mp hparams).2
 have hc:=(isWeaklyRegular_singleton_iff _ _).mp hlast
 rw [G5 ,G2 ,hfront] at hc
 exact zXB hc
   (by simpa only [f,RD,hei,v8] using hx)
end bjD
end
section
namespace bzN
open wH (cH)
open Tx (gQ oe)
open yz (oF Ny)
open zP (ke)
open axi (Affine wN DX Cm aPw)
open MvPolynomial IsLocalRing
open scoped TensorProduct
noncomputable section
private def exv (k :Type) [c9 k] (I:lz (Affine k))
   (y :Fin 4→k) (hy :wN y∈I.minimalPrimes) :
   let P:=wN y
   let S:=oY P
   (Affine k ⧸ Cm I P) ≃ₐ[k] S ⧸ I.map (aU (Affine k) S) := by
 let P:=wN y
 let S:=oY P
 let J:=I.map (aU (Affine k) S)
 let Q:=Cm I P
 let:P.IsMaximal:=cez y
 let a :=zE2 k (Affine k) S
 let φ:Affine k ⧸ Q →ₐ[k] S ⧸ J:=Ideal.quotientMapₐ J a vZ
 refine AlgEquiv.ofBijective φ ⟨zmq,?_⟩
 obtain ⟨n,hn⟩ : ∃ n:ℕ,qz S^n≤J:= by
   apply zK9 _ (Ideal.fg_of_isNoetherianRing _)
   rw [show J.radical=P.map (aU (Affine k) S) from
     GR S P I hy,
     Il]
 intro b
 obtain ⟨b,rfl⟩:=uh b
 obtain ⟨x,hx⟩:=(IsLocalization.AtPrime.equivQuotMaximalIdealPow P S n).surjective
   (lV (qz S^n) b)
 obtain ⟨x,rfl⟩:=uh x
 rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk] at hx
 exact ⟨lV Q x,ox (Av hn) hx⟩
private theorem fWW (k :Type) [c9 k] (y :Fin 4→k) :
   Au (FR k) (FR (oY (wN y)))=1 := by
 let P:=wN y
 let S:=oY P
 let:P.IsMaximal:=cez y
 let e :=zx7 P S
 have hs :u5 (aU k (FR S)) := by
   intro z
   obtain ⟨a,ha⟩:=e.surjective z
   obtain ⟨a,rfl⟩:=uh a
   have hc:lV P (C (eval y a))=lV P a := by
     apply Ideal.Quotient.eq.mpr
     change eval y (C (eval y a)-a)=0
     simp
   refine ⟨eval y a,?_⟩
   rw [← ha,← hc,show e=zx7 P S from rfl,
     IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
     Ee k S (FR S),
     Ee k (Affine k) S,Mw]
   rfl
 have hs' : u5 (aU (FR k) (FR S)) := by
   intro z
   obtain ⟨a,ha⟩:=hs z
   exact ⟨residue k a,ha⟩
 rw [zAi hs',Module.length_eq_one]
private theorem eIh (I:lz gQ) (y :oe) (hy :oF y∈I.minimalPrimes) :
   let Q:=Cm I (wN y)
   oz cH (gQ ⧸ Q) ∧
     pG cH (gQ ⧸ Q)=(Ny I y).toNat := by
 let k :=cH
 let P:=wN y
 let S:=oY P
 let J:=I.map (aU gQ S)
 let Q:=Cm I P
 have hP:oF y=P:=VG.bKz y
 have hy' : P∈I.minimalPrimes :=hP ▸ hy
 let e : (gQ ⧸ Q) ≃ₐ[k] S ⧸ J:=exv k I y hy'
 have hpoint :Ny I y=Au S (S ⧸ J) := by
   rw [VG.a6E]
   rfl
 have hlen:Au k (S ⧸ J)=Ny I y := by
   rw [IsLocalRing.length_restrictScalars k S,fWW k y,mul_one,hpoint]
 have hfin:Au k (S ⧸ J) ≠ ⊤ := by
   rw [hlen,VG.a6E]
   exact VG.c4j hy'
 let:IsNoetherian k (S ⧸ J) :=
   (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hfin)).1
 let:oz k (S ⧸ J) :=⟨Te _⟩
 refine ⟨Ar e.symm.toLinearMap e.symm.surjective,?_⟩
 rw [e.toLinearEquiv.finrank_eq,← hlen,Zg ,zzq]
theorem proof :axi.c1 := by
 intro k _ _ f y hy
 let K:=cH
 let P:=wN y
 let Q:=Cm (ke f) P
 let m:Affine K →+* Affine k :=map (aU K k)
 have hP:oF y=P:=VG.bKz y
 have hp:P∈(ke f).minimalPrimes :=hP ▸ hy
 have hi: (ke f).map m=DX (fun i=>m (f i)) :=
  axi.bpr _ f
 obtain ⟨hmin,hQ⟩:=dPB (aU K k) y (ke f) hp
 change _∈((ke f).map m).minimalPrimes at hmin
 rw [hi] at hmin hQ
 obtain ⟨hfin,hlen⟩:=eIh (ke f) y hy
 let:oz K (Affine K ⧸ Q) :=hfin
 let e :k ⊗[K] (Affine K ⧸ Q) ≃ₐ[k] Affine k ⧸ Q.map m:=aPw K k Q
 refine ⟨hmin,?_⟩
 rw [hQ]
 exact ⟨Ar e.toLinearMap e.surjective,
  e.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_baseChange.trans hlen)⟩
end
end bzN
end
section
namespace baw
noncomputable section
open aR lB XU VG
open Filter MeasureTheory Set
open scoped BigOperators ENNReal Function Pointwise Topology
private def PN (e :t5) :Set QC :=
 Set.pi Set.univ fun i=>Set.Ico (e i:ℝ) ((e i:ℝ)+1)
private def Ax (p:nI) :Set QC :=
 ⋃ e∈PS p,PN e
private theorem dGn:Pairwise (Lf on PN) := by
 intro e f hef
 refine Set.disjoint_left.mpr fun x hx hy=>hef (Finsupp.ext fun i => ?_)
 exact (zrg (e i) _ (hx i (Mk i))).symm.trans
  (zrg (f i) _ (hy i (Mk i)))
private theorem cvk (p:nI) :oj (Ax p)=(PS p).card:= by
 unfold Ax
 rw [measure_biUnion_finset (fun _ _ _ _ h=>dGn h)]
 · have hcell (e :t5) :oj (PN e)=1 := by
     simp [PN,zEj]
   simp [hcell]
 · intro e _
   exact MeasurableSet.pi Set.countable_univ fun _ _=>zQD
private theorem bWp (p:nI) :nD (p.scale 2)⊆Ax p:= by
  intro x hx
  obtain ⟨hx₀,hxb,hxj,hxt⟩:=(aOM _ _).mp hx
  let e :Exponent:=Finsupp.equivFunOnFinite.symm fun i => ⌊x i⌋₊
  have hle (i:Fin 4) : (e i:ℝ)≤x i:=Sv (hx₀ i)
  have hmem:e∈PS p:= by
    apply (mem_support p e).mpr
    change e 0+e 1+e 2+e 3≤(p.scale 2).b ∧
      e 1+2*e 2 + 3*e 3≤(p.scale 2).j∧e 3≤(p.scale 2).t
    refine ⟨?_,?_,?_⟩
    · exact_mod_cast (show (e 0:ℝ)+e 1+e 2+e 3≤(p.scale 2).b by
        linarith [hle 0,hle 1,hle 2,hle 3])
    · exact_mod_cast (show (e 1 :ℝ)+2*e 2 + 3*e 3≤(p.scale 2).j by
        linarith [hle 1,hle 2,hle 3])
    · exact_mod_cast (hle 3).trans hxt
  exact Set.mem_iUnion₂.mpr ⟨e,hmem,fun i _=>⟨hle i,Rm (x i)⟩⟩
private theorem bWE (p:nI) :
  Ax p⊆nD ((p.scale 2).plus ⟨6,6,1⟩) := by
 intro x hx
 obtain ⟨e,he,hx⟩:=Set.mem_iUnion₂.mp hx
 obtain ⟨heb,hej,het⟩ :
    e 0+e 1+e 2+e 3≤(p.scale 2).b ∧
    e 1+2*e 2 + 3*e 3≤(p.scale 2).j∧e 3≤(p.scale 2).t :=
  (mem_support p e).mp he
 have hb: (e 0:ℝ)+e 1+e 2+e 3≤(p.scale 2).b:= by exact_mod_cast heb
 have hj: (e 1 :ℝ)+2*e 2 + 3*e 3≤(p.scale 2).j:= by exact_mod_cast hej
 have ht: (e 3:ℝ)≤(p.scale 2).t:= by exact_mod_cast het
 have h (i:Fin 4) : (e i:ℝ)≤x i∧x i<(e i:ℝ)+1 :=hx i (Mk i)
 apply (aOM _ _).mpr
 refine ⟨fun i=>(zm _).trans (h i).1,?_,?_,?_⟩ <;>
  simp only [yL,GB,C9,RP] <;>
  linarith [(h 0).2,(h 1).2,(h 2).2,(h 3).2]
private theorem dFe (p:nI) :oj (nD p) ≠ ∞ := by
 have hsubset :nD p⊆Set.Icc (0:QC) (fun _=>(p.b:ℝ)) := by
  intro x hx
  refine ⟨hx.1,fun i => ?_⟩
  exact (zfK (fun j _=>hx.1 j) (Finset.mem_univ i)).trans hx.2.1
 refine ne_top_of_le_ne_top ?_ (Bf hsubset)
 rw [zk7]
 exact ENNReal.prod_ne_top fun _ _=>Up
private theorem cIq (p:nI) :
    (oj (nD (p.scale 2))).toReal≤(PS p).card ∧
      ((PS p).card:ℝ) ≤
        (oj (nD ((p.scale 2).plus ⟨6,6,1⟩))).toReal:= by
  have hlo:=Bf (μ:=oj) (bWp p)
  have hhi:=Bf (μ:=oj) (bWE p)
  rw [cvk] at hlo hhi
  exact ⟨by simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hlo,
    by simpa using LO  (dFe _) hhi⟩
private def biC (b j t:ℝ) :ℝ :=
 (8*b*j^2*t - 24*b*j*t^2+24*b*t^3-4*j^3*t+14*j^2*t^2 - 20*j*t^3+9*t^4)/32
private theorem cD7 (p:nI) (hp:bF p) :
  (oj (nD p)).toReal=biC p.b p.j p.t:= by
 have h:=bRF.proof p hp
 change 32*(oj (nD p)).toReal=(Dn p:ℝ) at h
 rw [show (oj (nD p)).toReal=(Dn p:ℝ)/32 by linarith]
 unfold Dn biC
 push_cast
 rfl
private theorem dg3 (p u:nI) (hp:bF p) (hu:bF u) :
   th (fun n:ℕ=>(oj (nD ((p.scale n).plus u))).toReal/(n:ℝ)^4)
     atTop (𝓝 (volume (nD p)).toReal) := by
 let f (r :ℝ) :=
   biC (p.b+u.b*r) (p.j+u.j*r) (p.t+u.t*r)
 have hf :Continuous f := by
   unfold f biC
   fun_prop
 have hi:th (fun n:ℕ=>(n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
   tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
 rw [cD7 p hp,show biC p.b p.j p.t=f 0 by simp [f]]
 refine ((hf.tendsto 0).comp hi).congr' ?_
 filter_upwards [Kp (1 :ℕ)] with n hn
 have hn' : (n:ℝ)≠0:= by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
 rw [cD7 _ (E6.Nc (xu hp _) hu)]
 change f (n:ℝ)⁻¹= _
 simp only [f,p9,yL,GB,zd ,biC]
 field_simp
theorem gAT (p u:nI) (hp:bF p) (hu:bF u) :
   th (fun n:ℕ=>((PS ((p.scale n).plus u)).card:ℝ)/(n:ℝ)^4)
     atTop (𝓝 (volume (nD (p.scale 2))).toReal) := by
 have hshape (n:ℕ) : ((p.scale n).plus u).scale 2=((p.scale 2).scale n).plus (u.scale 2) := by
   cases p
   cases u
   simp [p9,yL,Qy ,Nat.mul_left_comm]
 have hp₂:=xu hp 2
 have hu₂:=xu hu 2
 have hpadding:bF (⟨6,6,1⟩:nI) := by norm_num [bF]
 have hplus (a b c:nI) : (a.plus b).plus c=a.plus (b.plus c) := by
   cases a
   cases b
   cases c
   simp [yL,Vq]
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le
   (dg3 _ _ hp₂ hu₂)
   (dg3 _ _ hp₂ (E6.Nc hu₂ hpadding))
   (fun n => ?_) (fun n => ?_)
 · exact div_le_div_of_nonneg_right (by simpa only [hshape] using (cIq ((p.scale n).plus u)).1)
     (by positivity)
 · exact zrZ
     (by simpa only [hshape,hplus] using (cIq ((p.scale n).plus u)).2)
     (by positivity)
end
end baw
end
section
namespace baw
open aR lB VG
open zP (TX LK)
open Filter MeasureTheory
open scoped BigOperators Pointwise Topology
theorem proof :VG.c4 := by
 intro p q H hp hq hH b S
 let B:Fin 4→Shape := ![p,q,q,H]
 have hB (i:Fin 4) :bF (B i) := by
  fin_cases i <;> assumption
 have hA:Eb p q H=fun i=>PS (B i) := by
  funext i
  fin_cases i <;> rfl
 change th (fun n:ℕ=>(TX (Eb p q H) (uW b n S) :ℝ)/(n:ℝ)^4)
  atTop (𝓝 (volume (∑ i∈S,LK (Eb p q H i))).toReal)
 simp_rw [hA,d5e B hB b,dzz B hB S]
 exact gAT _ _ (awr hB S)
  (xu (awr hB t9) b)
end baw
end
section
namespace aiI
noncomputable section
open aR
open scoped BigOperators
private theorem arA (P:Symbol) :
  acO P=vh Fin.val P:= by
 unfold acO vh
 simp only [zDM,v8 ,Nat.mul_comm]
end
end aiI
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 8
namespace aqb
noncomputable section
open cu gT pI Polynomial
theorem cDR {R:Type*} [oD R] {M:lz R} {f a :R} {n:ℕ}
  (hM:M=ov {f}) (hf :p7 (fun x :R=>f*x))
  (h:f*a∈M^(n+1)) :a∈M^n:= by
 rw [FK,show M*M^n=ov {f} * M^n from ox (· * M^n) hM] at h
 obtain ⟨b,hb,he⟩:=Ideal.mem_span_singleton_mul.mp h
 exact (hf he) ▸ hb
private theorem eNl {R:Type*} [oD R] {M F T:lz R}
    (hM:M=F ⊔ T) (n:ℕ) :M^(n+1)≤F*M^n ⊔ T^(n+1) := by
  induction n with
  | zero=>simpa using hM.le
  | succ n ih =>
    have hTM:T≤M:=hM ▸ le_sup_right
    calc
      M^(n+1+1)=(F ⊔ T)*M^(n+1) := by rw [FK,← hM]
      _=F*M^(n+1) ⊔ T*M^(n+1) :=Ideal.sup_mul F T _
      _≤F*M^(n+1) ⊔ T*(F*M^n ⊔ T^(n+1)) :=
        sup_le_sup_left (zMu ih) _
      _≤F*M^(n+1) ⊔ T^(n+1+1) := by
        rw [Ideal.mul_sup,← pU T F,t6 T F,pU,← FK T]
        apply sup_le Nj (sup_le ?_ le_sup_right)
        rw [FK M]
        exact (zMu (Ideal.mul_mono_left hTM)).trans Nj
theorem a1X {R:Type*} [oD R] [zE R] {M:lz R}
   {f t a :R} {n:ℕ} (hf :Prime f) (hM:M=ov {f,t})
   (h:f*a∈M^(n+1)) :a∈M^n:= by
 let F:lz R:=ov {f}
 let T:lz R:=ov {t}
 have hs :M=F ⊔ T:=hM.trans (Ideal.span_insert _ _)
 have hinj:p7 (fun x :R=>f*x) := fun _ _ h=>mul_left_cancel₀ hf.ne_zero h
 by_cases ht:f∣t
 · have hTF:T≤F:=Ideal.span_singleton_le_span_singleton.mpr ht
   exact cDR (hs.trans (sup_eq_left.mpr hTF)) hinj h
 have hparts :=eNl hs n h
 obtain ⟨b,hb,c,hc,he⟩:=Submodule.mem_sup.mp hparts
 obtain ⟨x,hx,rfl⟩:=Ideal.mem_span_singleton_mul.mp hb
 change c∈(ov ({t} : Set R))^(n+1) at hc
 rw [Ideal.span_singleton_pow,QL] at hc
 obtain ⟨y,rfl⟩:=hc
 have hdiv :f∣t^(n+1)*y :=⟨a - x,by
   rw [mul_sub,← he,zYK]⟩
 obtain ⟨z,rfl⟩:=(hf.dvd_or_dvd hdiv).resolve_left (fun hd=>ht (hf.dvd_of_dvd_pow hd))
 have ha :x+t^(n+1)*z=a :=hinj (by
   change f*(x+t^(n+1)*z)=f*a
   rw [In,← JM (t^(n+1)) f]
   exact he)
 have htM:t∈M:=hM ▸ Dz (by simp)
 rw [← ha]
 exact (M^n).add_mem hx ((M^n).mul_mem_right _
   (zdr (Nat.le_succ n) (Zt htM (n+1))))
theorem c2C (I:lz qU) [I.IsPrime] (hd:dual I) (P:Jet) (n:ℕ) :
  O9 I P n↔aIW I (iJ P)∈(I.map (aIW I))^n:= by
 simp only [O9,IU hd,Oc]
 rw [← Iw ,zi I.primeCompl (aBW I)]
 rfl
theorem c2F (I:lz qU) [I.IsPrime] (hd : ¬ dual I) (P:Jet) (n:ℕ) :
   O9 I P n↔brm I (aIW I (iJ P)) ∈
     ((I.map (aIW I)).map (brm I))^n:= by
 simp only [O9,Eg hd]
 rw [← Iw (brm I) (I.map (aIW I)) n,
   Ideal.mem_quotient_iff_mem_sup,← Iw ,← II,
   zi I.primeCompl (aBW I)]
 rfl
theorem cY8 {I:lz qU} {P:Jet} {a b:ℕ} (hab:a≤b)
  (h:O9 I P b) :O9 I P a := by
 classical
 obtain ⟨s,hs,h⟩:=h
 let J:lz Ambient:=if dual I then ⊥ else azl I
 have hle :I ^b ⊔ J≤I ^a ⊔ J:=sup_le_sup_right (zdr hab) J
 exact ⟨s,hs,hle h⟩
theorem bB3 {I:lz qU} (hp:I.IsPrime) {g:Equation} {P:Jet} {m:ℕ}
  (hg:Co g∉I) (h:O9 I (C g*P) m) :O9 I P m:= by
 obtain ⟨a,ha,h⟩:=h
 refine ⟨a*Co g,fun hz=>(hp.mem_or_mem hz).elim ha hg,?_⟩
 simpa only [nq,btc,pU] using h
theorem bWc {I:lz qU} {f :Equation} {P:Jet} {m r e :ℕ}
   (cancel : ∀ Q n,O9 I (C f*Q) (n+1)→O9 I Q n) (he :e< r)
   (hm:r≤ m) (h:O9 I (C (f^e)*P) m) :O9 I P (m+1 - r) := by
 let n:=m+1 - r
 have hne :n+e≤ m:= by omega
 have h' := cY8 hne h
 clear h hne he hm
 induction e with
 | zero=>simpa using h'
 | succ e ih =>
   apply ih
   apply cancel
   simpa only [FK,nq,pU,Vq,Nat.succ_eq_add_one] using h'
end
end aqb
end
section
namespace bat
noncomputable section
open Polynomial aR dN Rl
def Fy (linear :Bool) :ℕ:=if linear then 1 else 2
def step (linear :Bool) (g:af 4) (a :ℕ) (P:af 4) :af 4 :=
 if linear then u6 g P-(a :af 4)*pK (oK g)*P
 else aqZ g a P
def raw (linear :Bool) (g:af 4) :ℕ→af 4
 | 0=>MvPolynomial.X 0
 | n+1=>step linear g (Fy linear*n) (raw linear g n)
private theorem c7d (g:af 4) (n:ℕ) :raw false g n=su g n:= by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [raw,ih,step,Bool.false_eq_true,↓reduceIte,Fy,su]
@[simp] private theorem ajn (P:af 4) (m:Fin 4 →₀ ℕ) :
    (lX P).coeff m=pL (P.coeff m) := by
  classical
  rw [lX,MvPolynomial.coeff_sum]
  simp only [Yi ,Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,qm]
private theorem aTO (p:ao[X]) :
  lX (pQ p)=pQ (pL p) := by
 classical
 apply MvPolynomial.ext
 intro m
 rw [ajn]
 by_cases hm:0=m <;> simp [MvPolynomial.coeff_C,hm]
private theorem aCH (P Q:af 4) :
  lX (P+Q)=lX P+lX Q:= by
 ext m
 simp
private theorem bnr (P:af 4) (j:Fin 4) :
  lX (P*lI j)=lX P*lI j:= by
 classical
 ext m
 rw [ajn,Yo ,Yo]
 split_ifs <;> simp
private theorem a2H (P Q:af 4) :
  lX (P*Q)=lX P*Q+P*lX Q:= by
 classical
 ext m
 simp only [ajn,AddMonoidAlgebra.coeff_add,Cy ,
  MvPolynomial.coeff_mul,sI,G1 ,vG]
private theorem a6r (P Q:af 4) :
    pK (P*Q)=pK P*Q+P*pK Q:= by
  simp only [pK,a2H,zg ,
    add_mul,In,vG,JW,yl]
  have h (i:Fin 3) :
      pQ (C ((i.val+1 :ℕ) :ao))*lI i.succ *
        (P*qy i.castSucc Q) =
      P*(pQ (C ((i.val+1 :ℕ) :ao))*lI i.succ *
        qy i.castSucc Q) := by ac_rfl
  simp only [← pU,← JW] at h ⊢
  simp only [h]
  ring
private theorem ZF (g P Q:af 4) :
  u6 g (P*Q)=u6 g P*Q+P*u6 g Q:= by
 simp only [u6,a6r,oK,zg]
 ring
theorem exb {g:af 4} (hg: (shape g).t=1) :
  oK (oK g)=0:= by
 let w:Fin 4→ℕ:=Pi.single 3 1
 have hb:=Fa w 3 g
 rw [show w 3=1 by decide] at hb
 simp only [w,z5e] at hb
 change g.degreeOf 3=1 at hg
 have hd: (oK g).degreeOf 3≤0:= by
  simpa [oK,hg] using hb
 apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
 intro hm
 exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hm) (Ob hd)
private theorem c7g (g:af 4) (h:oK (oK g)=0) (n:ℕ) :
   su g n=oK g^n*raw true g n:= by
 have hD:u6 g (oK g)=oK g*pK (oK g) := by
   simp [u6,h]
 have hOne :u6 g 1=0:= by
   have hm:=ZF g 1 1
   simp only [mul_one,yU] at hm
   linear_combination -hm
 have hp (a :ℕ) :
     u6 g (oK g^a)=(a :af 4)*oK g^a*pK (oK g) := by
   induction a with
   | zero=>simp [hOne]
   | succ a ih =>
     rw [C5 ,ZF,ih,hD,Nat.cast_succ]
     ring
 induction n with
 | zero=>simp [su,raw]
 | succ n ih =>
   simp only [su,raw,step,Fy,↓Fz ,yU,ih,aqZ,
     ZF,hp,hD,C5 ,zd ,C9]
   ring
abbrev WB {L:Type} [c9 L] [oq ao L] (S:L[X]) :af 4 →+* L[X] :=
 Et (xL (aU ao L))
  (fun i=>v9 i.val S)
private theorem aNu {L:Type} [c9 L] [oq ao L]
    (P:af 4) (a :Fin 4→ L[X]) :
    let E :=Et (xL (aU ao L)) a
    pL (E P)=E (lX P) +
      ∑ i,pL (a i)*E (qy i P) := by
  classical
  let E :=Et (xL (aU ao L)) a
  change pL (E P)=E (lX P)+_
  induction P using LP with
  | C c =>
    simp [E,aTO,derivative_map]
  | add P Q hP hQ =>
    simp only [qG,aCH,hP,hQ,In,vG]
    ring
  | mul_X P j ih =>
    have hx :E (lI j)=a j:=MvPolynomial.eval₂_X _ _ _
    rw [nq,hx,G1 ,ih,bnr,nq,hx]
    simp only [zg ,qG,nq,In,vG]
    have hleft: (∑ i,pL (a i) *
          (E (qy i P)*E (lI j))) =
        (∑ i,pL (a i)*E (qy i P))*a j:= by
      simp only [hx,JW,pU]
    have hright: (∑ i,pL (a i) *
          (E P*E (qy i (lI j)))) =
        pL (a j)*E P:= by
      simp [MvPolynomial.pderiv_X,Pi.single_apply,mul_ite]
    rw [hleft,hright]
    ring
private theorem aNh {L:Type} [c9 L] (S:L[X]) (k :ℕ) :
  pL (v9 k S)=C ((k+1 :ℕ) :L)*v9 (k+1) S:= by
 have h:=LinearMap.congr_fun (hasseDeriv_comp (R:=L) 1 k) S
 simpa [hasseDeriv_one',Nat.choose_one_right,NZ,C_eq_natCast,Nat.add_comm,add_mul] using h
private theorem bdn {L:Type} [c9 L] [oq ao L]
   (S:L[X]) (P:af 4) :
   pL (WB S P)=WB S (pK P) +
     pL (v9 3 S)*WB S (oK P) := by
 rw [aNu,Fin.sum_univ_castSucc,pK,qG,sI,← add_assoc]
 congr 2
 refine vw rfl fun i _ => ?_
 simp [WB,aNh]
private theorem bpy {L:Type} [c9 L] [oq ao L] (S:L[X])
   (g P:af 4) (hg:WB S g=0) :
   WB S (u6 g P)=WB S (oK g) *
     pL (WB S P) := by
 have hz :=(bdn S g).symm
 rw [hg,qm] at hz
 rw [bdn,u6,uz ,nq,nq]
 linear_combination -WB S (oK P)*hz
private theorem anS {L:Type} [c9 L] (a :ℕ) (U V:L[X]) :
   U*pL (U^a*V)-(a :L[X])*pL U*(U^a*V) =
     U^(a+1)*pL V:= by
 cases a with
 | zero=>simp
 | succ a =>
   rw [G1 ,derivative_pow,Nat.succ_sub_one,C5 U (a+1),FK U a]
   simp only [C_eq_natCast]
   ring
theorem bpF {L:Type} [c9 L] [oq ao L] (linear :Bool)
    (g:af 4) (hl:linear=true→ oK (oK g)=0)
    (S:L[X]) (hg:WB S g=0) (n:ℕ) :
    WB S (raw linear g n) =
      WB S (oK g)^(Fy linear*n)*((pL (R:=L))^[n]) S:= by
  induction n with
  | zero=>simp [raw]
  | succ n ih =>
    rw [raw,Nat.mul_succ,zLk]
    let a :=Fy linear*n
    let U:=WB S (oK g)
    let V:=((pL (R:=L))^[n]) S
    let P:=raw linear g n
    change WB S (step linear g a P)=U^(a+Fy linear)*pL V
    have hP:WB S P=U^a*V:=ih
    have hflow:=bpy S g P hg
    have hrule :=anS a U V
    cases linear with
    | false =>
      simp only [step,zN5,↓Fz ,aqZ,uz ,nq,G4]
      rw [hflow,bpy S g (oK g) hg,hP]
      change U*(U*pL (U^a*V))-(a :L[X])*(U*pL U)*(U^a*V)
        = U^(a+2)*pL V
      rw [show a+2=(a+1)+1 by omega,C5]
      linear_combination U*hrule
    | true =>
      have hA:WB S (pK (oK g))=pL U:= by
        dsimp only [U]
        rw [bdn,hl rfl,qm,vj,zS]
      simp only [step,↓Fz ,uz ,nq,G4]
      rw [hflow,hA,hP]
      exact hrule
end
end bat
end
section
namespace bat
noncomputable section
open Polynomial MvPolynomial aR Ex dN wH lB
open Sr.Weight
local notation "W" => MvPolynomial.weightedTotalDegree
def ail (g:af 4) :Bool:=decide ((shape g).t=1)
def denominator (g:af 4) (n:ℕ) :af 4 :=
 oK g^(Fy (ail g)*n)
def bqQ (g:af 4) {n:ℕ} (j:Fin n) :af 4 :=
  pQ (lJ (↑j.val.factorial:ao)⁻¹) *
    (oK g^(Fy (ail g)*(n - j.val))*raw (ail g) g j.val)
def backwardWeight (i j:ℕ) :ao[X] :=
 (((mD:ao[X][X])-Polynomial.C (mD:ao[X]))^j).coeff i
def numerator (g:af 4) {n:ℕ} (i:Fin n) :af 4 :=
 ∑ j:Fin n,pQ (backwardWeight i.val j.val)*bqQ g j
private theorem al0 (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {g P:af 4} {B d:ℕ} (hB:w 3≤B) (hg:W w g≤B) (hP:W w P≤d) :
    W w (u6 g P)≤d+(B - w 3)+Δ:= by
  have hsep:=(Fa w 3 g).trans (G8 hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply MK
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (FU _ _ _).trans
      ((wA hsep (aa5 w Δ hshift P hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    by_cases h:w 3≤d
    · have hp:=(Fa w 3 P).trans (G8 hP (w 3))
      exact (FU _ _ _).trans
        ((wA (aa5 w Δ hshift g hg) hp).trans (by omega))
    · rw [oK,arU w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
        vj,weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem dlS (w:Fin 4→ℕ) (a :ℕ) (P:af 4) :
  W w ((a :af 4)*P)≤W w P:= by
 rw [← G4 (pQ:ao[X] →+* af 4)]
 exact Po w _ _
private theorem step_bound (linear :Bool) (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {g P:af 4} {B d:ℕ} (hB:w 3≤B) (hg:W w g≤B) (hP:W w P≤d) (a :ℕ) :
    W w (step linear g a P)≤d+(Fy linear*(B - w 3)+Δ) := by
  have hsep:W w (oK g)≤B - w 3 :=
    (Fa w 3 g).trans (G8 hg (w 3))
  cases linear
  · simp only [step,zN5,↓Fz ,Fy,aqZ]
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply MK <;> apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    · exact (FU _ _ _).trans
        ((wA hsep (al0 w Δ hshift hB hg hP)).trans (by omega))
    · exact (FU _ _ _).trans (wA
        ((dlS _ _ _).trans (al0 w Δ hshift hB hg hsep)) hP |>.trans (by omega))
  · simp only [step,Fy,↓Fz ,yU]
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply MK <;> apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    · exact (al0 w Δ hshift hB hg hP).trans (by omega)
    · exact (FU _ _ _).trans (wA
        ((dlS _ _ _).trans (aa5 w Δ hshift _ hsep)) hP |>.trans (by omega))
private theorem ceI (linear :Bool) (w:Fin 4→ℕ) (Δ:ℕ)
   (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) {g:af 4} {B:ℕ}
   (hB:w 3≤B) (hg:W w g≤B) (n:ℕ) :
   W w (raw linear g n)≤w 0+n*(Fy linear*(B - w 3)+Δ) := by
 induction n with
 | zero=>simpa only [raw,zero_mul,add_zero] using abx (R:=ao[X]) w 0
 | succ n ih =>
   simpa only [raw,Ts ,yU,Vq] using
     step_bound linear w Δ hshift hB hg ih (Fy linear*n)
private theorem cpc (g:af 4) (w:Fin 4→ℕ) (a :ℕ) {B:ℕ} (hg:W w g≤B) :
   W w (oK g^a)≤a*(B - w 3) :=
 (weightedTotalDegree_pow_le _ _ _).trans (SD _
   ((Fa w 3 g).trans (G8 hg _)))
end
end bat
end
section
namespace bat
noncomputable section
open Polynomial aR dN lB Rl
private theorem bO3 (g:af 4) :
  ail g=true→ oK (oK g)=0 :=
 fun h=>exb (of_decide_eq_true h)
private theorem ajW {L:Type} [c9 L] (S:L[X]) (n:ℕ) :
  pL^[n] S=C (n.factorial:L)*v9 n S:= by
 ext m
 rw [coeff_iterate_derivative,coeff_C_mul,hasseDeriv_coeff,Nat.descFactorial_eq_factorial_mul_choose]
 simp only [NZ,zd ,pU]
private theorem d2o {L:Type} [c9 L] [oq ao L]
   (g:af 4) (S:L[X]) (hg:WB S g=0)
   {n:ℕ} (hn:n≤K1.p) (j:Fin n) :
   WB S (bqQ g j) =
     WB S (denominator g n)*v9 j.val S:= by
 let k :=Fy (ail g)
 let U:=WB S (oK g)
 let m:=xL (aU ao L)
 let u:ao:=(j.val.factorial:ao)
 have hu:u≠0:=ahA (j.isLt.trans_le hn)
 have hinv :m (C u⁻¹)*C (↑j.val.factorial:L)=1 := by
   have h:C u⁻¹*C u=(1 :ao[X]) := by
     rw [← nq,inv_mul_cancel₀ hu,map_one]
   simpa only [m,u,nq,map_one,zKC,PA,G4]
     using ox m h
 simp only [bqQ,denominator,nq,xW,UY]
 rw [bpF _ _ (bO3 g) S hg,ajW]
 change m (C u⁻¹)*(U^(k*(n - j.val)) *
   (U^(k*j.val)*(C (↑j.val.factorial:L)*v9 j.val S))) =
     U^(k*n)*v9 j.val S
 calc
   _=(m (C u⁻¹)*C (↑j.val.factorial:L)) *
         ((U^(k*(n - j.val))*U^(k*j.val))*v9 j.val S) := by ring
   _ = _:= by
     rw [hinv,yU,← pow_add,← Qy ,zxt j.isLt.le]
private theorem eyU {L:Type} [c9 L] [oq ao L] (i j:ℕ) :
   (backwardWeight i j).map (aU ao L) =
     (((mD:L[X][X]) - C (mD:L[X]))^j).coeff i:= by
 let m:=xL (aU ao L)
 change m ((((mD:ao[X][X]) - C (mD:ao[X]))^j).coeff i)= _
 rw [← Y4 (f :=m)]
 simp [m]
private theorem d1R {L:Type} [c9 L] (P:L[X]) :
 (P.map (C:L →+* L[X])).eval (mD:L[X])=P:= by rw [eval_map,eval₂_C_X]
private theorem b6w {L:Type} [c9 L] (S:L[X])
   {n:ℕ} (hS:S.natDegree<n) (i:ℕ) :
   (∑ j:Fin n,(((mD:L[X][X]) - C (mD:L[X]))^j.val).coeff i *
     v9 j.val S)=C (S.coeff i) := by
 let Sh:=S.map (C:L →+* L[X])
 have hd: (taylor (mD:L[X]) Sh).natDegree<n:= by
   rw [natDegree_taylor]
   exact natDegree_map_le.trans_lt hS
 have h:=sum_taylor_eq Sh (mD:L[X])
 rw [sum_over_range' _ (fun n=> by simp) _ hd,← Fin.sum_univ_eq_sum_range] at h
 have hc:=ox (fun P:L[X][X]=>P.coeff i) h
 simpa only [finsetSum_coeff,coeff_C_mul,taylor_coeff,hasseDeriv_map,d1R,Sh,
   Y4 ,t6] using hc
private theorem b12 {L:Type} [c9 L] [oq ao L]
  (g:af 4) (S:L[X]) (hg:WB S g=0)
  {n:ℕ} (hd:S.natDegree<n) (hn:n≤K1.p) (i:Fin n) :
  WB S (numerator g i)=WB S (denominator g n)*C (S.coeff i.val) := by
 simp only [numerator,sI,nq,UY ,d2o _ _ hg hn,
  zKC,eyU,yl,← b6w S hd]
 exact vw rfl (fun j _=> by ring)
private theorem d29 {L:Type} [c9 L] [oq ao L]
  (g:af 4) (S:L[X]) (hg:WB S g=0) {n:ℕ} (hd:S.natDegree<n) :
  WB S (raw (ail g) g n)=0:= by
 rw [bpF _ _ (bO3 g) S hg,iterate_derivative_eq_zero hd,vj]
private theorem specializes {L:Type} [c9 L] [oq ao L]
    (g:af 4) (S:L[X]) {n:ℕ} (hd:S.natDegree<n) (hn:n≤K1.p)
    (hs :Ve g S=0) (hr :Ve (oK g) S≠0) :
    Ve (denominator g n) S≠0∧Ve (raw (ail g) g n) S=0 ∧
      ∀ i:Fin n,Ve (numerator g i) S =
        Ve (denominator g n) S*C (S.coeff i.val) := by
  have hD:WB S (denominator g n)≠0:= by
    rw [denominator,xW]
    exact J4 _ hr
  exact ⟨hD,d29 g S hs hd,fun i=>b12 g S hs hd hn i⟩
end
end bat
end
section
namespace bzt
noncomputable section
open aR oR we aA1 MvPolynomial
open dN (lX pK)
open lB (aJY Po abx)
open scoped Polynomial
local notation "W" => weightedTotalDegree
private theorem bfH {R:Type*} [CommSemiring R] {w:Fin 4→ℕ}
   {p q:cy (Fin 4) R} {a b:ℕ} (hp:W w p≤a) (hq:W w q≤b) :
   W w (p*q)≤a+b :=
 (FU w p q).trans (wA hp hq)
private theorem dWx (w:Fin 4→ℕ) (i:Fin 4) (p:af 4)
  (h:W w p<w i) :qy i p=0:= by
 apply MvPolynomial.ext
 intro m
 rw [coeff_pderiv]
 have hz :p.coeff (m+Finsupp.single i 1)=0:= by
  by_contra hn
  have hm:=GF w (MvPolynomial.mem_support_iff.mpr hn)
  rw [qG,UZ,one_smul] at hm
  omega
 simp [hz]
private theorem c00 (w:Fin 4→ℕ) (i:Fin 4) {p q:af 4} {d delta :ℕ}
   (hp:W w p≤d) (hq:W w q≤w i+delta) :
   W w (q*qy i p)≤d+delta := by
 by_cases hi:w i≤d
 · have hd:=(Fa w i p).trans
     (G8 hp (w i))
   exact (bfH hq hd).trans (by omega)
 · rw [dWx w i p (hp.trans_lt (Nat.lt_of_not_ge hi)),vj,
     weightedTotalDegree_zero]
   exact Nat.zero_le _
private theorem dMG (w:Fin 4→ℕ) (p:af 4) :
  W w (lX p)≤W w p:= by
 classical
 apply aJY
 intro m hm
 obtain ⟨j,hj,hmj⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
 have h:j=m:= by
  by_contra hne
  exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [Yi ,Eg hne])
 exact h ▸ hj
private theorem aa5 (w:Fin 4→ℕ) {delta d:ℕ}
   (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+delta)
   {p:af 4} (hp:W w p≤d) :
   W w (pK p)≤d+delta := by
 classical
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
 apply zcy
 · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
     ((dMG w p).trans (hp.trans (Nat.le_add_right _ _)))
 · apply Submodule.sum_mem
   intro i _
   apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
   rw [pU]
   exact (Po w _ _).trans
     (c00 w i.castSucc hp ((abx w i.succ).trans (hshift i)))
private theorem cXB (f :af 3) :KY f=qy 2 (KX f) :=
 (pderiv_rename (Vs 3) (2 :Fin 3) f).symm
private theorem cXW (w:Fin 4→ℕ) {delta step sep d:ℕ}
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+delta)
    {f :af 3} {p:af 4} (hp:W w p≤d) (hs :W w (KY f)≤ sep)
    (hsep:sep+delta≤ step) (hu:W w (apE f)≤w 3+step) (k :ℕ) :
    W w (a5p f k p)≤d+step:= by
  unfold a5p
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply MK
  · apply zcy
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((bfH hs (aa5 w hshift hp)).trans (by omega))
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        (c00 w 3 hp hu)
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [← G4 (pQ:ao[X] →+* af 4),pU]
    exact ((Po w _ _).trans
      (bfH (aa5 w hshift hs) hp)).trans (by omega)
private theorem bHm (w:Fin 4→ℕ) (p:af 4) :
  W w (fW p)≤W w p :=
 aJY w (support_map_subset qY p)
private abbrev bh4 :Fin 4→ℕ := ![1,1,1,0]
private abbrev indexWeight:Fin 4→ℕ := ![0,1, 2,0]
private abbrev topWeight:Fin 4→ℕ:=Pi.single 2 1
private abbrev bet:Fin 4→ℕ:=Pi.single 3 1
private theorem azs (w:Fin 4→ℕ) (f :af 3) :
  W w (KX f)=W (w ∘ Gn) f :=
 weightedTotalDegree_rename_of_injective (Vs 3)
private theorem fits {p:eT 4} {b j t h:ℕ}
  (hb:W bh4 p≤b) (hj:W indexWeight p≤j)
  (ht:W topWeight p≤t) (hh:W bet p≤h) :
  DO p ⟨b,j,min t (j/2)⟩ h:= by
 intro a ha
 have hb' := (GF bh4 ha).trans hb
 have hj' := (GF indexWeight ha).trans hj
 have ht' := (GF topWeight ha).trans ht
 have hh' := (GF bet ha).trans hh
 rw [Finsupp.weight_single_one_apply] at ht' hh'
 simp [Finsupp.weight_eq_sum,v8 ,x7] at hb' hj'
 have hj'' : a 1+2*a 2≤j:= by omega
 exact ⟨hb',hj'',le_min ht' (by omega),hh'⟩
end
end bzt
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Qo
noncomputable section
open wT MvPolynomial Finset
variable {F:Type*} [c9 F]
theorem c1a (P:cy (Fin 5) F) (hP:yV P) :
  bsE (P*lI 1) 1 0∧bsE (P*lI 2) 0 1 := by
 constructor
 all_goals
  intro e he
  rw [support_mul_X] at he
  obtain ⟨f,hf,rfl⟩:=mem_map.mp he
  have hh:=bfT P hP f hf
  simpa [Cy ,Kc] using hh
theorem gxC (P Q:cy (Fin 5) F) (a b c d:ℕ)
  (hP:bsE P a b) (hQ:bsE Q c d) (hne : (a,b)≠(c,d)) :
  Lf P.support Q.support := by
 apply disjoint_left.mpr
 intro e heP heQ
 have h1 :=hP e heP
 have h2 :=hQ e heQ
 exact hne (Prod.ext (by omega) (by omega))
theorem cwT (v :Fin 5→ℕ) (P Q:cy (Fin 5) F)
  (h:Lf P.support Q.support) :
  (P+Q).weightedTotalDegree v=max (P.weightedTotalDegree v) (Q.weightedTotalDegree v) := by
 have hs : (P+Q).support=P.support∪Q.support :=zbA h
 simp only [vh,hs,Finset.sup_union]
theorem cYi (v :Fin 5→ℕ) (U V R:cy (Fin 5) F)
    (hU:U≠0) (hV:V≠0) (hUm:yV U) (hVm:yV V)
    (hRm:yV R) :
    (U*lI 1+V*lI 2-R).weightedTotalDegree v=
      max (max (U.weightedTotalDegree v+v 1) (V.weightedTotalDegree v+v 2))
        (R.weightedTotalDegree v) := by
  have htU:=(c1a U hUm).1
  have htV:=(c1a V hVm).2
  have hd:=gxC _ _ 1 0 0 1 htU htV (by decide)
  have hsum: (U*lI 1+V*lI 2).support=(U*lI 1).support∪(V*lI 2).support :=
    zbA hd
  have hdR:Lf (U*lI 1+V*lI 2).support (-R).support := by
    apply disjoint_left.mpr
    intro e he heR
    have hR:e∈R.support := by simpa using heR
    have hRtag :=bfT R hRm e hR
    rw [hsum] at he
    rcases mem_union.mp he with hu | hv
    · have hh:=htU e hu
      omega
    · have hh:=htV e hv
      omega
  rw [sub_eq_add_neg,cwT _ _ _ hdR,
    cwT _ _ _ hd,
    Pr _ _ _ hU (X_ne_zero 1),
    Pr _ _ _ hV (X_ne_zero 2)]
  have hx (i:Fin 5) : (lI i:cy (Fin 5) F).weightedTotalDegree v=v i:= by
    rw [lI,weightedTotalDegree_monomial _ _ _ one_ne_zero]
    simp [UZ]
  rw [hx 1,hx 2]
  have hn: (-R).weightedTotalDegree v=R.weightedTotalDegree v := by simp [vh]
  rw [hn]
theorem bfU (w:ℕ) (P:cy (Fin 5) F)
   (hP:yV P) (q:Fin 4) :
   P.weightedTotalDegree (vO w q)=![P.degreeOf 0,0,P.degreeOf 3,P.degreeOf 4] q:= by
 have ht:=bfT P hP
 fin_cases q
 · change P.weightedTotalDegree (vO w 0)=P.degreeOf 0
   rw [vh,IT]
   apply S2 rfl
   intro e he
   have hh:=ht e he
   simp [vO,aQ8,hh.1,hh.2]
 · change P.weightedTotalDegree (vO w 1)=0
   apply Ob
   apply Ok
   intro e he
   have hh:=ht e he
   simp [vO,aQ8,hh.1,hh.2]
 · change P.weightedTotalDegree (vO w 2)=P.degreeOf 3
   rw [vh,IT]
   apply S2 rfl
   intro e he
   have hh:=ht e he
   simp [vO,aQ8,hh.1,hh.2]
 · change P.weightedTotalDegree (vO w 3)=P.degreeOf 4
   rw [vh,IT]
   apply S2 rfl
   intro e he
   have hh:=ht e he
   simp [vO,aQ8,hh.1,hh.2]
theorem b1J (w H :ℕ) (U V W:cy (Fin 5) F)
   (hU:U≠0) (hV:V≠0)
   (hUm:yV U) (hVm:yV V) (hWm:yV W)
   (hH :max (U.degreeOf 0) (V.degreeOf 0)=H) (hWX:W.degreeOf 0≤w+H)
   (hWS:W.degreeOf 3≤YF U V) (hWT:W.degreeOf 4≤aab U V) :
   ∀ j,(U*lI 1+V*lI 2 - W).weightedTotalDegree
     (vO w j)=A6 (w+H) 1 (YF U V) (aab U V) j:= by
 intro j
 rw [cYi _ U V W hU hV hUm hVm hWm,bfU w U hUm,
   bfU w V hVm,bfU w W hWm]
 fin_cases j
 · simp [vO,A6]
   omega
 · simp [vO,A6]
 · simp [vO,A6,YF] at hWS ⊢
   omega
 · simp [vO,A6,aab] at hWT ⊢
   omega
private theorem a6L (Q:cy (Fin 5) F)
  (hQ:yV Q) :xx Q=lJ ((xx Q).coeff 0) := by
 apply Polynomial.eq_C_of_natDegree_le_zero
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro j hj
 by_contra hn
 obtain ⟨f,hf⟩:=support_nonempty.mpr hn
 obtain ⟨e,he,_,_,he2,_,_⟩:=cce Q j f hf
 have he0:=(bfT Q hQ e he).2
 omega
def equation (U V W:cy (Fin 5) F) :cy (Fin 5) F :=
 U*lI 1+V*lI 2 - W
def ayz (U W:cy (Fin 5) F) :cy (Fin 4) F :=
 (xx W).coeff 0-(xx U).coeff 0*lI 1
def auL (V:cy (Fin 5) F) :cy (Fin 4) F :=
 (xx V).coeff 0
theorem bpu (U V W:cy (Fin 5) F)
    (hU:yV U) (hV:yV V) (hW:yV W) :
    xx (equation U V W) =
      lJ (auL V)*mD -
        lJ (ayz U W) := by
  simp only [equation,uz ,qG,nq,aI3]
  rw [a6L U hU,a6L V hV,a6L W hW]
  simp [auL,ayz,uz ,nq]
  ring
theorem bDV (V:cy (Fin 5) F)
  (hV:yV V) (hn:V≠0) :auL V≠0:= by
 intro h
 apply hn
 apply (xx (F:=F)).injective
 have he :xx V=lJ (auL V) :=
  a6L V hV
 rw [he,h,Polynomial.C_0]
 exact (qm (xx (F:=F))).symm
theorem bpv (U V W:cy (Fin 5) F)
    (hU:yV U) (hV:yV V) (hW:yV W)
    (hn:V≠0) (hUV:IsRelPrime U V) :
    (lJ (auL V)*mD -
        lJ (ayz U W)).IsPrimitive := by
  apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro d hd
  have hc:=(Polynomial.C_dvd_iff_dvd_coeff d _).mp hd
  have hdV:d∣auL V:= by
    simpa [PM,z8l] using hc 1
  have hdN :d∣ayz U W:= by
    simpa [PM,z8l] using hc 0
  let e :=(xx (F:=F)).symm (lJ d)
  have heV:e∣V:= by
    apply (map_dvd_iff (xx (F:=F))).mp
    change xx ((xx (F:=F)).symm (lJ d))∣xx V
    rw [Aa ,a6L V hV]
    exact map_dvd lJ hdV
  have heN :e∣W-U*lI 1 := by
    apply (map_dvd_iff (xx (F:=F))).mp
    change xx ((xx (F:=F)).symm (lJ d)) ∣
      xx (W-U*lI 1)
    rw [Aa ,uz ,nq,aI3,
      a6L W hW,a6L U hU]
    change lJ d∣lJ ((xx W).coeff 0) -
      lJ ((xx U).coeff 0)*lJ (lI 1)
    rw [← nq,← uz]
    exact map_dvd lJ hdN
  obtain ⟨v,hv⟩:=heV
  have he :e≠0:= by intro hz; apply hn; rw [hv,hz,zero_mul]
  have hv_ne :v≠0:= by intro hz; apply hn; rw [hv,hz,vj]
  have heomits :e.degreeOf 1=0:= by
    have hdeg:=ox (degreeOf (1 :Fin 5)) hv
    rw [hV.1,degreeOf_mul_eq he hv_ne] at hdeg
    omega
  obtain ⟨q,hq⟩:=heN
  have hh : -U=e*qy 1 q:= by
    simpa [uz ,zg ,aPg _ _ hW.1,
      aPg _ _ hU.1,
      aPg _ _ heomits] using ox (qy (R:=F) (1 :Fin 5)) hq
  have heU:e∣U:= by
    refine ⟨-pderiv 1 q,?_⟩
    rw [mul_neg,← hh,neg_neg]
  have hu:=(hUV heU ⟨v,hv⟩).map (xx (F:=F)).toRingHom
  change wR (xx e) at hu
  exact Polynomial.isUnit_C.mp (by simpa only [e,Aa] using hu)
theorem bZY (w H s t:ℕ) (U V W:cy (Fin 5) F)
   (hU:yV U) (hV:yV V) (hW:yV W) (hVn:V≠0)
   (hQ:equation U V W∈filtered (vO w) (A6 (w+H) 1 s t)) :
   (ayz U W).weightedTotalDegree Qb≤1 ∧
   (auL V).weightedTotalDegree Qb≤0 ∧
   (ayz U W).weightedTotalDegree ME≤ s ∧
   (auL V).weightedTotalDegree ME≤ s ∧
   (ayz U W).weightedTotalDegree MD ≤t ∧
   (auL V).weightedTotalDegree MD ≤t - 1 := by
 obtain ⟨hY,hS,hT⟩:=bgg (w+H) w 1 s t _ hQ
 have h0: (xx (equation U V W)).coeff 0 = -ayz U W:= by
   rw [bpu U V W hU hV hW]
   simp [PM]
 have h1 : (xx (equation U V W)).coeff 1=auL V:= by
   rw [bpu U V W hU hV hW]
   simp [PM]
 have hV' : (xx (equation U V W)).coeff 1≠0:= by
   rw [h1]
   exact bDV V hV hVn
 have hy1 :=hY 1 vZ hV'
 have hs1 :=hS 1 vZ hV'
 have ht1 :=hT 1 vZ hV'
 rw [h1] at hy1 hs1 ht1
 refine ⟨?_,by omega,?_,hs1,?_,by omega⟩
 all_goals
   by_cases hn:ayz U W=0
   · simp [hn,vh]
   · have hn' : (xx (equation U V W)).coeff 0≠0:= by simpa [h0] using hn
     first
     | simpa [h0,weightedTotalDegree] using hY 0 (by decide) hn'
     | simpa [h0,weightedTotalDegree] using hS 0 (by decide) hn'
     | simpa [h0,weightedTotalDegree] using hT 0 (by decide) hn'
end
end Qo
end
section
namespace Jq
noncomputable section
open dN WI MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem dVH {σ:Type} (s :σ→Fin 5) (a :σ →₀ ℕ) :
  (Kv (jT s) a).degree=a.degree := by
 have h:Finsupp.degree.comp (Kv (jT s))=Finsupp.degree := by
  ext j
  simp [UZ,jT,zY]
 exact zk h a
private theorem eLa {σ:Type} [C4 σ] (s :σ→Fin 5) (t:jJ) :
  (dO s t).FG:= by
 change (weightedHomogeneousSubmodule p6 (jT s) t).FG
 rw [weightedHomogeneousSubmodule_eq_finsupp_supported,← Module.Finite.iff_fg]
 have hs : {a :σ →₀ ℕ | Kv (jT s) a=t}.Finite := by
  refine (Finsupp.finite_of_degree_eq t.degree).subset ?_
  intro a ha
  change Kv (jT s) a=t at ha
  change a.degree=t.degree
  exact (dVH s a).symm.trans (ox Finsupp.degree ha)
 have :=hs.to_subtype
 exact Module.Finite.of_basis
  (basisRestrictSupport p6 {a :σ →₀ ℕ | Kv (jT s) a=t})
abbrev aPz {σ:Type} (s :σ→Fin 5) (J:lz (cy σ p6))
   (t:jJ) :=
 (dO s t).map (F9 p6 J).toLinearMap
instance {σ:Type} [C4 σ] (s :σ→Fin 5) (J:lz (cy σ p6))
  (t:jJ) :oz p6 (aPz s J t) :=
 Module.Finite.iff_fg.mpr ((eLa s t).map _)
theorem a4I {σ:Type} [C4 σ] (s :σ→Fin 5)
    (J:lz (cy σ p6)) (hJ:J.IsHomogeneous (dO s))
    (i:Fin 5) (g:cy σ p6) (hg:g∈dO s (zY i)) :
    (J ⊔ ov {g}).IsHomogeneous (dO s) ∧
      ∀ t:jJ,KQ s (J ⊔ ov {g}) (t+zY i) +
        KQ s (J.colon {g}) t=KQ s J (t+zY i) := by
  have hspan: (ov {g}).IsHomogeneous (dO s) :=
    Ideal.homogeneous_span _ _ (by
      intro x hx
      obtain rfl :x=g:=hx
      exact ⟨zY i,hg⟩)
  refine ⟨hJ.sup hspan,?_⟩
  intro t
  let K:=J ⊔ ov {g}
  let A:=J.colon {g}
  let e :=zY i
  let q:=z5F p6 (show J≤K from Nj)
  let cut:aPz s J (t+e) →ₗ[p6] aPz s K (t+e) :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y=> by
      obtain ⟨b,hb,hby⟩:=y.property
      exact ⟨b,hb,by simpa [q] using ox q hby⟩
  have hsurj:u5 cut:= by
    intro y
    obtain ⟨b,hb,hby⟩:=y.property
    exact ⟨⟨lV J b,⟨b,hb,rfl⟩⟩,vH (by simpa [cut,q] using hby)⟩
  let mu:=(Vp J g).restrictScalars p6
  let emb:aPz s A t →ₗ[p6] aPz s J (t+e) :=
    (mu.domRestrict _).codRestrict _ fun y=> by
      obtain ⟨b,hb,hby⟩:=y.property
      have hbg:b*g∈dO s (t+e) :=
        IsWeightedHomogeneous.mul hb hg
      refine ⟨b*g,hbg,?_⟩
      change lV J (b*g)=mu y.val
      change lV A b=y.val at hby
      rw [← hby]
      exact (azY J g b).symm
  have hInj:p7 emb:= fun y z h =>
    vH (aPy J g (ox Re h))
  have hker :Sd cut=LinearMap.range emb:= by
    ext y
    obtain ⟨b,hb,hby⟩:=y.property
    have hy :y=⟨lV J b,⟨b,hb,rfl⟩⟩:=vH hby.symm
    rw [hy,zeS,LinearMap.mem_range]
    constructor
    · intro hz
      have hkb:b∈K:= by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa [cut,q] using ox Re hz
      obtain ⟨a,ha,c,hc,hac⟩:=Submodule.mem_sup.mp hkb
      obtain ⟨d,rfl⟩:=Ideal.mem_span_singleton'.mp hc
      let m:=weightedHomogeneousComponent (jT s) t d
      have hm:m∈dO s t:=weightedHomogeneousComponent_mem _ _ _
      have ha' := weightedHomogeneousComponent_mem_of_mem _ _ hJ ha (t+e)
      have hb' : b.IsWeightedHomogeneous (jT s) (t+e) :=hb
      have hdecomp:=ox (weightedHomogeneousComponent (jT s) (t+e)) hac
      rw [qG,bDb s hg,weightedHomogeneousComponent_eq_self hb'] at hdecomp
      refine ⟨⟨lV A m,⟨m,hm,rfl⟩⟩,vH ?_⟩
      change Vp J g (lV A m)=lV J b
      rw [azY,← hdecomp,qG,Ideal.Quotient.eq_zero_iff_mem.mpr ha',yB]
    · rintro ⟨z,hz⟩
      obtain ⟨a,_,haz⟩:=z.property
      apply vH
      change lV K b=0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm:a*g∈K :=
        Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a,rfl⟩)
      have he :=ox Re hz
      change mu z.val=lV J b at he
      rw [← haz] at he
      change Vp J g (lV A a)=lV J b at he
      rw [azY,Ideal.Quotient.eq] at he
      have hsub:a*g-(a*g - b)∈K:=K.sub_mem hm ((show J≤K from Nj) he)
      rwa [sub_sub_cancel] at hsub
  have hrank :=cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,hker,LinearMap.finrank_range_of_inj hInj] at hrank
  exact hrank
end
end Jq
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace wT
noncomputable section
open MvPolynomial
open scoped BigOperators
private theorem a5X {A:Type*} (S:n5 A) (aa0:Set A) [DecidablePred (· ∈ aa0)] :
  ((S:Set A)∩aa0).ncard=(S.filter (· ∈ aa0)).card:= by
 rw [← Du,Finset.coe_filter]
 rfl
private theorem caj {F σ:Type*} [c9 F] [C4 σ]
    (J:lz (cy σ F)) [J.IsPrime] (x :σ→F) (hx :x∈yJ F J) :
    1≤u9 J:= by
  classical
  generalize hd: (G7 J).natDegree=d
  induction d using Zf generalizing J with
  | h d ih =>
    by_cases h0:d=0
    · have hfin:=Zi (K:=F) J (hd.trans h0)
      have hxone :1≤(yJ F J).ncard:= by
        simpa using SM (Set.singleton_subset_iff.mpr hx) hfin.1
      exact (by exact_mod_cast hxone : (1 :ℚ)≤_).trans hfin.2
    have hproper : ∃ i,lI i - C (x i)∉J:= by
      by_contra hn
      push Not at hn
      let φ:=lV J
      have hmaps :φ=φ.comp (C.comp (xI x)) := by
        apply t8
        · intro c
          simp [φ]
        · intro i
          simp only [EK,eval_X]
          exact sub_eq_zero.mp (by rw [← uz]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hn i))
      have hsurj:u5 (aU F (cy σ F ⧸ J)) := by
        intro q
        obtain ⟨g,rfl⟩:=uh q
        refine ⟨xI x g,?_⟩
        exact (Ef hmaps g).symm
      letI:oz F (cy σ F ⧸ J) :=
        Ar (Algebra.linearMap F (cy σ F ⧸ J)) hsurj
      exact h0 (by rw [← hd,affineHilbertPolynomial_eq_C_finrank,Polynomial.natDegree_C])
    obtain ⟨i,hi⟩:=hproper
    let f :=lI i - C (x i)
    have hxf :oZ x f=0:= by simp [f]
    have hfdeg:f.totalDegree≤1 := by
      exact (totalDegree_sub _ _).trans (by simp)
    have hxp:x∈yJ F (J ⊔ ov {f}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx,hxf⟩
    obtain ⟨Q,hQ,hxQ⟩:=zwb
      (J ⊔ ov {f}) (1 :cy σ F) x hxp (by simp)
    have hQmin:=(Ideal.mem_retainedMinimalPrimes.mp hQ).1
    letI:Q.IsPrime :=hQmin.isPrime
    have hd' := zdH hi hQmin
    have hone :=ih _ (by omega) Q hxQ rfl
    have hsum:=zcE
      (1 :cy σ F) hi hfdeg
    have hQsum:=zfK (f :=u9)
      (fun A _=>zcN A) hQ
    simpa only [RP ,yU] using hone.trans (hQsum.trans hsum)
private theorem ccD {F σ ι:Type*} [c9 F] [C4 σ] [Fintype ι]
    (s :cy σ F) (cuts :ι→cy σ F) {A L M:ℕ}
    (hLA:L≤A) (hdeg : ∀ i,(cuts i).totalDegree≤M) {R:ℚ} (hR:1≤R)
    (hratio : ∀ m<L,(((JQ ι - m)*M:ℕ) :ℚ)≤R*((A - m:ℕ) :ℚ))
    (S:n5 (σ→F)) (hreg : ∀ x∈S,oZ x s≠0)
    (hA : ∀ x∈S,A ≤ {i | oZ x (cuts i)=0}.ncard)
    (hterminal : ∀ J:lz (cy σ F),L ≤ {i | cuts i∈J}.ncard →
      (((S:Set (σ→F))∩yJ F J).ncard:ℚ)≤R)
    (P:lz (cy σ F)) [P.IsPrime] (W:n5 (σ→F)) (hW:W⊆S)
    (hzero : ∀ x∈W,x∈yJ F P) :
    (W.card:ℚ)≤u9 P*R^(G7 P).natDegree := by
  classical
  generalize hd: (G7 P).natDegree=d
  induction d using Zf generalizing P W with
  | h d ih =>
    rcases W.eq_empty_or_nonempty with rfl | ⟨x₀,hx₀⟩
    · simpa using ze (zcN P) (pow_nonneg (zero_le_one.trans hR) d)
    rcases d with _ | e
    · have hfin:=Zi (K:=F) P hd
      have hcard:=SM
        (fun x (hx :x∈(W:Set (σ→F)))=>hzero x hx) hfin.1
      rw [Du] at hcard
      simpa using (by exact_mod_cast hcard: (W.card:ℚ)≤_).trans hfin.2
    let keep:n5 ι:=Finset.univ.filter fun i=>cuts i∈P
    have hkeep:keep.card = {i | cuts i∈P}.ncard:= by
      rw [← Du]
      congr 1
      ext i
      simp [keep]
    by_cases hpers :L≤keep.card
    · have hc:W.card≤((S:Set (σ→F))∩yJ F P).ncard:= by
        rw [← Du]
        exact SM (fun x hx=>⟨hW hx,hzero x hx⟩)
      have hdegP:=caj P x₀ (hzero x₀ hx₀)
      calc
        (W.card:ℚ)≤(((S:Set (σ→F))∩yJ F P).ncard:ℚ) := by exact_mod_cast hc
        _≤R:=hterminal P (hkeep ▸ hpers)
        _≤u9 P*R^(e+1) := by
          calc
            R=1*R^(1 :ℕ) := by ring
            _≤u9 P*R^(e+1) :=
              mul_le_mul hdegP (pow_le_pow_right₀ hR (by omega)) (by positivity) (by linarith)
    let rel : (σ→F)→ι→Prop := fun x i=>oZ x (cuts i)=0
    let c:ℚ:=((A - keep.card:ℕ) :ℚ)
    have hc:0<c:= by
      change (0:ℚ)<((A - keep.card:ℕ) :ℚ)
      exact_mod_cast (by omega :0<A - keep.card)
    have hlowNat :W.card*(A - keep.card) ≤ ∑ i∈keepᶜ,(W.bipartiteBelow rel i).card:= by
      refine Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow rel keep fun x hx => ?_
      rw [← Du,Finset.coe_bipartiteAbove]
      simpa [rel] using hA x (hW hx)
    have hlow: (W.card:ℚ)*c ≤ ∑ i∈keepᶜ,((W.bipartiteBelow rel i).card:ℚ) := by
      change (W.card:ℚ)*((A - keep.card:ℕ) :ℚ)≤_
      exact_mod_cast hlowNat
    have hcut : ∀ i∈keepᶜ,((W.bipartiteBelow rel i).card:ℚ)≤M*u9 P*R^e := by
      intro i hi
      have hiP:cuts i∉P:= by simpa [keep] using hi
      rw [← Du,Finset.coe_bipartiteBelow]
      refine ncard_inter_cut_le_of_retained_le s hiP (hdeg i) W
        (fun x hx=>⟨hzero x hx,hreg x (hW hx)⟩) (by positivity) fun Q hQ => ?_
      have hQmin:=(Ideal.mem_retainedMinimalPrimes.mp hQ).1
      letI:Q.IsPrime :=hQmin.isPrime
      have hQdim: (G7 Q).natDegree=e := by
        have :=zdH hiP hQmin
        omega
      rw [a5X]
      exact ih e (by omega) Q _ (fun _ hx=>hW (Finset.mem_filter.mp hx).1)
        (fun _ hx=>(Finset.mem_filter.mp hx).2) hQdim
    have hupp : ∑ i∈keepᶜ,((W.bipartiteBelow rel i).card:ℚ) ≤
        ((JQ ι - keep.card:ℕ) :ℚ)*(M*u9 P*R^e) := by
      refine (Finset.sum_le_card_nsmul _ _ _ hcut).trans_eq ?_
      rw [NZ,Finset.card_compl]
    refine le_of_mul_le_mul_right (hlow.trans (hupp.trans ?_)) hc
    calc
      ((JQ ι - keep.card:ℕ) :ℚ)*(M*u9 P*R^e) =
          (((JQ ι - keep.card)*M:ℕ) :ℚ)*(u9 P*R^e) := by
        rw [zd]
        ring
      _≤(R*c)*(u9 P*R^e) :=
        mul_le_mul_of_nonneg_right (hratio keep.card (by omega))
          (ze  (zcN P) (pow_nonneg (zero_le_one.trans hR) e))
      _=(u9 P*R^(e+1))*c:= by rw [C5]; ring
private theorem bxi {F ι:Type*} [c9 F] [Fintype ι]
   (g s :cy (Fin 3) F) (hg:g≠0) (cuts :ι→cy (Fin 3) F)
   {A L M E :ℕ} (hLA:L≤A) (hgdeg:g.totalDegree≤E) (hdeg : ∀ i,(cuts i).totalDegree≤M)
   {R:ℚ} (hR:1≤R)
   (hratio : ∀ m<L,(((JQ ι - m)*M:ℕ) :ℚ)≤R*((A - m:ℕ) :ℚ))
   (S:n5 (Fin 3→F)) (hS : ∀ x∈S,oZ x g=0∧oZ x s≠0)
   (hA : ∀ x∈S,A ≤ {i | oZ x (cuts i)=0}.ncard)
   (hterminal : ∀ J:lz (cy (Fin 3) F),L ≤ {i | cuts i∈J}.ncard →
     (((S:Set (Fin 3→F))∩yJ F J).ncard:ℚ)≤R) :
   (S.card:ℚ)≤E*R^2 := by
 classical
 let family :=(ov {g}).retainedMinimalPrimes s
 have hmem (Q) (hQ:Q∈family) :g∈Q :=
   (Ideal.mem_retainedMinimalPrimes.mp hQ).1.le (z5J g)
 have hdim : ∀ Q∈family,(G7 Q).natDegree≤2 := by
   intro Q hQ
   simpa [Nat.card_eq_fintype_card] using natDegree_affineHilbertPolynomial_le_of_mem hg (hmem Q hQ)
 have hsum : ∑ Q∈family,u9 Q≤(E :ℚ) := by
   letI: (⊥ : lz (cy (Fin 3) F)).IsPrime :=Ideal.isPrime_bot
   have hnot:g∉(⊥ : lz (cy (Fin 3) F)) := by simpa using hg
   simpa only [family,bot_sup_eq,affineDegree_bot,mul_one] using
     zcE s hnot hgdeg
 refine card_le_mul_pow_of_forall_mem_zeroLocus family hdim hsum hR S (fun x hx => ?_) ?_
 · have hxg:x∈yJ F (ov {g}) :=mem_zeroLocus_iff_le_ker_aeval.mpr
     ((Qx _).mpr (RingHom.mem_ker.mpr (hS x hx).1))
   exact zwb _ s x hxg (hS x hx).2
 · intro Q hQ
   letI:Q.IsPrime :=(Ideal.mem_retainedMinimalPrimes.mp hQ).1.isPrime
   rw [a5X]
   exact ccD s cuts hLA hdeg hR hratio S
     (fun x hx=>(hS x hx).2) hA hterminal Q _
     (fun _ hx=>(Finset.mem_filter.mp hx).1) (fun _ hx=>(Finset.mem_filter.mp hx).2)
open K1
end
end wT
end
section
namespace bRj
noncomputable section
open aR oR yz Qp aeB
open MeasureTheory Set Filter
open scoped Topology Pointwise ENNReal
private def Ui (b j c h:ℝ) :Set iz :=
 {x | (∀ k,0≤x k)∧x 0 + x 1 + x 2≤b ∧
   x 1+2*x 2≤j∧x 2≤ c∧x 3≤h}
private def aXK (P:Set iz) (s :nI) (h:ℕ) (t:ℝ) :
  Set iz :=
 Ui ((s.b:ℝ)+t*UB P) ((s.j:ℝ)+t*V9 P)
  ((s.t:ℝ)+t*WA P) h
open private a9x fbW fr7 bkw frB fsM from ProximityPrize.SubmissionLower.BG
private theorem c7t {b j c h:ℝ} (hc:0≤ c) (hbj:j≤b)
    (hjc:2*c≤j) (hh:0≤h) :
    (oj (Ui b j c h)).toReal=h*c*(j - c)*(b - j/2) := by
  have hcap:Ui b j c h = {x | (fun i:Fin 3=>x i.castSucc)∈bkw b j c ∧
      x 3∈Icc 0 h} := by
    ext x
    simp only [Ui,bkw,mem_ofPred_eq,mem_Icc,Fin.forall_iff_castSucc (n:=3)]
    change ((0≤x 3 ∧ ∀ i:Fin 3,0≤x i.castSucc) ∧
      x 0 + x 1 + x 2≤b∧x 1+2*x 2≤j∧x 2≤ c∧x 3≤h) ↔
      ((∀ i:Fin 3,0≤x i.castSucc)∧x 0 + x 1 + x 2≤b ∧
      x 1+2*x 2≤j∧x 2≤ c)∧0≤x 3∧x 3≤h
    tauto
  have hm:MeasurableSet (Ui b j c h) := by
    rw [hcap]
    exact ((frB _ _ _).preimage
      (measurable_pi_iff.mpr (fun i=>zk2 i.castSucc))).inter
        (measurableSet_Icc.preimage (zk2 3))
  have hbound (v :iz) (hv :v∈Ui b j c h) :
      (fbW v).1∈Icc 0 h:=⟨hv.1 3,hv.2.2.2.2⟩
  have hvol:oj (Ui b j c h)=oj (bkw b j c)*Hw h:= by
    rw [a9x fbW (volume_preserving_piFinSuccAbove _ _) hm hbound]
    calc
      _ = ∫⁻ _ in Icc 0 h,oj (bkw b j c) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro z hz
        dsimp only
        congr 1
        ext v
        have h3: (@Fin.snoc 3 (fun _=>ℝ) v z) 3=z :=
          @Fin.snoc_last 3 (fun _=>ℝ) z v
        simp [hcap,fr7,h3,hz.1,hz.2]
      _ = _:= by rw [setLIntegral_const,Real.volume_Icc,NI]
  have hn:0≤ c*(j - c)*(b - j/2) :=
    ze (ze hc (by linarith)) (by linarith)
  rw [hvol,fsM hc hbj hjc,zFP,
    Mz hn,Mz hh]
  ring
private theorem fUk (b j c h:ℝ) :
   Ui b j c h=Ui b j (min c (j/2)) h:= by
 ext x
 simp only [Ui,mem_ofPred_eq,le_min_iff]
 constructor
 · rintro ⟨hx,hb,hj,hc,hh⟩
   exact ⟨hx,hb,hj,⟨hc,by linarith [hx 1]⟩,hh⟩
 · rintro ⟨hx,hb,hj,⟨hc,_⟩,hh⟩
   exact ⟨hx,hb,hj,hc,hh⟩
private theorem gqq (P:Set iz) (s :nI) (h:ℕ)
    (hs :Qp.bF s) (hjb:s.j<s.b) (htop:0<s.t) :
    th
      (fun t:ℝ=>((oj (aXK P s h t)).toReal -
        (oj (nD s h)).toReal)/t)
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (aeB.ajg s h
        (aeB.UB P) (aeB.V9 P)
        (aeB.WA P))) := by
  classical
  let b:ℝ:=s.b
  let j:ℝ:=s.j
  let c:ℝ:=s.t
  let B:ℝ:=UB P
  let J:ℝ:=V9 P
  let T:ℝ:=WA P
  let U:ℝ:=if 2*c=j then min T (J/2) else T
  have hc:0<c:= by
    change (0:ℝ)<(s.t:ℝ)
    exact_mod_cast htop
  have hj:j<b:= by
    change (s.j:ℝ)<(s.b:ℝ)
    exact_mod_cast hjb
  have hcj:2*c≤j:= by
    change 2*(s.t:ℝ)≤(s.j:ℝ)
    exact_mod_cast hs.2
  have hline (a m:ℝ) :HasDerivAt (fun t:ℝ=>a+t*m) m 0:= by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const m).const_add a
  have hpositive : ∀ᶠ t:ℝ in 𝓝[Set.Ioi 0] (0:ℝ),0<c+t*U :=
    (Filter.Tendsto.eventually
      (show th (fun t:ℝ=>c+t*U) (𝓝 0) (𝓝 c) by
        simpa [ContinuousAt] using (hline c U).continuousAt) (Ioi_mem_nhds hc)).filter_mono Dw
  have hchamber : ∀ᶠ t:ℝ in 𝓝[Set.Ioi 0] (0:ℝ),j+t*J<b+t*B :=
    ((hline j J).continuousAt.eventually_lt (hline b B).continuousAt (by simpa using hj)).filter_mono
      Dw
  have heff : ∀ᶠ t:ℝ in 𝓝[Set.Ioi 0] (0:ℝ),
      min (c+t*T) ((j+t*J)/2)=c+t*U:= by
    by_cases heq :2*c=j
    · filter_upwards [MO (a :=(0:ℝ)) (s :=Ioi 0)] with t ht
      have ht' : 0≤t:=(show 0<t from ht).le
      rw [show (j+t*J)/2=c+t*(J/2) by rw [← heq]; ring]
      by_cases hTJ:T≤J/2
      · rw [Wm (JK (t7 hTJ ht') _)]
        simp [U,heq,Wm hTJ]
      · have hJT:=(lt_of_not_ge hTJ).le
        rw [min_eq_right (JK (t7 hJT ht') _)]
        simp [U,heq,min_eq_right hJT]
    · have hnear : ∀ᶠ t:ℝ in 𝓝 (0:ℝ),c+t*T<(j+t*J)/2 :=
        (hline c T).continuousAt.eventually_lt
          ((hline j J).div_const 2).continuousAt (by
            simp only [zero_mul,zS]
            linarith [lt_of_le_of_ne hcj heq])
      filter_upwards [hnear.filter_mono (Dw
        (s :=Ioi (0:ℝ)))] with t ht
      simp [U,heq,Wm ht.le]
  let f := fun t:ℝ=>(h:ℝ)*(c+t*U) *
    ((j+t*J)-(c+t*U))*((b+t*B)-(j+t*J)/2)
  have hcoef : (j - 2*c)*U=(j - 2*c)*T:= by
    by_cases heq :2*c=j
    · rw [show j - 2*c=0 by linarith,zero_mul,zero_mul]
    · simp [U,heq]
  have hf :HasDerivAt f ((h:ℝ)*(c*(j - c)*B +
      c*(b - j+c/2)*J+(j - 2*c)*(b - j/2)*T)) 0:= by
    convert ((((hline c U).const_mul (h:ℝ)).mul
      ((hline j J).sub (hline c U))).mul
      ((hline b B).sub ((hline j J).div_const 2))) using 1
    simp only [Pi.mul_apply,Pi.sub_apply,zero_mul,zS]
    calc
      _=(h:ℝ)*(c*(j - c)*B+c*(b - j+c/2)*J +
          (b - j/2)*((j - 2*c)*T)) := by ring
      _ = _:= by rw [← hcoef]; ring
  have hlim:=hf.tendsto_slope_zero_right
  have hbase : (oj (nD s h)).toReal=f 0:= by
    change (oj (Ui b j c h)).toReal= _
    rw [c7t hc.le hj.le hcj (by positivity)]
    simp [f]
  apply hlim.congr'
  filter_upwards [hpositive,hchamber,heff] with t hp hb he
  have hclip:2*(c+t*U)≤j+t*J:= by
    rw [← he]
    linarith [min_le_right (c+t*T) ((j+t*J)/2)]
  change t⁻¹•(f (0+t) - f 0) =
    ((oj (Ui (b+t*B) (j+t*J) (c+t*T) h)).toReal -
      (oj (nD s h)).toReal)/t
  rw [fUk,he,c7t hp.le hb.le hclip (by positivity),hbase,
    yB ,v8 ,PD ]
  exact t6 _ _
private def bfP:Matrix (Fin 6) (Fin 4) ℝ :=
 ![![1,1,1,0],![0,1,2,0],![0,0,1,0],![-1,0,0,0],![0,-1,0,0],![0,0,-1,0]]
private def form (i:Fin 6) :iz →ₗ[ℝ] ℝ :=
 (LinearMap.proj i).comp (KH bfP)
private theorem bd6 (i:Fin 6) (x :iz) :
   form i x=(![x 0 + x 1 + x 2,x 1+2*x 2,x 2,-x 0,-x 1,-x 2] :
     Fin 6→ℝ) i:= by
 change ((KH bfP) x) i= _
 rw [ Xu]
 fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,x7,bfP]
private theorem bGT (i:Fin 6) :
    (form i:iz→ℝ) =
      (fun x=>(![x 0 + x 1 + x 2,x 1+2*x 2,x 2,-x 0,-x 1,-x 2] :
        Fin 6→ℝ) i) :=
  funext (bd6 i)
private def Ca (s :nI) :Fin 6→ℝ := ![s.b,s.j,s.t,0,0,0]
private theorem bJb {b j c h:ℝ} {x :iz} :
  x∈Ui b j c h↔x 3∈Icc 0 h ∧
    ∀ i,form i x≤(![b,j,c,0,0,0] :Fin 6→ℝ) i:= by
 simp [Ui,Fin.forall_fin_succ,bd6]
 tauto
private def support (P:Set iz) (i:Fin 6) :ℝ:=sSup (form i '' P)
private theorem gxw {P:Set iz} (hc:IsCompact P)
  (h0:0∈P) (i:Fin 6) :
  ∃ p∈P,form i p=support P i ∧ ∀ q∈P,form i q≤ support P i:= by
 obtain ⟨p,hp,hm⟩:=hc.exists_isMaxOn ⟨0,h0⟩ (form i).continuous_of_finiteDimensional.continuousOn
 have hle : ∀ q∈P,form i q≤form i p:= fun q hq=>hm hq
 have hsup:support P i=form i p:= by
  refine wY (csSup_le ⟨form i p,mem_image_of_mem _ hp⟩ ?_) (le_csSup ?_ (mem_image_of_mem _ hp))
  · rintro _ ⟨q,hq,rfl⟩
    exact hle q hq
  · exact ⟨form i p,by rintro _ ⟨q,hq,rfl⟩; exact hle q hq⟩
 exact ⟨p,hp,hsup.symm,hsup ▸ hle⟩
private theorem c0h {P:Set iz} (h0:0∈P)
   (hsub:P⊆nD S9 0) {s :nI} {h:ℕ} {t:ℝ} {x :iz} :
   x∈aXK P s h t↔x 3∈Icc 0 (h:ℝ) ∧
     ∀ i,form i x≤Ca s i+t*support P i:= by
 rw [aXK,bJb]
 have hlow (i:Fin 6) (hi:3≤ i.val) :support P i=0:= by
   have hzero : (0:ℝ)∈form i '' P:=⟨0,h0,qm _⟩
   have hub:0∈upperBounds (form i '' P) := by
     rintro _ ⟨p,hp,rfl⟩
     have hn:=(hsub hp).1
     fin_cases i <;> norm_num at hi
     all_goals simpa [bd6] using hn _
   exact wY (csSup_le ⟨0,hzero⟩ hub) (le_csSup ⟨0,hub⟩ hzero)
 refine and_congr_right (fun _=>forall_congr' (fun i => ?_))
 fin_cases i
 · simp [Ca,support,UB,bGT]
 · simp [Ca,support,V9,bGT]
 · simp [Ca,support,WA,bGT]
 all_goals rw [hlow _ (by decide)]; simp [Ca]
private abbrev aBV:=Fin 6×Fin 6
private def bfO (p:aBV) :Prop :=
 p.1.val<3∧p.1≠p.2∧(p.1≠2∨p.2≠5)
private instance (p:aBV) :Decidable (bfO p) := by
 unfold bfO
 infer_instance
private def remaining (p:aBV) :Fin 4 :=
 (![![0,2,1,2,2,1],![2,0,0,2,0,0],![1,0,0,1,0,0],0,0,0] :
   Fin 6→Fin 6→Fin 4) p.1 p.2
private def apu (p:aBV) :Matrix (Fin 4) (Fin 4) ℝ :=
 ![bfP p.1,bfP p.2,fun i=>if i=remaining p then 1 else 0,![0,0,0,1]]
private theorem grz (p:aBV) :
   (apu p).det=((apu p).submatrix Gn Gn).det:= by
 rw [Matrix.det_succ_row _ (u8 3),x7]
 have h0:apu p (u8 3) 0=0:=rfl
 have h1 :apu p (u8 3) 1=0:=rfl
 have h2 :apu p (u8 3) 2=0:=rfl
 have h3:apu p (u8 3) (u8 3)=1 :=rfl
 simp only [h0,h1,h2,vj,zero_mul,yB]
 change (-1 :ℝ)^6*apu p (u8 3) (u8 3) *
     ((apu p).submatrix (u8 3).succAbove (u8 3).succAbove).det= _
 rw [h3,Fin.succAbove_last]
 norm_num
private theorem grA (p:aBV) (hp:bfO p) : (apu p).det≠0:= by
 obtain ⟨i,j⟩:=p
 fin_cases i <;> fin_cases j <;> norm_num [bfO] at hp
 all_goals
  rw [grz,Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply,
   show (0:Fin 3).castSucc=(0:Fin 4) from rfl,
   show (1 :Fin 3).castSucc=(1 :Fin 4) from rfl,
   show (2 :Fin 3).castSucc=(2 :Fin 4) from rfl]
  norm_num [apu,bfP,remaining]
private theorem gry (p:aBV) (x :iz) :
   KH (apu p) x = ![form p.1 x,form p.2 x,x (remaining p),x 3] := by
 ext i
 fin_cases i
 · rfl
 · rfl
 · rw [ Xu]
   change (∑ k,(if k=remaining p then 1 else (0:ℝ))*x k)= _
   simp [ite_mul]
 · rw [ Xu]
   norm_num [Matrix.mulVec,dotProduct,x7,apu]
private def bwt (a :Fin 6→ℝ) (R e :ℝ) (p:aBV) :Set iz :=
 if bfO p then
   KH (apu p) ⁻¹'
     Icc (![a p.1-e,a p.2 - e,0,0] :iz) ![a p.1+e,a p.2+e,R,R]
 else ∅
private theorem gLm (a :Fin 6→ℝ) {R e :ℝ} (hR:0≤R) (he :0≤e)
   (p:aBV) :
   oj (bwt a R e p)≤Hw (|(apu p).det⁻¹| * 4*R^2*e^2) := by
 unfold bwt
 split_ifs with hp
 · rw [Measure.addHaar_preimage_linearMap volume (by rw [LinearMap.det_toLin']; exact grA p hp),
     LinearMap.det_toLin',zk7,Fin.prod_univ_four]
   have hwidth (w:ℝ) :w+e-(w-e)=2*e := by ring
   simp only [zbs,Matrix.cons_val_one,Matrix.cons_val_two,
     Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,hwidth,NI ]
   rw [← ENNReal.ofReal_mul (by positivity :0≤2*e),← ENNReal.ofReal_mul (by positivity :0≤2*e*(2*e)),
     ← zwu (by positivity :0≤2*e*(2*e)*R),
     ← zwu (abs_nonneg _)]
   apply le_of_eq
   congr 1
   ring
 · simp
private theorem cSP {P:Set iz} (hsub:P⊆nD S9 0)
  {x :iz} (hx :x∈P) (i:Fin 6) : |form i x| ≤ 250:= by
 have hp:=hsub hx
 have h0:=hp.1 0
 have h1 :=hp.1 1
 have h2 :=hp.1 2
 have hb:=hp.2.1
 change x 0 + x 1 + x 2≤(S9.b:ℝ) at hb
 norm_num [S9] at hb
 rw [abs_le,bd6]
 fin_cases i <;> simp <;> constructor <;> linarith
private theorem gqp {P:Set iz} (hP:OE P) (hsub:P⊆nD S9 0)
    (s :nI) (h:ℕ) (htop:0<s.t) :
    ∃ K:ℝ,∀ᶠ t:ℝ in 𝓝[Set.Ioi 0] (0:ℝ),
      0≤(oj (aXK P s h t)).toReal-(oj (t•P+nD s h)).toReal ∧
      (oj (aXK P s h t)).toReal-(oj (t•P+nD s h)).toReal≤K*t^2 := by
  have hc:IsCompact P:= by
    obtain ⟨v,hv,rfl⟩:=hP.polytope
    exact hv.isCompact_convexHull ℝ
  choose pt hpt heq hmax using gxw hc hP.zero_mem
  have hsup (i:Fin 6) :support P i≤250 :=
    (heq i).symm.trans_le ((le_abs_self _).trans (cSP hsub (hpt i) i))
  let R:ℝ:=(s.b:ℝ)+(h:ℝ)+250
  let coeff (p:aBV) :ℝ := |(apu p).det⁻¹| * 4*R^2*250^2
  have hR:0≤R:= by positivity
  refine ⟨∑ p,coeff p,?_⟩
  have htop' : (0:ℝ)<(s.t:ℝ) := by exact_mod_cast htop
  have hsmall : ∀ᶠ t:ℝ in 𝓝[Set.Ioi 0] (0:ℝ),t<(s.t:ℝ)/250 :=
    Dw (Iio_mem_nhds (div_pos htop' (by norm_num : (0:ℝ)<250)))
  have hone : ∀ᶠ t:ℝ in 𝓝[Set.Ioi 0] (0:ℝ),t<1 :=
    Dw (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [MO (a :=(0:ℝ)) (s :=Ioi 0),hone,hsmall]
      with t ht ht1 hts
  have ht' : 0<t:=ht
  let e :ℝ:=t*250
  have he :0≤e := by positivity
  let S:=aXK P s h t
  let C:=t•P+nD s h
  let E := fun p:aBV=>bwt (Ca s) R e p
  have hCS:C⊆S:= by
    rintro x hx
    obtain ⟨w,hw,z,hz,rfl⟩:=mem_add.mp hx
    obtain ⟨y,hy,hwy⟩:=mem_smul_set.mp hw
    subst w
    have hz' := bJb.mp (show z∈Ui s.b s.j s.t h from hz)
    refine (c0h hP.zero_mem hsub).mpr ⟨?_,fun i => ?_⟩
    · simpa [TZ,Mj,hP.zero_height y hy] using hz'.1
    · rw [qG,map_smul,v8]
      exact (add_le_add (t7 (hmax i y hy) ht'.le) (hz'.2 i)).trans_eq
        (add_comm _ _)
  have hcube :S⊆Icc (0:iz) (fun _=>R) := by
    intro x hx
    obtain ⟨hn,hb,_,_,hh⟩:=(show x∈Ui _ _ _ _ from hx)
    have htotal:UB P=support P 0:= by simp [UB,support,bGT]
    have hbx :x 0 + x 1 + x 2≤(s.b:ℝ)+t*250:= by
      rw [htotal] at hb
      exact hb.trans (JK (t7 (hsup 0) ht'.le) _)
    refine ⟨hn,fun i => ?_⟩
    have h0:=hn 0
    have h1 :=hn 1
    have h2 :=hn 2
    have hH :0≤(h:ℝ) := by positivity
    have hB:0≤(s.b:ℝ) := by positivity
    fin_cases i <;> dsimp [R] <;> linarith
  have hcover :S⊆C ∪ ⋃ p,E p:= by
    intro x hx
    by_cases hxc:x∈C
    · exact Or.inl hxc
    have hb:=(c0h hP.zero_mem hsub).mp hx
    have hbase :x∉nD s h:= fun h =>
      hxc (mem_add.mpr ⟨0,⟨0,hP.zero_mem,smul_zero _⟩,x,h,yB _⟩)
    have hviol : ¬ ∀ i,form i x≤Ca s i :=
      fun h=>hbase (bJb.mpr ⟨hb.1,h⟩)
    push Not at hviol
    obtain ⟨i,hi⟩:=hviol
    let y :=x - t•pt i
    have hyh:y 3∈Icc 0 (h:ℝ) := by
      simpa [y,Pi.sub_apply,Mj,hP.zero_height _ (hpt i)] using hb.1
    have hy :y∉nD s h:= fun h =>
      hxc (mem_add.mpr ⟨t•pt i,⟨pt i,hpt i,rfl⟩,y,h,by dsimp [y]; abel⟩)
    have hother : ¬ ∀ j,form j y≤Ca s j :=
      fun h=>hy (bJb.mpr ⟨hyh,h⟩)
    push Not at hother
    obtain ⟨j,hj⟩:=hother
    have hshift (k :Fin 6) :form k y=form k x - t*form k (pt i) := by
      simp [y,v8]
    have hji:i≠j:= by
      rintro rfl
      rw [hshift,heq] at hj
      linarith [hb.2 i]
    have hlo:Ca s j-e≤form j x := by
      have h:=(abs_le.mp (cSP hsub (hpt i) j)).1
      rw [hshift] at hj
      dsimp [e]
      linarith [t7 h ht'.le]
    have hhi (k :Fin 6) :form k x≤Ca s k+e :=
      (hb.2 k).trans (JK (t7 (hsup k) ht'.le) _)
    have hpar :bfO (i,j) := by
      refine ⟨?_,hji,?_⟩
      · have hn : ∀ k :Fin 4,0≤x k :=(hcube hx).1
        fin_cases i <;> norm_num [Ca,bd6] at hi ⊢
        · exact (XJ (hn 0)) hi
        · exact (XJ (hn 1)) hi
        · exact (XJ (hn 2)) hi
      · by_contra hn
        push Not at hn
        obtain ⟨rfl,rfl⟩:=hn
        simp [Ca,bd6] at hi hlo
        linarith [show e<(s.t:ℝ) from (WD (by norm_num : (0:ℝ)<250)).mp hts]
    refine Or.inr (mem_iUnion.mpr ⟨(i,j),?_⟩)
    change x∈bwt _ _ _ _
    simp only [bwt,hpar,↓Fz ,mem_preimage,gry]
    have hxl:=(hcube hx).1
    have hxu:=(hcube hx).2
    constructor <;> intro k <;> fin_cases k
    · exact (sub_le_self _ he).trans hi.le
    · exact hlo
    · exact hxl (remaining (i,j))
    · exact hxl 3
    · exact hhi i
    · exact hhi j
    · exact hxu (remaining (i,j))
    · exact hxu 3
  have hevol:oj (⋃ p,E p)≤Hw ((∑ p,coeff p)*t^2) := by
    calc
      _ ≤ ∑ p,oj (E p) :=measure_iUnion_fintype_le _ _
      _ ≤ ∑ p,Hw (coeff p*t^2) := by
        apply wB
        intro p _
        have h:=gLm (Ca s) hR he p
        convert h using 2
        dsimp [coeff,e]
        ring
      _ = _:= by
        rw [JW,ENNReal.ofReal_sum_of_nonneg (fun p _=> by positivity)]
  have hS:oj S ≠ ∞ := Xo hcube isCompact_Icc.measure_ne_top
  have hC:oj C ≠ ∞ := Xo hCS hS
  have hevol' : oj S≤oj C+ENNReal.ofReal ((∑ p,coeff p)*t^2) :=
    (Bf hcover).trans ((measure_union_le _ _).trans (JK hevol _))
  constructor
  · exact sub_nonneg.mpr (LO hS (Bf hCS))
  · have h:=LO (ENNReal.add_ne_top.mpr ⟨hC,Up⟩) hevol'
    rw [ENNReal.toReal_add hC Up,Mz (by positivity)] at h
    exact sub_le_iff_le_add'.mpr h
theorem proof :aeB.c2 := by
  intro P hP hsub s h hs hjb htop _
  obtain ⟨K,hK⟩:=gqp hP hsub s h htop
  let f := fun t:ℝ =>
    ((oj (aXK P s h t)).toReal-(oj (nD s h)).toReal)/t
  have hupper :=gqq P s h hs hjb htop
  have hzero :th (fun t:ℝ=>K*t) (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
    have hid :th (fun t:ℝ=>t) (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) :=
      tendsto_id.mono_left Dw
    simpa using hid.const_mul K
  have hlower :th (fun t=>f t - K*t) (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (ajg s h (UB P) (V9 P) (WA P))) := by
    simpa using hupper.sub hzero
  apply hlower.squeeze' hupper
  · filter_upwards [hK,MO (a :=(0:ℝ)) (s :=Set.Ioi 0)] with t ht htpos
    have hpos :0<t:=htpos
    have he :=(div_le_iff₀ hpos).mpr (show _≤K*t*t by
      simpa only [pow_two,pU] using ht.2)
    have hd:f t - apK P (nD s h) t =
        ((oj (aXK P s h t)).toReal -
          (oj (t•P+nD s h)).toReal)/t:= by
      unfold f apK
      rw [← sub_div]
      congr 1
      ring
    linarith
  · filter_upwards [hK,MO (a :=(0:ℝ)) (s :=Set.Ioi 0)] with t ht htpos
    have hpos :0<t:=htpos
    exact zrZ (by linarith [ht.1]) hpos.le
end
end bRj
end
section
namespace aY0
noncomputable section
open as3 MvPolynomial
open zP (xB fZ)
open scoped nonZeroDivisors
private abbrev as0 (A:N9) :=cy (Slot A) (xB A)
private def Nk (A:N9) (i:Fin 4) :as0 A :=
 ∑ a : ↥(A i),C (lI ⟨i,a⟩)*lI ⟨i,a⟩
private def Xk (A:N9) (b: (j:Fin 4) → ↥(A j)) :as0 A :=
 ∏ j:Fin 4,lI ⟨j,b j⟩
private def DX (A:N9) (k :ℕ) :lz (as0 A) :=
 ov (Nk A '' {i:Fin 4 | i.val<k})
private def O6 (A:N9) (k :ℕ) :lz (as0 A) :=
 Nb A (xB A) ⊔ DX A k
private abbrev swap (A:N9) :=commAlgEquiv nU (Slot A) (Slot A)
private def toModel (A:N9) :as0 A →+* adl A :=
 (oy (lV (Nb A nU))).comp (swap A).toRingHom
private theorem ctG (A:N9) :u5 (toModel A) :=
 (MvPolynomial.map_surjective (lV (Nb A nU)) uh).comp (f:=⇑(swap A).toRingHom) (swap A).surjective
private theorem ctF (A:N9) :
   sS (toModel A)=Nb A (xB A) := by
 have hswap: (swap A).toRingHom.comp (oy (C (σ:=Slot A)))=C:= by
   apply t8
   · intro c
     simp [swap]
   · intro v
     simp [swap]
 have hker :sS (swap A).toRingHom = ⊥ :=
   (RingHom.injective_iff_ker_eq_bot (swap A).toRingHom).mp (swap A).injective
 rw [toModel,← zEW,MvPolynomial.ker_map,Ideal.mk_ker,← hswap,
   ← zR,SW (swap A).toRingHom (swap A).surjective,
   ← Un,hker,
   Oc,bsj]
private theorem bxM (A:N9) (b: (j:Fin 4) → ↥(A j)) :
  toModel A (Xk A b)=C (avA A b) := by
 simp [ Xk,toModel,avA,coordinate]
private theorem bq8 (A:N9) (k :ℕ) :
  O6 A k=(Wd A k).comap (toModel A) := by
 have hmap : (DX A k).map (toModel A)=Wd A k := by
  rw [DX,Wd,uJ,Set.image_image]
  congr 1
  apply S1
  intro i _
  simp [Nk,a5P,toModel,coordinate]
  exact vw rfl (fun _ _=>t6 _ _)
 rw [← hmap,SW _ (ctG A),
  ← Un,ctF,O6,sup_comm]
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev ayQ (A:N9) :=aU (as0 A) (vJ A)
private theorem bpU (A:N9) (b: (j:Fin 4) → ↥(A j)) :
  ayQ A (Xk A b)=GW A b:= by
 change oy (aU (xB A) (fZ A))
  (Xk A b)=GW A b
 simp only [ Xk,GW,map_prod,map_X]
private theorem bFK (A:N9) (k :ℕ) :
  (O6 A k).map (ayQ A)=ke A k := by
 change (O6 A k).map
  (oy (aU (xB A) (fZ A)))=ke A k
 rw [O6,II,bsj,
  ← ce5,ke,DX,uJ,Set.image_image]
 congr 2
 apply S1
 intro i _
 simp only [Nk,T2,sI,nq,map_C,map_X]
set_option maxHeartbeats 800000 in
theorem proof :as3.c2 := by
 classical
 intro A hz i b f n hf
 let k :=i.val+1
 let b₀ (j:Fin 4) : ↥(A j) :=⟨0,hz j⟩
 let I:=O6 A k
 let e :=ayQ A
 let M:=(xB A)⁰.map (C (σ:=Slot A))
 have :G9 M (vJ A) :=
   zEY (xB A)⁰ (fZ A)
 obtain ⟨⟨p,s⟩,hs⟩:=IsLocalization.surj M f
 change f*e s=e p at hs
 have hc:e (Xk A b₀)=ab5 A hz :=bpU A b₀
 have hp:e (Xk A b₀^n*p)∈I.map e := by
   rw [show I.map e=ke A k from bFK A k,nq,xW,hc,← hs,
     ← pU]
   exact (ke A k).mul_mem_right _ hf
 obtain ⟨d,hd,hpre⟩:=(zi M _ I _).mp hp
 have hpre' : Xk A b₀^n*(d*p)∈O6 A k := by
   rw [JM (Xk A b₀^n) d p]
   exact hpre
 have hmod:C (avA A b₀)^n*toModel A (d*p)∈Wd A k := by
   rw [bq8] at hpre'
   change toModel A (Xk A b₀^n*(d*p))∈Wd A k at hpre'
   simpa only [nq,xW,bxM] using hpre'
 obtain ⟨m,hm⟩:=b9l A k b (bsI A b₀) (toModel A (d*p)) n hmod
 have hm' : Xk A b^m*(d*p)∈I:= by
   change _∈O6 A k
   rw [bq8]
   change toModel A (Xk A b^m*(d*p))∈Wd A k
   simpa only [nq,xW,bxM] using hm
 have hresult :=zf e hm'
 rw [show I.map e=ke A k from bFK A k,nq,xW,bpU,
   nq,← hs] at hresult
 have hds :wR (e d) :=Ze (vJ A) ⟨d,hd⟩
 have hss :wR (e s) :=Ze (vJ A) s
 refine ⟨m,(Ideal.unit_mul_mem_iff_mem _ (hds.mul hss)).mp ?_⟩
 rw [pU (e d) (e s),JM (e s) (GW A b^m),
   JM (e d) (GW A b^m),t6 (e s) f]
 exact hresult
end
end aY0
end
section
namespace bak
open yz zP
open scoped Pointwise
noncomputable section
private theorem df4 {ι:Type*} (t:n5 ι) (D:Set pz)
  (k :ι→ℕ) (v :ι→pz) (h : ∀ i∈t,v i∈k i•D) :
  (∑ i∈t,v i)∈(∑ i∈t,k i)•D:= by
 rw [← Finset.sum_nsmul_assoc]
 exact zlD t _ v h
theorem d4w {D:Set pz} (hD:D.Finite) (hzero :0∈D)
    (hunit : ∀ a∈D,∀ j,0<a j→vi j 1∈D) :
    ∃ c:ℕ,∀ (m:ℕ) (y :iz),y∈LK D →
      ∃ a∈(m+c)•D,∀ j,(a j:ℝ)≤(m:ℝ)*y j ∧
        (m:ℝ)*y j<(a j:ℝ)+1 := by
  classical
  let _:Fintype D:=hD.fintype
  let bound (j:Fin 4) :ℕ := ∑ a :D,a.val j
  refine ⟨∑ j,bound j,?_⟩
  intro m y hy
  let v (a :D) :iz :=an7 a.val
  have himage :an7 '' D =vk v := by
    ext x
    exact ⟨fun ⟨a,ha,h⟩=>⟨⟨a,ha⟩,h⟩,fun ⟨a,h⟩=>⟨a.val,a.property,h⟩⟩
  rw [LK,himage,convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨t,w,hw,hsum,hy⟩:=hy
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hy
  let u (a :D) :ℝ:=(m:ℝ)*w a
  let k (a :D) :ℕ := ⌊u a⌋₊
  have hu (a :D) (ha :a∈t) :0≤u a :=ze (zm _) (hw a ha)
  have hk (a :D) (ha :a∈t) : (k a :ℝ)≤u a :=Sv (hu a ha)
  have hdegrees : (∑ a∈t,k a)≤ m:= by
    apply (Nat.cast_le (α:=ℝ)).mp
    rw [SL]
    calc
      _ ≤ ∑ a∈t,u a :=wB hk
      _=(m:ℝ) := by simp [u,← yl,hsum]
  let r (j:Fin 4) :ℝ := ∑ a∈t,(u a-(k a :ℝ))*(a.val j:ℝ)
  let l (j:Fin 4) :ℕ := ⌊r j⌋₊
  have hr (j:Fin 4) :0≤ r j :=
    Finset.sum_nonneg fun a ha=>ze (sub_nonneg.mpr (hk a ha)) (zm _)
  have hbound (j:Fin 4) :l j≤bound j:= by
    apply Nat.floor_le_of_le
    calc
      r j ≤ ∑ a∈t,(a.val j:ℝ) := by
        refine wB (fun a _ => ?_)
        exact mul_le_of_le_one_left (zm _)
          (by have h:=Rm (u a); change u a<(k a :ℝ)+1 at h; linarith)
      _≤(bound j:ℝ) := by
        rw [show (bound j:ℝ) = ∑ a :D,(a.val j:ℝ) by simp [bound,SL]]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _=>zm _)
  have haxes (j:Fin 4) (hj:l j≠0) :vi j 1∈D:= by
    by_contra h
    have hv (a :D) :a.val j=0 :=
      Nat.eq_zero_of_not_pos (fun ha=>h (hunit a.val a.property j ha))
    exact hj (by simp [l,r,hv])
  let b:Exponent := ∑ a∈t,k a•a.val
  let d:Exponent := ∑ j,l j•vi j 1
  have hb:b∈(∑ a∈t,k a)•D :=
    df4 t D k _ (fun a _=>zfk a.property)
  have hd:d∈(∑ j,l j)•D:= by
    refine df4 t9 D l _ (fun j _ => ?_)
    by_cases hj:l j=0
    · simp [hj]
    · exact zfk (haxes j hj)
  have hbd:b+d∈(m + ∑ j,bound j)•D:= by
    apply Set.nsmul_subset_nsmul_right hzero (wA hdegrees (wB fun j _=>hbound j))
    rw [NY]
    exact NX hb hd
  refine ⟨b+d,hbd,fun j => ?_⟩
  have hdj:d j=l j:= by
    change (∑ i:Fin 4,l i•vi i 1) j=l j
    rw [ze7,Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  have hbj: (b j:ℝ) = ∑ a∈t,(k a :ℝ)*(a.val j:ℝ) := by
    simp [b,ze7,Finsupp.smul_apply,SL]
  have hyj: (m:ℝ)*y j = ∑ a∈t,u a*(a.val j:ℝ) := by
    rw [← hy]
    simp [v,an7,Finset.sum_apply,v8 ,u,yl,pU]
  have hdecomp: (m:ℝ)*y j=(b j:ℝ)+r j:= by
    rw [hyj,hbj]
    simp only [r,sub_mul,Finset.sum_sub_distrib]
    abel
  change ((b j+d j:ℕ) :ℝ)≤(m:ℝ)*y j ∧
    (m:ℝ)*y j<((b j+d j:ℕ) :ℝ)+1
  rw [GB,hdj,hdecomp]
  have hlo:=Sv (hr j)
  have hhi:=Rm (r j)
  change (l j:ℝ)≤ r j at hlo
  change r j<(l j:ℝ)+1 at hhi
  constructor <;> linarith
end
end bak
end
section
namespace bak
open yz zP Filter MeasureTheory
open scoped ENNReal Pointwise Topology
noncomputable section
local instance :Dist iz :=(xm :PseudoMetricSpace iz).toDist
theorem bqc {D:Set pz} (hD:D.Finite) (n:ℕ) :
   (n•D).Finite := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [NY ,one_nsmul]
   exact ih.add hD
private def aVe (n:ℕ) (a :pz) :Set iz :=
 Set.univ.pi fun j=>Set.Ico ((a j:ℝ)/n) (((a j:ℝ)+1)/n)
private def bep (n:ℕ) (T:Set pz) :Set iz :=
 ⋃ a∈T,aVe n a
private theorem bI7 {n:ℕ} (hn:0<n) {a :pz} {x :iz} :
  x∈aVe n a ↔ ∀ j,(a j:ℝ)≤(n:ℝ)*x j ∧
    (n:ℝ)*x j<(a j:ℝ)+1 := by
 have hn' : (0:ℝ)<n:=Nat.cast_pos.mpr hn
 simp only [aVe,Set.mem_pi,Mk,true_implies,Set.mem_Ico,
  div_le_iff₀ hn',WD hn']
 exact forall_congr' fun j=> by rw [t6 (x j)]
private theorem djx {n:ℕ} (hn:0<n) {T:Set pz}
   (hT:T.Finite) :
   (oj (bep n T)).toReal=(T.ncard:ℝ)/(n:ℝ)^4 := by
 classical
 have hdisj: (↑hT.toFinset :Set pz).PairwiseDisjoint (aVe n) := by
   intro a _ b _ hab
   refine Set.disjoint_left.mpr fun x ha hb=>hab ?_
   ext j
   have ha' := (bI7 hn).mp ha j
   have hb' := (bI7 hn).mp hb j
   have hx :0≤(n:ℝ)*x j:=(zm _).trans ha'.1
   exact ((Nat.floor_eq_iff hx).mpr ha').symm.trans ((Nat.floor_eq_iff hx).mpr hb')
 have hbox (a :pz) :MeasurableSet (aVe n a) :=
   MeasurableSet.univ_pi fun _=>zQD
 have hvol (a :pz) :
     oj (aVe n a)=(Hw (1/(n:ℝ)))^4 := by
   rw [aVe,zEj]
   have hlength (j:Fin 4) : ((a j:ℝ)+1)/n-(a j:ℝ)/n = 1/(n:ℝ) := by
     ring
   simp only [hlength,zJD,Finset.card_univ,Pf]
 have hunion :bep n T = ⋃ a∈hT.toFinset,aVe n a := by
   ext x
   simp only [bep,Set.mem_iUnion,zih]
 rw [hunion,measure_biUnion_finset hdisj (fun a _=>hbox a),Set.ncard_eq_toFinset_card T hT]
 simp only [hvol,Finset.sum_const]
 rw [ENNReal.toReal_nsmul,ENNReal.toReal_pow,Mz (by positivity)]
 rw [NZ,one_div,inv_pow,PD]
private theorem eFz {D:Set pz} (hD:0∈D) (n:ℕ) :
   n•LK D =(n:ℝ)•LK D:= by
 have h0: (0:iz)∈LK D :=
   WW ℝ _ ⟨0,hD,qm an7⟩
 induction n with
 | zero =>
   rw [zero_nsmul,Nat.cast_zero,Set.zero_smul_set ⟨0,h0⟩]
 | succ n ih =>
   rw [NY ,one_nsmul,ih,GB,RP]
   have hconv :Convex ℝ (LK D) :=zvj ℝ _
   rw [hconv.add_smul (zm n) R9,one_smul]
private theorem cUk {B D:Set pz} {n:ℕ}
   (hn:0<n) (hD:0∈D) {R:ℝ} (hR : ∀ b∈B,‖an7 b‖ ≤ R) :
   bep n (B+n•D)⊆KI ((1+R)/n) (LK D) := by
 have hn' : (0:ℝ)<n:=Nat.cast_pos.mpr hn
 intro x hx
 obtain ⟨a,ha,hx⟩:=Set.mem_iUnion₂.mp hx
 obtain ⟨b,hb,d,hd,rfl⟩:=Set.mem_add.mp ha
 have hscaled:an7 d∈(n:ℝ)•LK D:= by
   rw [← eFz hD n]
   apply Set.nsmul_subset_nsmul_left (WW ℝ _)
   rw [← Set.image_nsmul an7]
   exact ⟨d,hd,rfl⟩
 obtain ⟨y,hy,hyd⟩:=hscaled
 let z :iz :=(n:ℝ)⁻¹•an7 (b+d)
 have hxy :dist x z≤1/(n:ℝ) := by
   rw [dist_pi_le_iff (by positivity)]
   intro j
   obtain ⟨hlo,hhi⟩:=(bI7 hn).mp hx j
   change (↑((b+d) j) :ℝ)≤(n:ℝ)*x j at hlo
   change (n:ℝ)*x j<(↑((b+d) j) :ℝ)+1 at hhi
   have hz :z j=(↑((b+d) j) :ℝ)/n:= by
     change (n:ℝ)⁻¹*(↑((b+d) j) :ℝ)= _
     rw [PD,t6]
   rw [Real.dist_eq,hz,abs_le]
   have hlo' := (div_le_iff₀ hn').mpr (by simpa only [mul_comm] using hlo :
     (↑((b+d) j) :ℝ)≤x j*n)
   have hhi' : x j<((↑((b+d) j) :ℝ)+1)/n:=(WD hn').mpr
     (by simpa only [t6] using hhi)
   rw [add_div] at hhi'
   constructor <;> linarith
 have hzy :dist z y≤R/(n:ℝ) := by
   have heq :z=(n:ℝ)⁻¹•an7 b+y := by
     dsimp [z]
     rw [qG,smul_add,← hyd,smul_smul,inv_mul_cancel₀ hn'.ne',one_smul]
   rw [dist_eq_norm,heq,add_sub_cancel_right,norm_smul,Real.norm_eq_abs,
     abs_of_nonneg (inv_nonneg.mpr hn'.le),PD,t6 R]
   exact t7 (hR b hb) (inv_nonneg.mpr hn'.le)
 apply Metric.mem_cthickening_of_dist_le x y _ _ hy
 calc
   dist x y≤dist x z+dist z y :=dist_triangle _ _ _
   _≤1/(n:ℝ)+R/n:=add_le_add hxy hzy
   _ = _:=(add_div _ _ _).symm
theorem gAU {B D:Set pz} (hB:B.Finite) (hD:D.Finite)
    (hB0:0∈B) (hD0:0∈D)
    (hunit : ∀ a∈D,∀ j,0<a j→vi j 1∈D) :
    th (fun n:ℕ=>((B+n•D).ncard:ℝ)/(n:ℝ)^4)
      atTop (𝓝 (volume (LK D)).toReal) := by
  let K:=LK D
  have hK:IsCompact K:=(hD.image an7).isCompact_convexHull ℝ
  have hKfin:oj K ≠ ∞ := hK.measure_lt_top.ne
  obtain ⟨c,hc⟩:=d4w hD hD0 hunit
  obtain ⟨R,_,hR⟩:=(hB.image an7).isCompact.isBounded.exists_pos_norm_le
  have hupper :th (fun n:ℕ=>(oj (KI ((1+R)/n) K)).toReal)
      atTop (𝓝 (volume K).toReal) :=
    (ENNReal.continuousAt_toReal hKfin).tendsto.comp
      ((tendsto_measure_cthickening_of_isCompact hK).comp
        (ZJ (1+R)))
  let scale (n:ℕ) :ℝ:=((n - c:ℕ) :ℝ)/n
  have hscale :th scale atTop (𝓝 1) := by
    have hone :th (fun _:ℕ=>(1 :ℝ)) atTop (𝓝 1) :=tendsto_const_nhds
    have h:=hone.sub (ZJ (c:ℝ))
    simp only [NI] at h
    refine h.congr' ?_
    filter_upwards [Kp (c+1)] with n hn
    have hn' : (n:ℝ)≠0:=Nat.cast_ne_zero.mpr (by omega)
    simp only [scale,zjK (by omega :c≤n),sub_div,div_self hn']
  have hlower :th (fun n=>(scale n)^4*(oj K).toReal)
      atTop (𝓝 (volume K).toReal) := by
    simpa only [one_pow,yU] using (hscale.pow 4).mul tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [Kp (c+1)] with n hn
    have hn' : 0<n:= by omega
    have hnR: (0:ℝ)<n:=Nat.cast_pos.mpr hn'
    have hcover :scale n•K⊆bep n (B+n•D) := by
      rintro x ⟨y,hy,rfl⟩
      obtain ⟨a,ha,hcoord⟩:=hc (n - c) y hy
      rw [zxt (by omega :c≤n)] at ha
      refine Set.mem_iUnion₂.mpr ⟨a,?_,(bI7 hn').mpr ?_⟩
      · simpa only [yB] using NX hB0 ha
      · intro j
        have heq : (n:ℝ)*((scale n•y) j)=((n - c:ℕ) :ℝ)*y j:= by
          change (n:ℝ)*((((n - c:ℕ) :ℝ)/n)*y j)= _
          field_simp [hnR.ne']
        rw [heq]
        exact hcoord j
    have hvol: (oj (scale n•K)).toReal=(scale n)^4*(oj K).toReal:= by
      rw [Measure.addHaar_smul_of_nonneg volume (by positivity :0≤ scale n),
        Module.finrank_pi,Pf ,zFP,Mz  (by positivity)]
    have hbounded:zg0 (KI ((1+R)/n) K) :=
      hK.isBounded.cthickening
    have hfinite :oj (bep n (B+n•D)) ≠ ∞ :=
      Xo
        (cUk hn' hD0 (fun b hb=>hR _ ⟨b,hb,rfl⟩))
        hbounded.measure_lt_top.ne
    rw [← hvol,← djx hn' (hB.add (bqc hD n))]
    exact LO hfinite (Bf hcover)
  · filter_upwards [Kp (1 :ℕ)] with n hn
    have hn' : 0<n:= by omega
    rw [← djx hn' (hB.add (bqc hD n))]
    have hbounded:zg0 (KI ((1+R)/n) K) :=
      hK.isBounded.cthickening
    exact LO hbounded.measure_lt_top.ne (Bf
      (cUk hn' hD0 (fun b hb=>hR _ ⟨b,hb,rfl⟩)))
end
end bak
end
section
namespace bak
open yz zP
open scoped Pointwise
noncomputable section
private theorem cR9 (Eb:Fin 4→Set pz) (S:n5 (Fin 4))
   (h : ∀ i,(Eb i).Finite) : (∑ i∈S,Eb i).Finite := by
 classical
 induction S using Df with
 | empty=>simp
 | insert i S hi ih =>
   rw [z8 hi]
   exact (h i).add ih
private theorem cw6 (Eb:Fin 4→Set pz) (S:n5 (Fin 4))
  (h : ∀ i,0∈Eb i) :0 ∈ ∑ i∈S,Eb i:= by
 simpa only [Finset.sum_const_zero] using
  zlD S Eb (fun _=>0) (fun i _=>h i)
private theorem gG2 (Eb:Fin 4→Set pz) (S:n5 (Fin 4))
   (hzero : ∀ i,0∈Eb i)
   (hunit : ∀ i,∀ a∈Eb i,∀ j,0<a j→vi j 1∈Eb i)
   (a :pz) (ha :a ∈ ∑ i∈S,Eb i) (j:Fin 4) (hj:0<a j) :
   vi j 1 ∈ ∑ i∈S,Eb i:= by
 classical
 induction S using Df generalizing a with
 | empty =>
   simp only [Finset.sum_empty,Set.mem_zero] at ha
   subst a
   simp at hj
 | insert i S hi ih =>
   rw [z8 hi] at ha ⊢
   obtain ⟨b,hb,d,hd,rfl⟩:=Set.mem_add.mp ha
   change 0<b j+d j at hj
   by_cases hb' : 0<b j
   · simpa only [zS] using NX (hunit i b hb j hb') (cw6 Eb S hzero)
   · simpa only [yB] using NX (hzero i) (ih d hd (by omega))
private theorem dP8 (Eb:Fin 4→Set pz) (q n:ℕ) (S:n5 (Fin 4)) :
   (∑ i,uW q n S i•Eb i)=(∑ i,q•Eb i)+n•(∑ i∈S,Eb i) := by
 classical
 simp only [uW,NY ,vG]
 congr 1
 have h (i:Fin 4) : (if i∈S then n else 0)•Eb i =
     if i∈S then n•Eb i else 0:= by
   split_ifs <;> simp
 simp only [h,← zLJ,zuy,Zh]
 rw [Finset.sum_nsmul]
theorem proof :zP.c3:= by
 classical
 intro A hzero hdown q S
 let Eb (i:Fin 4) :Set Exponent:=A i
 let B := ∑ i:Fin 4,q•Eb i
 let D := ∑ i∈S,Eb i
 have hf (i:Fin 4) : (Eb i).Finite :=Finset.finite_toSet _
 have hz (i:Fin 4) :0∈Eb i:=hzero i
 have hunit (i:Fin 4) (a :pz) (ha :a∈Eb i) (j:Fin 4) (hj:0<a j) :
     vi j 1∈Eb i:= by
   apply hdown i ha
   intro k
   by_cases h:j=k
   · subst k
     simpa using (Nat.succ_le_of_lt hj)
   · simp [h]
 have hB0:0∈B:=cw6 (fun i=>q•Eb i) t9
   (fun i=>Set.zero_mem_nsmul (hz i))
 have hbodies :LK D = ∑ i∈S,LK (A i) := by
   simp only [D,Eb,LK,Set.image_finsetSum an7,convexHull_sum]
 have hexponents (n:ℕ) :TX A (uW q n S)=(B+n•D).ncard:= by
   unfold TX
   exact ox Set.ncard (dP8 Eb q n S)
 simp only [hexponents,← hbodies]
 exact gAU (cR9 _ _ (fun i=>bqc (hf i) q))
   (cR9 Eb S hf) hB0 (cw6 Eb S hz) (gG2 Eb S hz hunit)
end
end bak
end
section
namespace bRh
open ac0
open scoped nonZeroDivisors
private theorem efI {k B:Type} [c9 k] [oD B] [zE B]
    [oq k B] (x :B)
    (hx :Transcendental k (aU B (qJ B) x))
    (hsep:XB
      (zvb k ({aU B (qJ B) x} : Set (qJ B)))
      (qJ B)) :
    letI:oq (nX k) B:=(Ea x).toRingHom.toAlgebra
    zjp (nX k) (⊥ : lz B) := by
  let R:=nX k
  let L:=qJ B
  let F:=qJ R
  let u:L:=aU B L x
  let f :R →ₐ[k] L:=Ea u
  have hf :p7 f :=transcendental_iff_injective.mp hx
  let g:F →ₐ[k] L:=IsFractionRing.liftAlgHom hf
  have hg:g.fieldRange=zvb k ({u} : Set L) :=
    IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq hf
      (Algebra.adjoin_singleton_eq_range_aeval k u).symm
  let e :F ≃ₐ[k] g.fieldRange :=AlgEquiv.ofInjectiveField g
  let:XB g.fieldRange L:= by rwa [hg]
  let:oq F L:=g.toRingHom.toAlgebra
  let:XB F L :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) (by
      ext y
      change g (e.symm y)=(y :L)
      exact ox Re (e.apply_symm_apply y))
  let:oq R L:=f.toRingHom.toAlgebra
  let:IsScalarTower R F L:=zsL fun p=> by
    change f p=g (aU R F p)
    simp [g]
  let:HZ R F :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ:=F) R⁰
  let:HZ F L:=Algebra.FormallyUnramified.of_isSeparable F L
  let:HZ R L:=Algebra.FormallyUnramified.comp R F L
  let:oq R B:=(Ea x).toRingHom.toAlgebra
  let:G9 (⊥ : lz B).primeCompl L:= by
    rw [Ideal.primeCompl_bot]
    infer_instance
  let T:=oY (⊥ : lz B)
  let eB:=IsLocalization.algEquiv (⊥ : lz B).primeCompl L T
  let eR:L ≃ₐ[R] T :=
    { eB.toRingEquiv with
      commutes' := fun p=> by
        change eB (f p)=aU R T p
        have hp:f p=aU B L (aU R B p) :=
          Polynomial.aeval_algHom_apply (zE2 k B L) x p
        rw [hp,eB.commutes,Ee R B T] }
  exact Algebra.FormallyUnramified.of_equiv eR
private theorem fSP {R B:Type} [oD R] [oD B] [oq R B]
   [WK R B] (b:B)
   [HZ R (qx b)]
   (p:lz R) [p.IsMaximal] {d:R} (hd:d∉p) (hb:b∣aU R B d) :
   (p.map (aU R B)).IsRadical:= by
 let S:=qx b
 let J:=p.map (aU R B)
 let:c9 (R ⧸ p) :=Ideal.Quotient.field p
 have hd' : wR (lV J (aU R B d)) := by
   have hu:wR (lV p d) :=
     isUnit_iff_ne_zero.mpr (fun h=>hd ((zc).mp h))
   exact hu.map (aU (R ⧸ p) (B ⧸ J))
 have hunit :wR (lV J b) :=
   zNU (map_dvd (lV J) hb) hd'
 let:WK B S:=Algebra.EssFiniteType.of_isLocalization S (.powers b)
 let:WK R S:=Algebra.EssFiniteType.comp R B S
 have hrad: (J.map (aU B S)).IsRadical:= by
   change ((p.map (aU R B)).map (aU B S)).IsRadical
   rw [zR,← IsScalarTower.algebraMap_eq R B S]
   exact Algebra.FormallyUnramified.isRadical_map_isMaximal R S p
 intro z hz
 obtain ⟨n,hn⟩:=Ideal.mem_radical_iff.mp hz
 have hzn:aU B S z^n∈J.map (aU B S) := by
   rw [← xW]
   exact zf _ hn
 have hz' := hrad (Ideal.mem_radical_iff.mpr ⟨n,hzn⟩)
 obtain ⟨s,hs,hsz⟩ :=
   (zi (.powers b) S J z).mp hz'
 obtain ⟨m,rfl⟩:=hs
 rw [← zc,nq,xW] at hsz
 exact Ideal.Quotient.eq_zero_iff_mem.mp ((hunit.pow m).mul_right_eq_zero.mp hsz)
theorem proof :ac0.c3:= by
  classical
  intro k σ _ _ _ I hI a hfin hsep
  let:I.IsPrime :=hI
  let B:=cy σ k ⧸ I
  let x :B:=lV I (P5 a)
  let:oq (nX k) B:=(VO I a).toRingHom.toAlgebra
  let:oz (nX k) B:=hfin
  let:zjp (nX k) (⊥ : lz B) :=
    efI x hsep.1 hsep.2
  obtain ⟨b,hb,hunram⟩ :=
    Algebra.exists_formallyUnramified_of_isUnramifiedAt (R:=nX k) (⊥ : lz B)
  let:HZ (nX k) (qx b) :=hunram
  have hb₀:b≠0:= fun h=>hb (by simp [h])
  obtain ⟨d,hd,hdiv⟩:=(zh6 (R:=nX k) b).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hb₀)
  refine ⟨d.roots.toFinset,fun t ht => ?_⟩
  let p:=sS (yQ t)
  have hp:p=ov {mD -Polynomial.C t} := Polynomial.ker_evalRingHom t
  let:p.IsMaximal:=VC (yQ t)
    (fun c=>⟨lJ c,zFf⟩)
  have hdp:d∉p:= by
    intro h
    exact ht (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr (RingHom.mem_ker.mp h)))
  have hrad:=fSP b p hdp hdiv
  have hmap :p.map (aU (nX k) B) =
      (ov {P5 a-MvPolynomial.C t}).map (lV I) := by
    have hgen:aU (nX k) B (mD -Polynomial.C t) =
        lV I (P5 a-MvPolynomial.C t) := by
      change (VO I a) (mD -Polynomial.C t)= _
      simp only [VO,uz ,Xx ,SC] <;> rfl
    rw [hp,uJ,uJ,Gj,Gj,hgen]
  rw [hmap] at hrad
  unfold auW
  rw [← Ideal.comap_map_quotientMk I (ov {P5 a-MvPolynomial.C t})]
  exact hrad.comap (lV I)
end bRh
end
section
namespace cyQ
theorem proof :aRW.c2 :=
 aRW.fVh bRg.proof bRh.proof
end cyQ
end
section
namespace agP
noncomputable section
open K1 aR Ex dN wH Rl MvPolynomial UniqueFactorizationMonoid
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem efs :j8.Flat := by
 exact (RingHom.flat_algebraMap_iff.mpr
    (zsF lN (FQ (nX ao)))).comp
  (RingHom.Flat.of_isField (Field.toIsField lN) (aU lN p6))
private theorem cTR (n:ℕ) : (oy (σ:=Fin n) j8).Flat := by
 let:oq (nX ao) GeoField:=j8.toAlgebra
 have hg: (aU (nX ao) p6).Flat :=efs
 exact RingHom.Flat.isStableUnderBaseChange (nX ao) p6 (af n)
  (cy (Fin n) p6) hg
private theorem b4J (n:ℕ) :
  p7 (oy (σ:=Fin n) j8) :=
 zNV _ ((aU lN p6).injective.comp
  (KA (nX ao) lN))
theorem bYh {n:ℕ} {r :cy (Fin n) p6} (hr :Prime r)
    {x :af n} (hx :x≠0) (hxr :r∣oy j8 x) :
    ∃ a :af n,Prime a ∧
      (ov ({r} : Set (cy (Fin n) p6))).comap
        (oy j8)=ov {a} := by
  let P:lz (cy (Fin n) p6) :=ov {r}
  have hP:P.IsPrime :=(Ideal.span_singleton_prime hr.ne_zero).mpr hr
  let Q:=P.comap (oy (σ:=Fin n) j8)
  have hQ:Q.IsPrime :=hP.comap _
  have hQn:Q ≠ ⊥ := fun h=>hx (by
    have hm:x∈Q:=Ideal.mem_span_singleton.mpr hxr
    simpa [h] using hm)
  have hPheight:P.height = 1 :=Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hr.ne_zero) hr.not_isUnit
  let:oq (af n) (cy (Fin n) p6) :=
    (oy (σ:=Fin n) j8).toAlgebra
  let:WX (af n) (cy (Fin n) p6) :=cTR n
  let:P.LiesOver Q:=⟨rfl⟩
  have h:=Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown Q P
  have hQle :Q.height≤1 := by
    rw [← hPheight,h]
    exact le_self_add
  have hQheight:Q.height = 1 := by
    apply wY hQle
    rw [Order.one_le_iff_ne_zero]
    exact fun hzero=>hQn (Ideal.height_eq_zero_iff_eq_bot.mp hzero)
  obtain ⟨a,haQ,ha⟩:=hQ.exists_mem_prime_of_ne_bot hQn
  exact ⟨a,ha,Ideal.eq_span_singleton_of_height_eq_one hQheight haQ ha⟩
private theorem cXz {q:af 3} (hq:q≠0) :He q≠0 :=
 fun hz=>hq (rename_injective _ (Vs 3) (by simpa [He] using hz))
theorem dLv {J:lz (af 4)} {aI:lz t3}
   [aI.IsPrime] {P:af 4}
   (hP:aU t3 (oY aI) (bC P) ∈
     (J.map (oy j8)).map (aU t3 (oY aI))) :
   ∃ s :af 4,bC s∉aI∧s*P∈J:= by
 let g:af 4 →+* GeoJets :=oy j8
 let Q:=aI.comap g
 let:Q.IsPrime :=(xm :aI.IsPrime).comap g
 let A:=oY Q
 let B:=oY aI
 let e :A →+* B:=Localization.localRingHom Q aI g rfl
 let:oq A B:=e.toAlgebra
 let:WX A B:=(cTR 4).localRingHom aI Q rfl
 let:IsLocalHom (aU A B) :=Localization.isLocalHom_localRingHom Q aI g rfl
 let:Module.FaithfullyFlat A B:=Module.FaithfullyFlat.of_flat_of_isLocalHom
 have he (x :af 4) :e (aU (af 4) A x)=aU t3 B (g x) :=
   Localization.localRingHom_to_map Q aI g rfl x
 have hJ: (J.map (aU (af 4) A)).map e=(J.map g).map (aU t3 B) := by
   rw [zR,zR]
   exact ox (fun a=>J.map a) (X8 he)
 have hx :aU (af 4) A P∈J.map (aU (af 4) A) := by
   rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B:=B) (J.map (aU (af 4) A))]
   change e (aU (af 4) A P)∈(J.map (aU (af 4) A)).map e
   rw [he,hJ]
   exact hP
 exact (zi Q.primeCompl A J P).mp hx
theorem ewr {f :af 4} {q:af 3} {aI:lz t3}
  (hf :f≠0) (hproper :IsRelPrime (bC f) (bC (He q)))
  (h:aqk f q aI) :aI.height=2 :=
 agL.aD7 (fun hz=>hf (b4J 4 (by simpa [bC] using hz)))
  hproper h.minimal
end
end agP
end
section
namespace agP
noncomputable section
open K1 aR dN wH Rl MvPolynomial
def c1 :Prop :=
 ∀ q:af 3,Vl q→q.totalDegree<K1.p→Vl (fW q)
private theorem cYA {f :af 4} {q:af 3} {aI:lz t3}
  (hp:aI.IsPrime) (h:bz9 f q aI hp) :
  oA (kC f (He q)) aI hp=1 := by
 let:aI.IsPrime :=hp
 let A:=oY aI
 change (kC f (He q)).map (aU t3 A) =
  qz A at h
 change Au A (A ⧸ (kC f (He q)).map (aU t3 A))=1
 rw [h,Module.length_eq_one_iff]
 exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp xm)
private theorem dgG {f :af 4} {q:af 3} {aI:lz t3}
   (h:aqk f q aI) (hloc:bz9 f q aI h.minimal.isPrime)
   (hqD:bC (acp q)∈aI) :Invariant f aI:= by
 let:aI.IsPrime :=h.minimal.isPrime
 let A:=oY aI
 let g:af 4 →+* GeoJets :=oy j8
 let J:lz (af 4) :=ov {f,He q}
 have hJ:J.map g=kC f (He q) := by
   simp [J,uJ,kC,bC,g]
 have hf :g f∈aI:=h.minimal.le (Dz (by simp [g,bC]))
 have hq:g (He q)∈aI:=h.minimal.le (Dz (by simp [g,bC]))
 have hqFlow:g (u6 f (He q))∈aI:= by
   simp only [u6,gpD,vj,NI]
   change g (oK f*acp q)∈aI
   rw [nq]
   exact aI.mul_mem_left _ hqD
 have hloc' : (J.map g).map (aU t3 A)=qz A :=
   (ox (fun I:lz t3=>I.map (aU t3 A)) hJ).trans hloc
 intro P hP
 change g P∈aI at hP
 change g (u6 f P)∈aI
 have hmem:aU t3 A (g P)∈(J.map g).map (aU t3 A) := by
   rw [hloc',Nq A aI]
   exact hP
 obtain ⟨u,hu,huP⟩:=dLv hmem
 obtain ⟨a,b,hab⟩:=Ideal.mem_span_pair.mp huP
 have hd:g (u6 f (u*P))∈aI:= by
   rw [← hab,cSL,ZF,ZF,cSN,vj,yB]
   simp only [qG,nq]
   exact aI.add_mem (aI.mul_mem_right _ hf) <|
     aI.add_mem (aI.mul_mem_left _ hqFlow) (aI.mul_mem_right _ hq)
 rw [ZF,qG,nq,nq] at hd
 have hterm :g P*g (u6 f u)∈aI:=aI.mul_mem_right _ hP
 have hprod:g u*g (u6 f P)∈aI:=(aI.add_mem_iff_left hterm).mp hd
 exact (h.minimal.isPrime.mem_or_mem hprod).resolve_left hu
end
end agP
end
section
namespace bzH
noncomputable section
open aR dN wH Rl
open scoped Polynomial
private def top {R:Type*} [oD R] :
   cy (Fin 4) R ≃ₐ[R] (cy (Fin 3) R)[X] :=
 (Ml R finSuccEquivLast).trans (MvPolynomial.optionEquivLeft R (Fin 3))
@[simp] private theorem bh2 {R:Type*} [oD R] (a :R) :
   top (pQ a)=lJ (pQ a) := by
  simp [top,MvPolynomial.optionEquivLeft_C]
@[simp] private theorem gRX {R:Type*} [oD R] :
   top (lI (3:Fin 4) :cy (Fin 4) R)=Polynomial.X:= by
  have h:finSuccEquivLast (3:Fin 4)=none :=finSuccEquivLast_last
  simp [top,h,MvPolynomial.optionEquivLeft_X_none]
@[simp] private theorem gCf {R:Type*} [oD R] (i:Fin 3) :
    top (lI i.castSucc:cy (Fin 4) R) =
      lJ (lI i) := by
  simp [top,MvPolynomial.optionEquivLeft_X_some]
private theorem dhD {R:Type*} [oD R] (q:cy (Fin 3) R) :
  top (G6 Gn q)=lJ q:= by
 have h: (top (R:=R)).toRingHom.comp (G6 Gn).toRingHom =
    Polynomial.C:= by
  apply t8
  · intro a
    simp
  · intro i
    simp
 exact zk h q
private theorem dhB {R S:Type*} [oD R] [oD S] (φ:R →+* S)
  (f :cy (Fin 4) R) :
  top (oy φ f)=(top f).map (oy φ) := by
 have h: (top (R:=S)).toRingHom.comp (oy φ) =
    (xL (oy φ)).comp (top (R:=R)).toRingHom:= by
  apply t8
  · intro a
    simp
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
 exact zk h f
private theorem dhz {R:Type*} [oD R] (f :cy (Fin 4) R) :
    top (qy 3 f)=(top f).derivative := by
  have hX (i:Fin 4) :
      top (qy 3 (lI i:cy (Fin 4) R)) =
        (top (lI i:cy (Fin 4) R)).derivative := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · have hne :j.castSucc≠(3:Fin 4) :=zm4 j
      simp only [MvPolynomial.pderiv_X_of_ne hne,qm,gCf,Polynomial.derivative_C]
  refine LP
    (motive := fun p=>top (qy 3 p)=(top p).derivative)
    f ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    simp only [qG,hp,hq]
  · intro p i hp
    simp only [zg ,qG,nq,hp,hX,G1]
end
end bzH
end
section
namespace cyJ
noncomputable section
open aR dN wH MvPolynomial
private theorem SZ:p7 j8 :=
 (aU lN p6).injective.comp
   (KA (nX ao) lN)
private theorem d4z {a :af 3} (ha :a≠0)
   (hvars :a.vars.Nonempty) (hsmall:a.totalDegree<K1.p) :
   ∃ i:Fin 3,¬ a∣qy i a := by
 obtain ⟨i,hi⟩:=hvars
 have hpos :=zOl (mem_vars_iff_degreeOf_ne_zero.mp hi)
 have hlt:=(degreeOf_le_totalDegree a i).trans_lt hsmall
 let _:CharP ao K1.p:=OJ embed.injective K1.p
 let _:CharP (nX ao) K1.p :=
   OJ Polynomial.C_injective K1.p
 have hcast: (a.degreeOf i:nX ao)≠0:= by
   intro hz
   exact (not_le_of_gt hlt)
     (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff (nX ao) K1.p _).mp hz))
 have hnonzero :=pderiv_ne_zero_of_natCast_ne_zero i a hcast
 have hdeg:=degreeOf_pderiv_le_sub_one i a
 refine ⟨i,?_⟩
 rintro ⟨b,hb⟩
 have hb0:b≠0:= fun hz=>hnonzero (by rw [hb,hz,vj])
 rw [hb,degreeOf_mul_eq ha hb0] at hdeg
 omega
theorem proof :agP.c1 := by
 intro q hsq hsmall
 change Vl (oy j8 q)
 have hq:q≠0:=hsq.ne_zero
 have hgq:oy j8 q≠0 :=
   (map_ne_zero_iff _ (zNV _ SZ)).mpr hq
 apply (squarefree_iff_no_irreducibles hgq).mpr
 intro r hir hrr
 have hr :=UniqueFactorizationMonoid.irreducible_iff_prime.mp hir
 have hrq:r∣oy j8 q:=(Qw r r).trans hrr
 obtain ⟨a,ha,hcomap⟩:=agP.bYh hr hq hrq
 have hdvd (x :af 3) :a∣x↔r∣oy j8 x := by
   rw [← QL,← hcomap,Ideal.mem_comap,QL]
 have haq:=(hdvd q).mpr hrq
 have hva :a.vars.Nonempty := by
   by_contra! he
   have heq :=vars_eq_empty_iff_eq_C.mp he
   have hc:a.coeff 0≠0:= fun hz=>ha.ne_zero (by rw [heq,hz,qm])
   have hcnz :j8 (a.coeff 0)≠0:= fun hz =>
     hc (SZ (hz.trans j8.map_zero.symm))
   have hu:wR (oy j8 a) := by
     rw [heq,MvPolynomial.map_C]
     exact (isUnit_iff_ne_zero.mpr hcnz).map C
   exact hr.not_isUnit (zNU ((hdvd a).mp dvd_rfl) hu)
 obtain ⟨i,hi⟩:=d4z ha.ne_zero hva
   ((totalDegree_le_of_dvd_of_isDomain haq hq).trans_lt hsmall)
 have hrderiv :r∣oy j8 (qy i q) := by
   obtain ⟨w,hw⟩:=hrr
   rw [← pderiv_map,hw,pU,zg]
   exact dvd_add (dvd_mul_of_dvd_right (Qw r w) _) (Qw r _)
 have haderiv :=(hdvd (qy i q)).mpr hrderiv
 obtain ⟨b,hb⟩:=haq
 have hab : ¬ a∣b:= by
   rintro ⟨c,hc⟩
   exact ha.not_isUnit (hsq a ⟨c,by rw [hb,hc,pU]⟩)
 rw [hb,zg] at haderiv
 exact hi ((ha.dvd_or_dvd ((dvd_add_left (Qw a _)).mp haderiv)).resolve_right hab)
end
end cyJ
end
section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace aiH
noncomputable section
open K1 wT MvPolynomial
section Field
variable {F:Type*} [c9 F]
private def awH :Fin 4 ≃ Fin 4 :=Equiv.swap 0 1
private def asJ:cy (Fin 4) F ≃ₐ[F]
   nX (cy (Fin 3) F) :=
 (Ml F awH).trans (p5 F 3)
private theorem dml (i:Fin 4) :
   asJ (lI i:cy (Fin 4) F) =
     ![lJ (lI 0),mD,lJ (lI 1),lJ (lI 2)] i:= by
 change p5 F 3 (G6 awH (lI i))= _
 rw [rename_X]
 fin_cases i
 · change (p5 F 3) (lI (0:Fin 3).succ)= _
   exact Gk
 · change (p5 F 3) (lI 0)= _
   exact TI
 · change (p5 F 3) (lI (1 :Fin 3).succ)= _
   exact Gk
 · change (p5 F 3) (lI (2 :Fin 3).succ)= _
   exact Gk
private def abn (s t:F) :Fin 3→nX F :=
 ![mD,lJ s,lJ t]
private def aE5 (G:cy (Fin 4) F) (s t:F) :
   nX (nX F) :=
 (asJ G).map (oZ (abn s t)).toRingHom
private theorem bOd (G:cy (Fin 4) F) (D:nX F) (s t:F) :
   (aE5 G s t).eval D =oZ (D9 D s t) G:= by
 let ev :cy (Fin 3) F →+* nX F:=(oZ (abn s t)).toRingHom
 have h: (yQ D).comp ((xL ev).comp asJ.toRingHom) =
     (oZ (D9 D s t)).toRingHom:= by
   apply t8
   · intro a
     simp [ev,asJ,X4]
   · intro i
     change (aE5 (lI i) s t).eval D = _
     unfold aE5
     rw [dml]
     fin_cases i <;> simp [abn,D9]
 exact Ef h G
private theorem cqk (G:cy (Fin 4) F) (s t:F) :
   aE5 (qy 1 G) s t=pL (aE5 G s t) := by
 let f :cy (Fin 4) F →+* nX (nX F) :=
   (xL (oZ (abn s t)).toRingHom).comp asJ.toRingHom
 change f (qy 1 G)=pL (f G)
 have hC (a :F) :f (C a)=lJ (lJ a) := by
   simp [f,asJ,X4]
 have hX (i:Fin 4) :f (lI i) = ![lJ mD,mD,
     lJ (lJ s),lJ (lJ t)] i:= by
   change (asJ (lI i)).map _ = _
   rw [dml]
   fin_cases i <;> simp [abn]
 induction G using LP with
 | C a=>simp [hC]
 | add a b ha hb=>simp [ha,hb]
 | mul_X a i ha =>
     simp only [zg ,qG,nq,G1 ,ha,hX]
     fin_cases i <;> simp
private theorem cql (G:cy (Fin 4) F) (s t:F) (j:ℕ) :
   aE5 (aNg G j) s t =
    (fun H :nX (nX F)=>pL H)^[j] (aE5 G s t) := by
 induction j with
 | zero=>rfl
 | succ j ih =>
    unfold aNg at *
    simp only [zLk,cqk,ih]
private theorem dmm (G:cy (Fin 4) F) :
  (asJ G).natDegree=G.weightedTotalDegree Qb:= by
 change (p5 F 3 (G6 awH G)).natDegree= _
 rw [natDegree_finSuccEquiv,show (0:Fin 4)=awH 1 by decide,
  degreeOf_rename_of_injective awH.injective,← z5e]
 congr 1
 funext i
 fin_cases i <;> decide
private theorem dM4 (G:cy (Fin 4) F) (i j:ℕ)
   (e :Fin 2 →₀ ℕ) (he :e ∈
     ((p5 F 2 ((asJ G).coeff j)).coeff i).support) :
   ∃ m∈G.support,m 2=e 0∧m 3=e 1 := by
 rw [zjq] at he
 change e.cons i∈((p5 F 3 (G6 awH G)).coeff j).support at he
 rw [zjq] at he
 obtain ⟨m,hm,hcoeff⟩:=coeff_rename_ne_zero awH G ((e.cons i).cons j)
   (mem_support_iff.mp he)
 refine ⟨m,mem_support_iff.mpr hcoeff,?_,?_⟩
 · have h:=ox (fun z :Fin 4 →₀ ℕ=>z (awH 2)) hm
   simp only [zm3 awH.injective] at h
   rw [show awH 2=(0:Fin 2).succ.succ by decide] at h
   simpa only [z9p] using h
 · have h:=ox (fun z :Fin 4 →₀ ℕ=>z (awH 3)) hm
   simp only [zm3 awH.injective] at h
   rw [show awH 3=(1 :Fin 2).succ.succ by decide] at h
   simpa only [z9p] using h
private theorem goC (H :cy (Fin 3) F) (s t:F) :
    oZ (abn s t) H =
      (p5 F 2 H).map (xI ![s,t]) := by
  change (oZ (abn s t)).toRingHom H =
    ((xL (xI ![s,t])).comp (p5 F 2).toRingHom) H
  congr 1
  apply t8
  · intro a
    simp [ X4]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [abn,TI]
    · change oZ (abn s t) (lI j.succ) =
        ((p5 F 2) (lI j.succ)).map _
      rw [Gk]
      fin_cases j <;> simp [abn]
private theorem exceptions (G:cy (Fin 4) F) (hG:G≠0)
   (q a b:ℕ) (hq:0<q) (ha :a<q)
   (hS:G.weightedTotalDegree ME≤a)
   (hT:G.weightedTotalDegree MD ≤b) (Γ:n5 F) :
   ∃ exceptional:n5 F,exceptional.card≤a+q*b ∧
     ∀ γ∈Γ,γ∉exceptional→aE5 G γ (γ^q)≠0:= by
 classical
 obtain ⟨j,hj⟩:=Polynomial.support_nonempty.mpr
   (show asJ G≠0 from fun hz=>hG (asJ.injective (hz.trans (qm asJ).symm)))
 have hn:p5 F 2 ((asJ G).coeff j)≠0:= by
   intro hz
   apply Polynomial.mem_support_iff.mp hj
   exact (p5 F 2).injective
     (hz.trans (qm (p5 F 2)).symm)
 obtain ⟨i,hi⟩:=Polynomial.support_nonempty.mpr hn
 let c:=(p5 F 2 ((asJ G).coeff j)).coeff i
 have hc:c≠0:=Polynomial.mem_support_iff.mp hi
 have hmono (e :Fin 2 →₀ ℕ) (he :e∈c.support) :e 0≤a∧e 1≤b:= by
   obtain ⟨m,hm,h0,h1⟩:=dM4 G i j e he
   have hs :=(Vz (f := fun m=>m.weight ME) hm).trans hS
   have ht:=(Vz (f := fun m=>m.weight MD) hm).trans hT
   simp [ME,MD,zDM,G0 ,
     LR,v8] at hs ht
   omega
 have hca :c.degreeOf 0≤a := by
   rw [IT]
   exact Ok fun e he=>(hmono e he).1
 have hcb:c.degreeOf 1≤b:= by
   rw [IT]
   exact Ok fun e he=>(hmono e he).2
 let E :=Γ.filter fun γ=>xI ![γ,γ^q] c=0
 refine ⟨E,BN.bqt q a b hq c hc hca ha hcb E
   (fun γ hγ=>(Finset.mem_filter.mp hγ).2),?_⟩
 intro γ hγ houtside hz
 apply houtside
 apply Finset.mem_filter.mpr
 refine ⟨hγ,?_⟩
 have he :=ox (fun R:nX (nX F)=>(R.coeff j).coeff i) hz
 simpa [aE5,goC,c] using he
end Field
end
end aiH
end
section
set_option maxHeartbeats 350000
set_option maxSynthPendingDepth 8
namespace aFY
noncomputable section
open K1 cu gT pI
open IsLocalRing
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev aGr :=cy (Fin 2) aZ
private abbrev aki:Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
 finSumFinEquiv.symm.trans (Equiv.sumComm (Fin 2) (Fin 2))
private def aEM:qU ≃+* aGr :=
 ((Ml FX aki).trans
   (ZK FX (Fin 2) (Fin 2))).toRingEquiv
private theorem pO :
    Dk=(aU aGr vR).comp aEM.toRingHom:= by
  have hChart :
      (aU aGr vR).comp aEM.toRingHom =
        Et (MvPolynomial.C.comp (aU FX aQ))
          (G3 lI (fun i=>pQ (ek i)) ∘ aki) := by
    apply t8
    · intro c
      simp [aEM]
      rfl
    · intro i
      rw [EK,Pv,RD]
      change aU aGr vR
        (ZK FX (Fin 2) (Fin 2)
          (Ml FX aki (lI i)))= _
      rw [MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X,MvPolynomial.algebraMap_def]
      cases aki i <;> simp [ek]
  rw [hChart]
  apply t8
  · intro c
    simp only [Dk,UY]
  · intro i
    simp only [Dk,Pv,RD]
    fin_cases i <;> rfl
private theorem emy {F:Type*} [c9 F]
   (J:lz (cy (Fin 2) F)) [J.IsMaximal] :J.height=2 := by
 let e :=(p5 F 1).toRingEquiv
 let P:=J.map e.toRingHom
 let A:=cy (Fin 1) F
 have hP:P.IsMaximal:=zfh e
 let q:=P.comap (lJ:A →+* nX A)
 have hq:q.IsMaximal:=Polynomial.isMaximal_comap_C_of_isJacobsonRing P
 have hdim:q.height = 1 := by
   let e₁:=(MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv
   let q' := q.map e₁.toRingHom
   have hq' : q'.IsMaximal:=zfh e₁
   exact (e₁.height_map q).symm.trans
     (IsPrincipalIdealRing.height_eq_one_of_isMaximal q' (Polynomial.not_isField F))
 have hqP:P.LiesOver q:=⟨rfl⟩
 calc
   J.height=P.height:=(e.height_map J).symm
   _=q.height+1 :=Polynomial.height_eq_height_add_one q P
   _=2 := by rw [hdim,one_add_one_eq_two]
private theorem ex0 {A F:Type*} [oD A] [c9 F]
   [oq A (cy (Fin 2) F)] (S:Submonoid A)
   [G9 S (cy (Fin 2) F)]
   (P:lz A) [P.IsPrime]
   (hproper :P.map (aU A (cy (Fin 2) F)) ≠ ⊤)
   (hfin:oz F
     (cy (Fin 2) F ⧸ P.map (aU A (cy (Fin 2) F)))) :
   P.height=2 := by
 let B:=cy (Fin 2) F
 let Q:=P.map (aU A B)
 have hd:=(IsLocalization.map_algebraMap_ne_top_iff_disjoint S B P).mp hproper
 have hQ:Q.IsPrime :=IsLocalization.isPrime_of_isPrime_disjoint S B P xm hd
 let:c9 (B ⧸ Q) :=fieldOfFiniteDimensional F _
 have :Q.IsMaximal:=Ideal.Quotient.maximal_of_isField Q (Field.toIsField _)
 exact (IsLocalization.height_map_of_disjoint S P hd).symm.trans (emy Q)
theorem drS {I:lz qU} (hI:xN I) :I.height=2 := by
 let S:Submonoid aGr :=(FQ aZ).map pQ
 let P:=I.map aEM.toRingHom
 let J:=I.map Dk
 have hJ:J=P.map (aU aGr vR) := by
  rw [zR,← pO]
 have hP:P.IsPrime := by
  change (I.map (aEM:qU →+* aGr)).IsPrime
  rw [Ideal.map_comap_of_equiv aEM]
  exact hI.prime.comap _
 have hproper :J ≠ ⊤ := by
  intro ht
  let:Subsingleton (vR ⧸ J) :=Ideal.Quotient.subsingleton_iff.mpr ht
  exact hI.seed_size.1.ne' (Module.finrank_eq_zero_of_subsingleton aQ (vR ⧸ J))
 have hfin:oz aQ (vR ⧸ J) :=hI.bg9
 have hproperP:P.map (aU aGr vR) ≠ ⊤ := by
  rw [← hJ]
  exact hproper
 have hfinP:oz aQ (vR ⧸ P.map (aU aGr vR)) := by
  rw [← hJ]
  exact hfin
 have hlocal:G9 S vR :=
  zEY (FQ aZ) aQ
 have hPheight:P.height=2 := by
  exact ex0 (A:=aGr) (F:=aQ) S P hproperP hfinP
 rw [← RingEquiv.height_map aEM I]
 exact hPheight
theorem bID {I:lz qU} [I.IsPrime]
    {J:lz qU} {f :qU} {n:ℕ}
    (h : ∃ a :qU,a∉I∧a*f∈I ^n ⊔ J) :
    aU qU (oY I) f ∈
      (qz (oY I))^n ⊔
        J.map (aU qU (oY I)) := by
  let R:=oY I
  let φ:=aU qU R
  obtain ⟨a,ha,haf⟩:=h
  have hb:=zf φ haf
  rw [II,Iw ,IsLocalization.AtPrime.map_eq_maximalIdeal,nq] at hb
  let B:=(qz R)^n ⊔ J.map φ
  have hu:wR (φ a) :=(IsLocalization.AtPrime.isUnit_to_map_iff R I a).mpr ha
  obtain ⟨u,hu⟩:=hu
  change φ a*φ f∈B at hb
  rw [← hu] at hb
  simpa [← pU] using B.mul_mem_left (↑u⁻¹:R) hb
end
end aFY
end
section
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8
namespace aFY
noncomputable section
open K1 cu gT pI Ty
open IsLocalRing
theorem proof :Ty.c4 := by
 classical
 intro P Q I hI n hn hP hQ
 let:I.IsPrime :=hI.prime
 let R:=oY I
 let:oD R:=inferInstanceAs (oD (oY I))
 let φ:=aU qU R
 have hdim:ringKrullDim R=2 := by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height I R,drS hI]
   rfl
 change (↑(if dual I then n^2 else n:ℕ) :ℕ∞) ≤
   Au R (R ⧸ ((ov {iJ P,iJ Q}).map φ:Kl R R))
 rw [uJ,Set.image_insert_eq,Gj]
 by_cases hD:dual I
 · rw [IU hD]
   rw [O9,IU hD] at hP hQ
   have hp:=bID hP
   have hq:=bID hQ
   have hbase :IsRegularRing FX:=xm
   have hambient:IsRegularRing Ambient:=MvPolynomial.isRegularRing_of_isRegularRing FX
   have hregular :IsRegularLocalRing R :=
     IsRegularRing.isRegularLocalRing_localization (R:=qU) I
   have hfactor :zsh Ambient :=
     MvPolynomial.uniqueFactorizationMonoid (Fin 4)
   have hlocalFactor :zsh R :=
     UniqueFactorizationMonoid.of_isLocalization I.primeCompl R
   have hdomain:zE R:=inferInstanceAs (zE (oY I))
   exact guq (qz R) (ce2 (R:=R) hdim)
     hn (by simpa only [Ideal.map_bot,Oc] using hp)
     (by simpa only [Ideal.map_bot,Oc] using hq)
 · rw [Eg hD]
   rw [O9,Eg hD] at hP hQ
   obtain ⟨G,_,hG⟩:=akR.cV2 hI hD
   have hGI:C7 G∈I:= by
     change G∈I.comap C7
     rw [hG]
     exact z5J G
   have hX:φ (C7 G)∈qz R :=
     (Nq R I _).mpr hGI
   have hM:1<(qz R).height:= by
     have h:=maximalIdeal_height_eq_ringKrullDim (R:=R)
     rw [hdim] at h
     have he : (qz R).height=2 :=WithBot.coe_injective h
     rw [he]
     decide
   have hp:=bID hP
   have hq:=bID hQ
   simp only [hG,uJ,Gj] at hp hq
   exact ew9 hX hM hp hq
end
end aFY
end
section
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Qo
noncomputable section
open MvPolynomial
variable {F E :Type*} [c9 F] [c9 E] [oq F E]
private theorem affine_image (Q:cy (Fin 5) F)
    (j:Fin 5) (hj:j=3∨j=4) (x :E) (v :Fin 5→nX E)
    (hv :v 0=lJ x) (hl:Q.degreeOf j≤1)
    (hzero : ∀ i:Fin 5,i≠0→i≠j→Q.degreeOf i=0) :
    ∃ a b:E,oZ v Q=lJ a+Polynomial.C b*v j:= by
  classical
  let c (e :Fin 5 →₀ ℕ) :=aU F E (Q.coeff e)*x^e 0
  let a (e :Fin 5 →₀ ℕ) :=if e j=0 then c e else 0
  let b (e :Fin 5 →₀ ℕ) :=if e j=0 then 0 else c e
  refine ⟨∑ e∈Q.support,a e,∑ e∈Q.support,b e,?_⟩
  conv_lhs=>rw [Q.as_sum]
  rw [sI,sI,sI,JW,← vG]
  apply vw rfl
  intro e he
  have hdz (i:Fin 5) (hi:i≠0) (hij:i≠j) :e i=0 :=
    Ob ((le_degreeOf_of_mem_support i he).trans (hzero i hi hij).le)
  have hmono :
      oZ v (Kz e (Q.coeff e))=lJ (c e)*v j^e j:= by
    rw [aeval_monomial]
    rcases hj with rfl | rfl
    · simp [z6B,zNH,hv,c,
        hdz 1 (by decide) (by decide),hdz 2 (by decide) (by decide),
        hdz 4 (by decide) (by decide),WY ,pU]
    · simp [z6B,zNH,hv,c,
        hdz 1 (by decide) (by decide),hdz 2 (by decide) (by decide),
        hdz 3 (by decide) (by decide),WY ,pU]
  rw [hmono]
  have he' := (le_degreeOf_of_mem_support j he).trans hl
  by_cases h:e j=0
  · simp [a,b,h]
  · have he1 :e j=1 := by omega
    simp [a,b,he1]
private def transpose (f :nX F →+* E) :
   nX (nX F) →+* nX E :=
 (xL f).comp (Dv (R:=F)).toRingHom
private theorem gD1 (f :nX F →ₐ[F] E) (q:ℕ)
    (Q:cy (Fin 5) F) :
    transpose f.toRingHom (graph q Q) =
      oZ ![lJ (f mD),0,0,
        mD,(mD (R:=E))^q] Q:= by
  have h: (transpose f.toRingHom).comp (graph (F:=F) q).toRingHom =
      (oZ ![lJ (f mD),0,0,
        mD,(mD (R:=E))^q]).toRingHom:= by
    apply t8
    · intro r
      simp [transpose,graph,WY ,Polynomial.Bivariate.swap_C_C]
      exact f.commutes r
    · intro i
      fin_cases i <;> simp [transpose,graph,zPy,
        Polynomial.Bivariate.swap_Y]
  exact Ef h Q
private def columns (z U V:nX E) :Fin 4→nX E :=
 ![U,mD *U,V,z*V]
private theorem dWi (z U V g:nX E)
  (a b c d:E) (hU:U≠0) (hg:g≠0)
  (hA:g*U=lJ a+Polynomial.C b*z)
  (hB:g*V=lJ c+Polynomial.C d*mD) :
  ¬ z7 E (columns z U V) := by
 intro hi
 have hrel : (lJ c+Polynomial.C d*mD)*U =
    (lJ a+Polynomial.C b*z)*V:= by
  rw [← hB,← hA]
  ring
 have hcomb : ∑ i:Fin 4,(![c,d,-a,-b] :Fin 4→E) i•columns z U V i=0:= by
  simp only [LR,Fin.sum_univ_zero,columns,
    zbs,Matrix.cons_val_succ,zS ,Polynomial.smul_eq_C_mul,map_neg]
  linear_combination hrel
 have hz :=Fintype.linearIndependent_iff.mp hi _ hcomb
 have ha :a=0:= by simpa using hz 2
 have hb:b=0:= by simpa using hz 3
 exact mul_ne_zero hg hU (by simpa [ha,hb] using hA)
private theorem c1v (q:ℕ) (f :nX F →ₐ[F] E)
   (hf :p7 f) (g:nX F)
   (U V:cy (Fin 5) F) (U' V' : nX (nX F))
   (hg:g≠0) (hu:U' ≠ 0) (hU:yV U) (hV:yV V)
   (hGU:graph q U=lJ g*U') (hGV:graph q V=lJ g*V')
   (hr :pG E (Submodule.span E (vk
     (columns (mD ^q) (transpose f.toRingHom U') (transpose f.toRingHom V'))))=4)
   (hs :YF U V=1) (ht:aab U V=1) :False := by
 let ψ:=transpose f.toRingHom
 let v :Fin 5→nX E :=
   ![lJ (f mD),0,0,mD,mD ^q]
 have htrans (Q:cy (Fin 5) F) :ψ (graph q Q)=oZ v Q :=
   gD1 f q Q
 have hU3:U.degreeOf 3=0:= by unfold YF at hs; omega
 have hV4 :V.degreeOf 4=0:= by unfold aab at ht; omega
 obtain ⟨hU1,hU2⟩:=hU
 obtain ⟨hV1,hV2⟩:=hV
 have haxisU : ∀ i:Fin 5,i≠0→i≠4→U.degreeOf i=0:= by
   intro i hi hj
   fin_cases i <;> simp_all
 have haxisV : ∀ i:Fin 5,i≠0→i≠3→V.degreeOf i=0:= by
   intro i hi hj
   fin_cases i <;> simp_all
 have hU4 :U.degreeOf 4≤1 := by
   unfold aab at ht
   omega
 have hV3:V.degreeOf 3≤1 := by
   unfold YF at hs
   omega
 obtain ⟨a,b,hab⟩:=affine_image U 4 (Or.inr rfl) _ v rfl hU4 haxisU
 obtain ⟨c,d,hcd⟩:=affine_image V 3 (Or.inl rfl) _ v rfl hV3 haxisV
 have hv4 :v 4=(mD (R:=E))^q:=rfl
 have hv3:v 3=(mD (R:=E)) :=rfl
 rw [← htrans,hGU,nq,hv4] at hab
 rw [← htrans,hGV,nq,hv3] at hcd
 have hψ:p7 ψ :=
   (NW f.toRingHom hf).comp (Dv (R:=F)).injective
 have hu' : ψ U' ≠ 0:= by
   intro h
   exact hu (hψ (h.trans (qm ψ).symm))
 have hg' : ψ (lJ g)≠0:= by
   intro h
   exact hg (Polynomial.C_eq_zero.mp (hψ (h.trans (qm ψ).symm)))
 have hi:z7 E (columns (mD ^q) (ψ U') (ψ V')) :=
   linearIndependent_iff_card_eq_finrank_span.mpr
     (by simpa only [Set.finrank,Pf] using hr.symm)
 exact dWi (mD ^q) (ψ U') (ψ V') (ψ (lJ g))
   a b c d hu' hg' hab hcd hi
open K1 wT
private theorem c1l (q:ℕ) (U V:nC) :
    Aj.ajp q U V =
      pG kB (Submodule.span kB (vk (columns (mD ^q)
        (sZ (Dv U)) (sZ (Dv V))))) := by
  have hcols : (fun j:Fin 4=>sZ (Dv
      (if j=0 then U else if j=1 then seed*U else if j=2 then V
        else seed^q*V)))=columns (mD ^q)
          (sZ (Dv U)) (sZ (Dv V)) := by
    funext j
    fin_cases j <;> simp [columns,sZ,seed,zPy]
  unfold Aj.ajp
  rw [hcols]
end
end Qo
end
section
namespace bRy
noncomputable section
open MJ E7
open scoped Polynomial RatFunc
attribute [local instance] Polynomial.algebra
private def scale {L:Type} [c9 L] (b:L) (hb:b≠0) :
  L[X] ≃ₐ[L] L[X] :=
 Polynomial.algEquivOfCompEqX (lJ b⁻¹*mD)
  (lJ b*mD)
  (by simp [← MS ,← pU,hb])
  (by simp [← MS ,← pU,hb])
private theorem bnK {k L σ:Type} [c9 k] [c9 L] [oq k L]
   (w:σ→L) (b:L) (hb:b≠0) :
   wL k (fun i=>w i/b)=(scale b hb).toRingHom.comp (wL k w) := by
 apply t8
 · intro c
   simp [wL,scale,zrE]
 · intro i
   simp only [EK,wL,Pv]
   change lJ (w i/b)*mD =
     Ea (lJ b⁻¹*mD) (lJ (w i)*mD)
   rw [nq,SC,zrE,Xx ,← pU,
     ← MS ,PD]
private theorem c6O {k L σ:Type} [c9 k] [c9 L] [oq k L]
  (w:σ→L) (i:σ) (b:L) (hb:b≠0) :
  YC k (fun l=>w l/b) i=YC k w i:= by
 have h:F8 (fun l=>w l/b) i=F8 w i:= by
  funext l
  exact div_div_div_cancel_right₀ hb (w l) (w i)
 simp only [YC,h]
private def Fh {k L σ:Type} [c9 k] [c9 L] [oq k L] (w:σ→L) :
   cy σ k →+* pC L :=
 (aU L[X] (pC L)).comp (wL k w)
private theorem a2S {k L σ:Type} [c9 k] [c9 L] [oq k L]
  (w:σ→L) (c:k) :
  Fh w (pQ c)=t4 (aU k L c) := by
 simp [Fh,wL]
private theorem aHd {k L σ:Type} [c9 k] [c9 L] [oq k L]
  (w:σ→L) (i:σ) :
  Fh (k :=k) w (lI i)=t4 (w i)*RatFunc.X:= by
 simp [Fh,wL]
private theorem bYx {k L σ:Type} [c9 k] [c9 L] [oq k L]
  (w:σ→L) (b:L) (hb:b≠0) :
  sS (Fh (k :=k) (fun i=>w i/b))=SQ k w:= by
 rw [Fh,zGm _ (RatFunc.algebraMap_injective L),
  bnK w b hb]
 exact zGm (wL k w)
  (f :=(scale b hb).toRingHom) (scale b hb).injective
private def ace {A K:Type} [oD A] [c9 K]
  (P:lz A) [P.IsPrime] (e :A →+* K) (h:sS e=P) :
  qJ (A ⧸ P) →+* K :=
 zIj (RingHom.lift_injective_of_ker_le_ideal P
  (fun _ ha=>RingHom.mem_ker.mp (h.symm ▸ ha)) h.le)
private theorem ay4 {A K:Type} [oD A] [c9 K]
   (P:lz A) [P.IsPrime] (e :A →+* K) (h:sS e=P) (a :A) :
   ace P e h
     (aU (A ⧸ P) (qJ (A ⧸ P)) (lV P a))=e a := by
 rw [ace,zoc,Ideal.Quotient.lift_mk]
private theorem b3S {A K:Type} [oD A] [c9 K]
  (P:lz A) [P.IsPrime] (e :A →+* K) (h:sS e=P)
  (S:Subfield K) (he : ∀ a,e a∈S) :
  (ace P e h).fieldRange≤S:= by
 rintro _ ⟨z,rfl⟩
 obtain ⟨x,y,_,rfl⟩:=IsFractionRing.div_surjective (A ⧸ P) z
 obtain ⟨a,rfl⟩:=uh x
 obtain ⟨b,rfl⟩:=uh y
 rw [map_div₀,ay4,ay4]
 exact S.div_mem (he a) (he b)
private theorem cHZ {k L σ A:Type} [c9 k] [c9 L] [oq k L]
   [c9 A] (w:σ→L) (i:σ) (f :A →+* pC L)
   (he : ∀ p:cy σ k,Fh w p∈f.fieldRange)
   {a :L} (ha :a∈YC k w i) :
   t4 a∈f.fieldRange := by
 let S:IntermediateField k L :=
   (f.fieldRange.comap t4).toIntermediateField (fun c=> by
     change t4 (aU k L c)∈f.fieldRange
     simpa only [a2S] using he (pQ c))
 have hle :YC k w i≤S:= by
   apply IntermediateField.adjoin_le_iff.mpr
   rintro _ ⟨j,rfl⟩
   change t4 (F8 w i j)∈f.fieldRange
   have hx (l:σ) :t4 (w l)*Gi∈f.fieldRange := by
     simpa only [aHd] using he (lI l)
   have hd:=f.fieldRange.div_mem (hx j) (hx i)
   rwa [mul_div_mul_right _ _ RatFunc.X_ne_zero,← map_div₀] at hd
 exact hle ha
private theorem bgs {F K:Type} [c9 F] [c9 K]
    (g:pC F →+* K) (S:Subfield K)
    (hC : ∀ a,g (t4 a)∈S) (hX:g Gi∈S) (z :pC F) :g z∈S:= by
  have hp (p:F[X]) :g (aU F[X] (pC F) p)∈S:= by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [qG,qG]
        exact S.add_mem hp hq
    | monomial n a =>
        rw [RatFunc.algebraMap_monomial,nq,xW]
        exact S.mul_mem (hC a) (S.pow_mem hX n)
  induction z using RatFunc.induction_on with
  | f p q hq =>
      rw [map_div₀]
      exact S.div_mem (hp p) (hp q)
private theorem aWK {F L:Type} [c9 F] [c9 L] [oq F L]
   (p:F[X]) :
   aU (pC F) (pC L) (aU F[X] (pC F) p) =
     aU L[X] (pC L) (p.map (aU F L)) := by
 rw [← Ee F[X] (pC F) (pC L),
   Ee F[X] L[X] (pC L)]
 rfl
private theorem a7t {F L:Type} [c9 F] [c9 L] [oq F L] (c:F) :
  aU (pC F) (pC L) (t4 c)=t4 (aU F L c) := by
 simpa only [RatFunc.algebraMap_C,PA] using
  aWK (L:=L) (lJ c)
private theorem buI {F L:Type} [c9 F] [c9 L] [oq F L] :
  aU (pC F) (pC L) Gi=RatFunc.X:= by
 simpa only [RatFunc.algebraMap_X,Polynomial.map_X] using
  aWK (L:=L) (mD:F[X])
set_option maxHeartbeats 1000000 in
theorem proof :E7.c4 := by
  classical
  intro k L σ τ _ _ _ u i v j φ hi hj hgen hcomp
  let P:=SQ k u
  let Q:=P.comap φ
  let _:P.IsPrime :=Pc (wL k u)
  let _:Q.IsPrime :=Ideal.IsPrime.comap φ
  let U:σ→L:= fun l=>u l/v j
  let V:τ→L:= fun l=>v l/v j
  let E :=YC k v j
  have hnorm: (Fh (k :=k) U).comp φ=Fh (k :=k) V:= by
    change ((aU L[X] (pC L)).comp (wL k U)).comp φ =
      (aU L[X] (pC L)).comp (wL k V)
    rw [show wL k U= _ from bnK u (v j) hj,
      show wL k V= _ from bnK v (v j) hj,
      XG,XG,hcomp]
  have hP:sS (Fh (k :=k) U)=P:=bYx u (v j) hj
  have hQ:sS (Fh (k :=k) V)= Q:= by
    rw [← hnorm,← zEW,hP]
  let KU:=qJ (cy σ k ⧸ P)
  let KV:=qJ (cy τ k ⧸ Q)
  let fU:KU →+* pC L:=ace P (Fh U) hP
  let fV:KV →+* pC L:=ace Q (Fh V) hQ
  have hU (p:cy σ k) :Fh U p∈fU.fieldRange :=
    ⟨_,ay4 P (Fh U) hP p⟩
  have hV (p:cy τ k) :Fh V p∈fV.fieldRange :=
    ⟨_,ay4 Q (Fh V) hQ p⟩
  let f :KV →+* KU :=
    IsFractionRing.map (zmq (I:=P) (f :=φ))
  let _:oq KV KU:=f.toAlgebra
  have hsquare :fU.comp f=fV:= by
    apply IsFractionRing.ringHom_ext (A:=cy τ k ⧸ Q)
    intro a
    obtain ⟨p,rfl⟩:=uh a
    have hf :f (aU (cy τ k ⧸ Q) KV (lV Q p)) =
        aU (cy σ k ⧸ P) KU (lV P (φ p)) := by
      change IsLocalization.map _ (Ideal.quotientMap P φ vZ) _ _ = _
      rw [IsLocalization.map_eq]
      rfl
    rw [EK,hf]
    exact (ay4 P (Fh U) hP (φ p)).trans
      ((Ef hnorm p).trans (ay4 Q (Fh V) hQ p).symm)
  have hX:Gi∈fV.fieldRange := by
    simpa only [aHd,V,div_self hj,map_one,yU] using hV (lI j)
  have hXU:Gi∈fU.fieldRange := by
    obtain ⟨x,hx⟩:=hX
    exact ⟨f x,(Ef hsquare x).trans hx⟩
  have hConstU (a :L) :t4 a∈fU.fieldRange :=
    cHZ U i fU hU (by
      rw [show YC k U i=YC k u i from c6O u i (v j) hj,hgen]
      exact IntermediateField.mem_top)
  have hsurjU:u5 fU:= fun z =>
    bgs (RingHom.id (pC L)) fU.fieldRange hConstU hXU z
  let g:=aU (pC E) (pC L)
  have hg:g.fieldRange=fV.fieldRange := by
    apply wY
    · rintro _ ⟨z,rfl⟩
      refine bgs g fV.fieldRange (fun c => ?_) ?_ z
      · rw [show g (t4 c)=t4 (c:L) from a7t c]
        exact cHZ V j fV hV (by
          rw [show YC k V j=E from c6O v j (v j) hj]
          exact c.property)
      · exact buI (F:=E) (L:=L) ▸ hX
    · apply b3S
      intro p
      induction p using LP with
      | C c =>
          rw [a2S]
          exact ⟨t4 (aU k E c),a7t _⟩
      | add p q hp hq =>
          rw [qG]
          exact g.fieldRange.add_mem hp hq
      | mul_X p l hp =>
          rw [nq,aHd]
          refine g.fieldRange.mul_mem hp (g.fieldRange.mul_mem ?_ ⟨Gi ,buI⟩)
          have hl:V l∈E :=IntermediateField.subset_adjoin _ _ ⟨l,rfl⟩
          exact ⟨t4 ⟨V l,hl⟩,a7t _⟩
  let eU:=RingEquiv.ofBijective fU ⟨fU.injective,hsurjU⟩
  let eV:=fV.rangeRestrictFieldEquiv.trans
    ((RingEquiv.subfieldCongr hg.symm).trans g.rangeRestrictFieldEquiv.symm)
  have hcomm:g.comp eV.toRingHom=eU.toRingHom.comp f := by
    ext1 x
    change g ((g.rangeRestrictFieldEquiv).symm _)=fU (f x)
    rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    exact (Ef hsquare x).symm
  unfold QZ
  rw [dite_eq_left (show P.IsPrime from xm)]
  change pG KV KU=pG E L
  calc
    _=pG (pC E) (pC L) :=Algebra.finrank_eq_of_equiv_equiv eV eU hcomm
    _=pG E[X] L[X] :=IsFractionRing.finrank_eq E[X] (pC E) L[X] (pC L)
    _=pG E L:=ox Cardinal.toNat (rank_polynomial_polynomial E L)
end
end bRy
end
