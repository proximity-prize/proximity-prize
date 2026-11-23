import ProximityPrize.SubmissionLower.I
import ProximityPrize.SubmissionLower.Z
import ProximityPrize.SubmissionLower.J
import ProximityPrize.SubmissionLower.K
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
open _root_ renaming AddCommGroup→SD,AffineIndependent→zP0,AlgEquiv.apply_symm_apply→zIH,AlgEquiv.symm_apply_apply→TH,Algebra→nI,Algebra.EssFiniteType→zl5,Algebra.FiniteType→WW,Algebra.FormallyEtale→Yc,Algebra.FormallyUnramified→Ww,Algebra.IsAlgebraic→X8,Algebra.IsIntegral→zVK,Algebra.IsIntegral.of_finite→zux,Algebra.IsSeparable→ZK,Algebra.TensorProduct.includeRight→Kl,Algebra.TensorProduct.tensorQuotientEquiv→zTd,Algebra.algebraMap→aU,Algebra.linearMap→zdh,Algebra.trdeg→sS,AlgebraicIndependent→GY,Bool.false→t5,Cardinal→xm,Cardinal.mk_fintype→Du,CharP.cast_eq_zero_iff→Xo,CharP.char_is_prime_of_two_le→zVj,CommRing→ ox,DFunLike.congr_fun→Kv,Derivation→KH,Derivation.leibniz→Ea,Differential→zyu,Differential.coeff_mapCoeffs→zyh,Differential.deriv→LR,Differential.deriv_aeval_eq→zkK,Differential.mapCoeffs→u8,Dr.ChamberBox→Nq,Dr.capExponents→vw,E7.CurveField→Mw,E7.CurvePlace→pG,E7.poleOrder→pL,Equiv.trans_apply→Vq,FaithfulSMul→Kz,Field→nX,Fin.last→Sd,Fin.sum_univ_eq_sum_range→zdx,Fin.sum_univ_four→zmL,Finite→vl,FiniteDimensional→NW,Finset→nq,Finset.card_image_of_injOn→zaG
open _root_ renaming Finset.filter_subset→WD,Finset.induction_on→zcw,Finset.le_sup→Xx,Finset.mem_univ→FR,Finset.mul_sum→zxw,Finset.smul_sum→PM,Finset.sum_add_distrib→PA,Finset.sum_apply→Ze,Finset.sum_congr→sI,Finset.sum_eq_single→Qw,Finset.sum_ite_eq'→X4,Finset.sum_le_sum→Wm,Finset.sum_le_sum_of_subset_of_nonneg→zlp,Finset.sum_lt_sum→zfK,Finset.sum_mul→Ye,Finset.sum_sub_distrib→zQq,Finset.sup_le→Pv,Finset.sup_le_iff→zUp,Finsupp.optionElim_apply_none→z6S,Finsupp.optionElim_some→zX5,Finsupp.single→GB,Finsupp.some_optionElim→zpo,Finsupp.sum_fintype→z9d,Finsupp.weight_optionElim→WX,Fintype→t7,Fintype.card→Gr,Fintype.card_prod→Pr,FractionRing→t4,Function.Injective→th,Function.Surjective→vZ,Function.comp_apply→z3s,Function.iterate_succ_apply'→zLk,Function.support→N0,Function.update→zc,Function.update_of_ne→UP,Function.update_self→RD,Ideal→lI,Ideal.Quotient.eq_zero_iff_mem→SC,Ideal.Quotient.factorₐ→SU,Ideal.Quotient.field→zxv,Ideal.Quotient.liftₐ→zTA,Ideal.Quotient.mk→lV,Ideal.Quotient.mk_surjective→zh,Ideal.Quotient.mkₐ→Zi,Ideal.comap_map_of_bijective→UZ,Ideal.exists_minimalPrimes_le→zXL,Ideal.map_map→x7,Ideal.map_span→Qx
open _root_ renaming Ideal.map_sup→Oc,Ideal.mem_comap→Ts,Ideal.mem_span_singleton_self→Mj,Ideal.mem_sup_left→zKg,Ideal.mem_sup_right→G2,Ideal.quotientEquivAlg→zpY,Ideal.span→ oz,Ideal.span_singleton_le_iff_mem→RJ,Ideal.subset_span→G9,IntermediateField.adjoin→Ef,IsAlgebraic→Z0,IsCompact→PD,IsDomain→uW,IsFractionRing→vj,IsFractionRing.injective→zm,IsFractionRing.lift→zIj,IsFractionRing.lift_algebraMap→zoc,IsLeftRegular→Xg,IsLocalRing.residue→zeo,IsLocalization→C4,IsLocalization.Away.algebraMap_isUnit→z4z,IsLocalization.Away.lift→ztx,IsLocalization.Away.lift_comp→zOe,IsLocalization.algEquiv→z0R,IsLocalization.exists_mk'_eq→zcf,IsLocalization.isPrime_of_isPrime_disjoint→znL,IsLocalization.map_units→Sv,IsLocalization.mk'→zzm,IsLocalization.mk'_mem_map_algebraMap_iff→zNj,IsLocalization.ringHom_ext→zuW,IsLocalization.under_map_of_isPrime_disjoint→ztT,IsLocalizedModule→XB,IsLocalizedModule.surj→zMS,IsScalarTower→sH,IsScalarTower.algebraMap_apply→t8,IsScalarTower.algebraMap_eq→Ok,IsScalarTower.of_algebraMap_eq→RC,IsScalarTower.toAlgHom→Hw,KaehlerDifferential.D→Aa,LinearIndependent→z14,LinearMap.ker→wA,LinearMap.mem_ker→XJ,LinearMap.mulLeft→zzN,LinearMap.smul_apply→zqa,Localization.AtPrime→zf,Localization.Away→xL,MeasureTheory.MeasureSpace.volume→qM,Module.Basis→y5
open _root_ renaming Module.Finite→qx,Module.Finite.of_basis→zwB,Module.Finite.of_surjective→Np,Module.Flat.ker_lTensor_eq→zai,Module.finrank→pQ,Module.length→Fz,MulZeroClass.mul_zero→G0,MulZeroClass.zero_mul→vh,MvPolynomial→cy,MvPolynomial.C→ oq,MvPolynomial.IsHomogeneous.sum→ II,MvPolynomial.IsPrime.vanishingIdeal_zeroLocus→ Iw,MvPolynomial.X→lz,MvPolynomial.aeval→p7,MvPolynomial.aeval_C→Gi,MvPolynomial.aeval_X→wR,MvPolynomial.aeval_eq_eval→uz,MvPolynomial.affineDegree→p9,MvPolynomial.affineDegree_nonneg→Pc,MvPolynomial.affineHilbertFunction→G4,MvPolynomial.affineHilbertPolynomial→n5,MvPolynomial.affineHilbertPolynomial_eq_C_finrank→Zg,MvPolynomial.algHom_ext→zpI,MvPolynomial.algebraMap_apply→zdz,MvPolynomial.algebraMap_def→Zh,MvPolynomial.algebraMap_eq→zKm,MvPolynomial.algebraTensorAlgEquiv→zoR,MvPolynomial.coeff_mul_X'→z0S,MvPolynomial.coeff_sum→zqN,MvPolynomial.commAlgEquiv→z7,MvPolynomial.commAlgEquiv_C→Qy,MvPolynomial.eq_affineHilbertPolynomial_of_eval_eq→zpB,MvPolynomial.eval→vi,MvPolynomial.eval_C→yl,MvPolynomial.eval_X→wY,MvPolynomial.eval_map→znM,MvPolynomial.eval₂Hom→C5,MvPolynomial.eval₂Hom_C→yL,MvPolynomial.eval₂Hom_X'→G1,MvPolynomial.exists_eval_affineHilbertPolynomial→NY,MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus→G5,MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree→z1b,MvPolynomial.homogeneousComponent→Av,MvPolynomial.homogeneousComponent_isHomogeneous→z8k,MvPolynomial.homogeneousComponent_mem_of_mem→zfj,MvPolynomial.homogeneousComponent_of_mem→UY,MvPolynomial.homogeneousSubmodule→Dz,MvPolynomial.induction_on→EK
open _root_ renaming MvPolynomial.isHomogeneous_monomial→MS,MvPolynomial.ker_map→zRA,MvPolynomial.le_totalDegree→Kc,MvPolynomial.map→mD,MvPolynomial.map_C→zi,MvPolynomial.map_X→zS,MvPolynomial.map_eval→zsn,MvPolynomial.map_map→Ml,MvPolynomial.mem_support_iff→zuk,MvPolynomial.mem_vanishingIdeal_singleton_iff→zIF,MvPolynomial.mk_mem_quotientDegreeLE→GR,MvPolynomial.moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero→zhp,MvPolynomial.monomial→xu,MvPolynomial.monomialMap→Gn,MvPolynomial.natDegree_affineHilbertPolynomial_comap_of_surjective→z1R,MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective→zwG,MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le→Lf,MvPolynomial.optionEquivLeft→p5,MvPolynomial.optionEquivLeft_X_none→WY,MvPolynomial.optionEquivLeft_X_some→zQa,MvPolynomial.optionEquivLeft_coeff_coeff→z9x,MvPolynomial.optionEquivRight→RP,MvPolynomial.pderiv→Dw,MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one→Pf,MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime→MK,MvPolynomial.quotientDegreeLE→p6,MvPolynomial.quotientDegreeLE_mono→zhv,MvPolynomial.rename→t3,MvPolynomial.renameEquiv→Vl,MvPolynomial.restrictSupport→Dv,MvPolynomial.ringHom_ext→yQ,MvPolynomial.totalDegree_finsetSum_le→WK,MvPolynomial.trdeg_of_isDomain→zUx,MvPolynomial.vanishingIdeal→Bf,MvPolynomial.zeroLocus→ oj,MvPolynomial.zeroLocusPointHom→QL,Nat.card_fin→VC,Nat.cast_add→Mk,Nat.cast_mul→SL,Nat.cast_nonneg→Rm,Nat.cast_one→G7,Nat.factorial_succ→zwO,Nat.le_add_right→S2,Nat.le_sub_one_of_lt→zxM,Nat.lt_succ_of_le→TZ,Nat.pos_of_ne_zero→zOl,Nat.strong_induction_on→z0n,Nat.sub_add_cancel→G6
open _root_ renaming Option→ oD,Pi.single→xW,Pi.smul_apply→MO,Polynomial→ IT,Polynomial.C→ oY,Polynomial.X→qJ,Polynomial.aeval→z8,Polynomial.aeval_C→z8q,Polynomial.aeval_X→ZJ,Polynomial.algebraMap_eq→zrE,Polynomial.backwardDifference→FV,Polynomial.coe_aeval_eq_eval→z99,Polynomial.coeff_derivative→VO,Polynomial.coeff_map→Eg,Polynomial.coeff_zero→z9,Polynomial.derivative→G3,Polynomial.eval_backwardDifference→zjN,Polynomial.eval_map→zhI,Polynomial.eval_monomial→zsC,Polynomial.factorial_smul_hasseDeriv→z6T,Polynomial.finsetSum_coeff→OJ,Polynomial.hasseDeriv→qm,Polynomial.hasseDeriv_map→Zt,Polynomial.leadingCoeff→SM,Polynomial.mapRingHom→P7,Polynomial.map_C→Zf,Polynomial.monomial→Kh,Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero→Te,Polynomial.natDegree_sum_le_of_forall_le→zMZ,Polynomial.natDegree_taylor→NX,Polynomial.ringHom_ext→z86,Polynomial.taylor→u9,Polynomial.taylor_coeff→Ob,RatFunc→t9,RatFunc.algebraMap_X→zYR,RingEquiv.subringCongr→zh4,RingHom.comp_apply→JM,RingHom.congr_fun→vk,RingHom.ext→u5,RingHom.formallyUnramified_algebraMap→zDh,RingHom.id→LO,RingHom.ker→vG,RingHom.ker_isPrime→zgL,Set.Icc→Gk,Set.InjOn→KI,Set.image_singleton→R9,Set.mem_fintype_sum→z2V,Set.ncard_coe_finset→zik
open _root_ renaming Set.ncard_le_ncard→zDB,Set.range→ oK,Submodule→Re,Submodule.equivMapOfInjective→zW6,Submodule.map_span→Xu,Submodule.mem_colon_singleton→Au,Submodule.span→yB,Submodule.span_le→VH,Submodule.subset_span→Un,Submodule.sum_mem→Y4,Submonoid→Pk,Submonoid.powers→JQ,Subtype.ext→zg,Subtype.val→zza,Sum.elim→Nj,TensorProduct.AlgebraTensorModule.lTensor→ In,TensorProduct.AlgebraTensorModule.lTensor_tmul→zbj,TensorProduct.inductionOn→z2P,TensorProduct.isScalarTower_left→XG,Transcendental→Yo,TrivSqZeroExt.ext→ IU,XX.placeWeight→ze,YW.dimension→ oy,YW.project→yo,aR.Shape→uJ,aR.Shape.plus→NZ,aR.Shape.scale→Fa,aR.extend→Ar,aZc.coordinate→Kp,aaq.Degree→Cy,add_comm→FU,add_neg_cancel→LQ,add_zero→zE,aeF.toFunction→yJ,algebraMap_smul→TI,congrArg→ ov,convexHull→v8,dN.GeoField→c9,dN.GeoJets→ oZ,dvd_mul_of_dvd_right→zfC,eq_neg_of_add_eq_zero_left→zZQ,eq_or_ne→G8,exists_finite_inj_algHom_of_fg→z4J,faithfulSMul_iff_algebraMap_injective→JW,finSuccEquivLast→wB,finSuccEquivLast_castSucc→VS,finSuccEquivLast_last→S1,finrank_top→Yi
open _root_ renaming finsum_mem_inter_support_eq'→zJX,inferInstance→F9,injective_iff_map_eq_zero→zLn,inv_mul_cancel₀→NI,ite_eq_left→zYo,ite_eq_right→Nr,lB.TaylorChart→t6,le_antisymm→zd,le_of_tendsto_of_tendsto→zyf,le_rfl→zk,le_sup_left→Df,left_ne_zero_of_mul→SW,lt_of_le_of_ne→Xp,map_add→qz,map_mul→lJ,map_natCast→ Il,map_neg→KA,map_ofNat→Pj,map_pow→qU,map_smul→FK,map_sub→yU,map_sum→pC,map_zero→qy,mul_assoc→v9,mul_comm→pz,mul_div_cancel_right₀→z5O,mul_le_mul_of_nonneg_left→Wl,mul_le_mul_of_nonneg_right→Mz,mul_lt_mul_of_pos_left→zu3,mul_nonneg→LP,mul_one→Ee,nhdsWithin_le_nhds→zBa,nonZeroDivisors→vH,nonZeroDivisors.ne_zero→zyw,not_le_of_gt→GF,nsmul_eq_mul→J4,oR.separant→pU,one_mul→uh,one_ne_zero→JK,pow_add→Et,rW.dimension→xI,right_ne_zero_of_mul→Vz,smul_eq_mul→qG,smul_eq_zero_iff_right→zBU,smul_zero→zR,sub_eq_add_neg→Vs,sub_eq_zero→HZ,sub_zero→FQ
open _root_ renaming sup_le→Gj,trdeg_add_eq→EP,trdeg_eq_zero→Up,zero_add→C9
set_option autoImplicit true
section
namespace YW
noncomputable section
open aR dN lB MvPolynomial
open scoped BigOperators
theorem bKR (C:t6) (y :KE)
  (hy :eval y C.denom≠0) :yo (BQ C y)=y := by
 funext i
 change eval y (C.numerator (au8 i))/eval y C.denom=y i
 rw [show C.numerator (au8 i)=lz i*C.denom from C.initial i,
  lJ,wY ,z5O _ hy]
private theorem bpG (z :alk) (q:oZ) :
  eval z (t3 au8 q)=eval (yo z) q :=
 eval_rename au8 z q
theorem bpB (C:t6) (z :alk) :
  eval z (bew C)=eval (yo z) C.denom :=
 bpG z C.denom
theorem bWZ {C:t6} {P:lI oZ} {y :KE}
  (hy :y∈oj c9 P) (hD:eval y C.denom≠0) :
  BQ C y∈oj c9 (ajF C P) :=
 zeroLocus_vanishingIdeal_le _ ⟨y,⟨hy,hD⟩,rfl⟩
theorem ePe {C:t6} {P:lI oZ} {z :alk}
  (hz :z∈oj c9 (ajF C P)) :yo z∈oj c9 P:= by
 intro q hq
 have hmem:t3 au8 q∈ajF C P:= by
  rintro _ ⟨y,⟨hy,hD⟩,rfl⟩
  simpa only [uz ,bpG,bKR C y hD] using hy q hq
 simpa only [uz ,bpG] using hz _ hmem
theorem dIb {C:t6} {P:lI oZ} {z :alk}
   (hz :z∈oj c9 (ajF C P)) (hD:eval z (bew C)≠0) :
   BQ C (yo z)=z := by
 funext i
 let q:=t3 au8 (C.numerator i)-MvPolynomial.X i*bew C
 have hmem:q∈ajF C P:= by
   rintro _ ⟨y,⟨_,hy⟩,rfl⟩
   simp only [q,uz ,yU,lJ,bpG,wY ,
     bpB,bKR C y hy,HZ,BQ]
   exact (div_mul_cancel₀ _ hy).symm
 apply (div_eq_iff (by rwa [← bpB])).mpr
 simpa only [q,uz ,yU,lJ,bpG,wY ,
   bpB,HZ] using hz _ hmem
theorem enD {C:t6} {P:lI oZ}
  (hp:P.IsPrime) (hP:C.denom∉P) :bew C∉ajF C P:= by
 let _:=hp
 intro hm
 apply hP
 rw [← Iw (K:=c9) P]
 intro y hy
 by_contra hD
 have hz :=bWZ (C:=C) hy (by simpa only [uz] using hD)
 apply hD
 simpa only [uz ,bpB,bKR C y
  (by simpa only [uz] using hD)] using hz _ hm
theorem b1X (a :agy) (z :alk) :
  eval z (adD a)=a.1 + ∑ i,a.2 i*z i:= by
 simp [adD]
theorem bFu (C:t6) (a :agy) (y :KE)
  (hy :eval y C.denom≠0) :
  eval y (C.pullback a)=eval y C.denom*eval (BQ C y) (adD a) := by
 rw [b1X]
 simp only [TaylorChart.pullback,qz ,lJ,yl,pC,mul_add,zxw]
 rw [pz a.1]
 apply ov (fun t:c9=>eval y C.denom*a.1+t)
 apply sI rfl
 intro i _
 rw [BQ,← v9,pz (eval y C.denom),v9,
  mul_div_cancel₀ _ hy]
theorem epg {I:lI oZ} {D:oZ} {S:nq KE}
    (hS : ∀ x∈oj c9 I,eval x D ≠0→x∈S)
    {y :KE} (hy :y∈oj c9 I) (hD:eval y D ≠0) :
    vG (eval y)∈I.minimalPrimes := by
  classical
  obtain ⟨P,hP,hyP⟩:=G5 I D y hy hD
  obtain ⟨hmin,hDP⟩:=Ideal.mem_retainedMinimalPrimes.mp hP
  have hle :S.inf (fun x=>Bf c9 {x})≤P:= by
    intro q hq
    have hm:D *q∈P:= by
      let _:=hmin.isPrime
      rw [← Iw (K:=c9) P]
      intro x hx
      by_cases hDx :eval x D =0
      · simp [uz ,hDx]
      · have hxs :=hS x (zeroLocus_anti_mono hmin.le hx) hDx
        have hqx :=(Finset.inf_le (f := fun x=>Bf c9 {x}) hxs) hq
        rw [zIF,uz] at hqx
        simp [uz ,hqx]
    exact (hmin.isPrime.mem_or_mem hm).resolve_left hDP
  obtain ⟨x,_,hx⟩:=hmin.isPrime.inf_le'.mp hle
  have hmax : (Bf c9 {x}).IsMaximal:=F9
  have heq :=hmax.eq_of_le hmin.isPrime.ne_top hx
  have hPy :P≤Bf c9 {y} := fun p hp =>
    (zIF y p).mpr (hyP p hp)
  have hPy_eq :=hmax.eq_of_le (Ideal.IsMaximal.ne_top F9) (heq ▸ hPy)
  have hy_eq :Bf c9 {y} = P:=hPy_eq.symm.trans heq
  have hk :vG (eval y)=Bf c9 {y} := by
    ext p
    simp [uz]
  rw [hk,hy_eq]
  exact hmin
end
end YW
end
section
namespace YW
noncomputable section
open K1 aR dN lB MvPolynomial
open scoped Polynomial BigOperators
def cAE (s :K→K[X]) (γ:K) :KE :=
 fun i=>j8 (jet (Ar (s γ)) i)
def rV (s :K→K[X]) (γ:K) :alk :=
 fun i=>j8 (qm i.val (Ar (s γ)))
theorem dIa {C:t6} {s :K→K[X]} {γ:K}
  (h:C.aay (Ar (s γ))) :BQ C (cAE s γ)=rV s γ:= by
 funext i
 change An (Ar (s γ)) (C.numerator i)/An (Ar (s γ)) C.denom =
  rV s γ i
 rw [h.2 i,pz ,z5O _ h.1]
 rfl
private theorem ezv {Γ:nq K} {s :K→K[X]}
  (h:KI s (Γ:Set K)) :KI (rV s) (Γ:Set K) := by
 intro a ha b hb heq
 have h₀:=congrFun heq (0:AK)
 have he :Ar (s a)=Ar (s b) :=SZ
  (by simpa only [rV,Fin.val_zero,Polynomial.hasseDeriv_zero'] using h₀)
 exact h ha hb (Polynomial.map_injective embed embed.injective he)
private def constants :ao →+* GeoField:=j8.comp oY
private def center :GeoField:=j8 qJ
private def L4 (x a :K) :agy :=
 (-constants (embed a),fun i=>(constants (embed x) - center)^i.val)
private theorem auQ (p:ao[X]) : (p.map constants).eval center=j8 p:= by
 rw [zhI]
 simpa only [constants,center,Polynomial.eval₂_C_X] using
  (Polynomial.hom_eval₂ p oY j8 qJ).symm
private theorem E4 {s :K→K[X]} {γ x a :K}
  (hd: (s γ).natDegree<bf) :
  p7 (rV s γ) (adD (L4 x a))=0↔(s γ).eval x=a := by
 let p:=(Ar (s γ)).map constants
 have hdeg: (u9 center p).natDegree<bf := by
  rw [NX]
  exact Polynomial.natDegree_map_le.trans_lt (Polynomial.natDegree_map_le.trans_lt hd)
 have hsum:=Polynomial.eval_eq_sum_range' hdeg (constants (embed x) - center)
 rw [← zdx,Polynomial.taylor_eval_sub] at hsum
 simp_rw [p,Ob ,Zt,auQ,
  Polynomial.eval_map_apply] at hsum
 rw [uz ,b1X]
 change -constants (embed a)+(∑ i:AK,
  (constants (embed x) - center)^i.val*rV s γ i)=0↔_
 simp_rw [pz (_^_),rV,Zt]
 rw [← hsum,FU,← Vs ,HZ,constants.injective.eq_iff,
  embed.injective.eq_iff]
private theorem cSQ (a :agy) : (adD a).totalDegree≤1 := by
 apply (totalDegree_add _ _).trans
 simp only [totalDegree_C,Nat.zero_le,Nat.max_eq_right]
 exact WK (fun i _ =>
  (totalDegree_mul _ _).trans (by rw [totalDegree_C,totalDegree_X,C9]))
private def ng (A:Al) :ℕ := ⌊p9 A⌋₊
private theorem bZ8 {A:Al} (hp:A.IsPrime)
    {z :alk} (hz :z∈oj c9 A) :1≤p9 A:= by
  classical
  generalize hd:oy A=n
  induction n using z0n generalizing A with
  | h n ih =>
    by_cases hn:n=0
    · obtain ⟨hf,hdeg⟩:=z1b
        (K:=c9) A (hd.trans hn)
      have hcard:1≤(oj c9 A).ncard:= by
        simpa using zDB (Set.singleton_subset_iff.mpr hz) hf
      exact (by exact_mod_cast hcard: (1 :ℚ)≤_).trans hdeg
    have hcut : ∃ i,lz i-MvPolynomial.C (z i)∉A:= by
      by_contra! hall
      let φ:=lV A
      have hm:φ=φ.comp (MvPolynomial.C.comp (eval z)) := by
        apply yQ
        · intro c
          simp [φ]
        · intro i
          simp only [JM,wY]
          exact sub_eq_zero.mp (by
            rw [← yU]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i))
      have hsurj:vZ (aU c9 (PK ⧸ A)) := by
        intro q
        obtain ⟨g,rfl⟩:=zh q
        exact ⟨eval z g,(vk hm g).symm⟩
      let _:qx c9 (PK ⧸ A) :=
        Np (zdh c9 (PK ⧸ A)) hsurj
      exact hn (hd.symm.trans (by simp [oy ,Zg]))
    obtain ⟨i,hi⟩:=hcut
    let cut:PK:=lz i-MvPolynomial.C (z i)
    have hdeg:cut.totalDegree≤1 :=(totalDegree_sub _ _).trans (by simp)
    have hzero :z∈oj c9 (A ⊔ oz {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz,by simp [cut]⟩
    obtain ⟨B,hB,hzB⟩:=G5
      _ (1 :PK) _ hzero (by simp)
    let _:=hp
    have hm:=(Ideal.mem_retainedMinimalPrimes.mp hB).1
    have hdim:=Pf hi hm
    change oy B+1=oy A at hdim
    have hBdeg:=ih (oy B) (by omega) hm.isPrime hzB rfl
    have hsum:=principalCut_sum_affineDegree_retainedMinimalPrimes_le (1 :PK) hi hdeg
    have hle :=Finset.single_le_sum (f :=p9) (fun B _=>Pc B) hB
    simpa only [G7,uh] using hBdeg.trans (hle.trans hsum)
private def JI (Γ:nq K) (s :K→K[X]) (A:Al) :nq K:= by
 classical
 exact Γ.filter fun γ=>rV s γ∈oj c9 A
private theorem P6 {Γ:nq K} {s :K→K[X]} {A:Al} {γ:K} :
  γ∈JI Γ s A↔γ∈Γ∧rV s γ∈oj c9 A:= by
 classical
 simp [JI]
private def aa9 (Γ:nq K) (s :K→K[X]) (T:nq Al) :DA Γ :=
 ⟨T.card,fun i=>JI Γ s (T.equivFin.symm i),
   fun _ _ h=>(P6.mp h).1,fun i=>ng (T.equivFin.symm i)⟩
private theorem cIy {Γ:nq K} {s :K→K[X]} {T:nq Al}
  {γ:K} (hγ:γ∈Γ) {A:Al} (hA:A∈T)
  (hmark :rV s γ∈oj c9 A) :γ∈(aa9 Γ s T).union := by
 classical
 refine Finset.mem_biUnion.mpr ⟨T.equivFin ⟨A,hA⟩,FR _,?_⟩
 simpa [aa9] using (P6.mpr ⟨hγ,hmark⟩:γ∈JI Γ s A)
private theorem c35 (Γ:nq K) (s :K→K[X]) (T:nq Al) :
   ((aa9 Γ s T).total:ℚ) ≤ ∑ A∈T,affineDegree A:= by
 have htotal: (aa9 Γ s T).total = ∑ A∈T,ng A:= by
   change ∑ i:Fin T.card,ng (T.equivFin.symm i)= _
   calc
     _ = ∑ A:T,ng A:=Fintype.sum_equiv T.equivFin.symm _ _ (fun _=>rfl)
     _ = _:=Finset.sum_attach T ng
 rw [htotal,Nat.cast_sum]
 exact Wm fun A _=>Nat.floor_le (Pc A)
private theorem cBa {Γ:nq K} {s :K→K[X]} {A:Al}
  (hp:A.IsPrime) (h: (JI Γ s A).Nonempty) :0<ng A:= by
 obtain ⟨γ,hγ⟩:=h
 exact Nat.floor_pos.mpr (bZ8 hp (P6.mp hγ).2)
private theorem cI9 {Γ:nq K} {s :K→K[X]} {A:Al} {x a :K}
  (hd : ∀ γ∈Γ,(s γ).natDegree<bf)
  (hz : ∀ γ∈Γ,rV s γ∈oj c9 A)
  (hmiss : ∃ γ∈Γ,(s γ).eval x≠a) :adD (L4 x a)∉A:= by
 obtain ⟨γ,hγ,hmiss⟩:=hmiss
 exact fun hm=>hmiss ((E4 (hd γ hγ)).mp (hz γ hγ _ hm))
private theorem dR3 {Γ:nq K} {s :K→K[X]} {A:Al}
  (hp:A.IsPrime) (hdim:oy A=1)
  (hd : ∀ γ∈Γ,(s γ).natDegree<bf)
  (hi:KI (rV s) (Γ:Set K))
  (hz : ∀ γ∈Γ,rV s γ∈oj c9 A) :
  agC Γ s (ng A) := by
 classical
 intro x a hmiss
 let cut:=adD (L4 x a)
 let J:=A ⊔ oz {cut}
 let H :=Γ.filter fun γ=>(s γ).eval x=a
 have hc:=MK
  hp (cI9 hd hz hmiss) (cSQ (L4 x a))
 have hdimJ:oy J=0:= by
  have h:=hc.1
  change oy J≤oy A - 1 at h
  omega
 have hdeg:p9 J≤p9 A:= by
  simpa [p9,hdim,hdimJ,J,cut,SM] using hc.2
 obtain ⟨hfinite,hcard⟩:=z1b (K:=c9) J hdimJ
 have hsub: (H.image (rV s) :Set _)⊆oj c9 J:= by
  intro z hzp
  obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hzp
  obtain ⟨hΓ,hv⟩:=Finset.mem_filter.mp hγ
  exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz γ hΓ,(E4 (hd γ hΓ)).mpr hv⟩
 have hcount:=zDB hsub hfinite
 rw [zik,zaG
  (hi.mono (WD _ _))] at hcount
 exact Nat.le_floor ((Nat.cast_le.mpr hcount).trans (hcard.trans hdeg))
private theorem bOG {Γ:nq K} {s :K→K[X]} {A:Al}
   (hp:A.IsPrime) (hdim:oy A=2)
   (hd : ∀ γ∈Γ,(s γ).natDegree<bf)
   (hi:KI (rV s) (Γ:Set K))
   (hz : ∀ γ∈Γ,rV s γ∈oj c9 A) :
   aB7 Γ s (ng A) := by
 classical
 let _:=hp
 intro x a hmiss H
 let J:=A ⊔ oz {adD (L4 x a)}
 let T:=J.minimalPrimesFinset.filter (fun B=>(JI H s B).Nonempty)
 have hproper :=cI9 hd hz hmiss
 have hmin (B:Al) (hB:B∈T) :J.IsMinimalPrime B :=
   Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hB).1
 refine ⟨aa9 H s T,?_,?_,?_,?_⟩
 · intro γ hγ
   obtain ⟨hΓ,hv⟩:=Finset.mem_filter.mp hγ
   have hzero :rV s γ∈oj c9 J :=
     mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz γ hΓ,(E4 (hd γ hΓ)).mpr hv⟩
   obtain ⟨B,hB,hzB⟩:=G5
     J (1 :PK) _ hzero (by simp)
   exact cIy hγ (Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr
     (Ideal.mem_retainedMinimalPrimes.mp hB).1,⟨γ,P6.mpr ⟨hγ,hzB⟩⟩⟩) hzB
 · intro i
   let B:=T.equivFin.symm i
   have hm:=hmin B B.property
   have hdimB:=Pf hproper hm
   change oy (B:Al)+1=oy A at hdimB
   apply dR3 hm.isPrime (by omega :dimension (B:Al)=1)
   · exact fun γ hγ=>hd γ (Finset.mem_filter.mp (P6.mp hγ).1).1
   · exact hi.mono (fun _ hγ=>(Finset.mem_filter.mp (P6.mp hγ).1).1)
   · exact fun _ hγ=>(P6.mp hγ).2
 · intro i
   let B:=T.equivFin.symm i
   exact cBa (hmin B B.property).isPrime (Finset.mem_filter.mp B.property).2
 · apply Nat.le_floor
   have hsum:=principalCut_sum_affineDegree_minimalPrimes_le hproper (cSQ (L4 x a))
   exact (c35 H s T).trans ((zlp
     (WD _ _) (fun B _ _=>Pc B)).trans
     (by simpa only [G7,uh] using hsum))
theorem eLj {Γ:nq K} {s :K→K[X]} (T:nq Al) {d:ℕ}
    (hT : ∀ A∈T,A.IsPrime∧oy A=2)
    (hd : ∀ γ∈Γ,(s γ).natDegree<bf) (hi:KI s (Γ:Set K))
    (hz : ∀ γ∈Γ,∃ A∈T,rV s γ∈oj c9 A)
    (hbudget : ∑ A∈T,p9 A≤d) :
    ∃ B:DA Γ,Γ⊆B.union∧B.uG s∧(∀ i,0<B.degree i)∧B.total≤d:= by
  classical
  let U:=T.filter (fun A=>(JI Γ s A).Nonempty)
  refine ⟨aa9 Γ s U,?_,?_,?_,?_⟩
  · intro γ hγ
    obtain ⟨A,hA,hmark⟩:=hz γ hγ
    exact cIy hγ (Finset.mem_filter.mpr ⟨hA,⟨γ,P6.mpr ⟨hγ,hmark⟩⟩⟩) hmark
  · intro i
    let A:=U.equivFin.symm i
    obtain ⟨hp,hdim⟩:=hT A (Finset.mem_filter.mp A.property).1
    have hsub:JI Γ s A⊆Γ:= fun _ h=>(P6.mp h).1
    exact bOG hp hdim (fun γ hγ=>hd γ (hsub hγ))
      ((ezv hi).mono hsub) (fun _ hγ=>(P6.mp hγ).2)
  · intro i
    let A:=U.equivFin.symm i
    obtain ⟨hA,hmark⟩:=Finset.mem_filter.mp A.property
    exact cBa (hT A hA).1 hmark
  · exact Nat.cast_le.mp ((c35 Γ s U).trans
      ((zlp (WD _ _)
        (fun A _ _=>Pc A)).trans hbudget))
end
end YW
end
section
namespace YW
noncomputable section
open K1 aR dN lB MvPolynomial
open scoped BigOperators
def c1 :Prop :=
  ∀ f g:oZ,f≠0→ g≠0→ IsRelPrime f g → ∀ C:t6,
    ∀ P∈Z1 f g C,(ajF C P).IsPrime∧oy (ajF C P)=2
def c2 :Prop :=
  ∀ (T:nq Al) (D:PK),
    (∀ A∈T,A.IsPrime∧oy A=2∧D∉A) →
    ∃ (a b:agy) (sectionPoints :nq alk),
      (∀ z,z∈sectionPoints↔(∃ A∈T,z∈oj c9 A) ∧
        eval z (adD a)=0∧eval z (adD b)=0) ∧
      (∀ z∈sectionPoints,eval z D ≠0) ∧
      (∑ A∈T,p9 A)≤(sectionPoints.card:ℚ)
private theorem mem_pair {y :KE} {f g:oZ} :
  y∈oj c9 (Ib f g)↔eval y f=0∧eval y g=0:= by
 rw [Ib,zeroLocus_span]
 simp [uz]
private theorem avy {y :KE} {f g u v :oZ} :
   y∈oj c9 (oz ({f,g,u,v} : Set oZ)) ↔
     (eval y f=0∧eval y g=0)∧eval y u=0∧eval y v=0:= by
 rw [zeroLocus_span]
 simp [uz ,and_assoc]
theorem of_children (h1 :c1) (h2 :c2) :lB.c2 := by
  classical
  intro f g hf hg hfg C d hbound Γ s hinj hmarks
  let T:=(Z1 f g C).image (ajF C)
  have hT : ∀ A∈T,A.IsPrime∧oy A=2∧bew C∉A:= by
    intro A hA
    obtain ⟨P,hP,rfl⟩:=Finset.mem_image.mp hA
    obtain ⟨hmin,hden⟩:=Ideal.mem_retainedMinimalPrimes.mp hP
    obtain ⟨hp,hd⟩:=h1 f g hf hg hfg C P hP
    exact ⟨hp,hd,enD hmin.isPrime hden⟩
  obtain ⟨a,b,sectionPoints,hZ,hDZ,hsum⟩:=h2 T (bew C) hT
  let S:=sectionPoints.image yo
  let I:=oz ({f,g,C.pullback a,C.pullback b} : Set oZ)
  have hfinite : ∀ y∈oj c9 I,eval y C.denom≠0→y∈S:= by
    intro y hy hDy
    obtain ⟨hpair,ha,hb⟩:=avy.mp hy
    obtain ⟨P,hP,hyP⟩:=G5
      (Ib f g) C.denom y (mem_pair.mpr hpair) hDy
    rw [bFu C a y hDy] at ha
    rw [bFu C b y hDy] at hb
    have hz :BQ C y∈sectionPoints :=(hZ _).mpr
      ⟨⟨ajF C P,Finset.mem_image.mpr ⟨P,hP,rfl⟩,bWZ hyP hDy⟩,
        (mul_eq_zero.mp ha).resolve_left hDy,(mul_eq_zero.mp hb).resolve_left hDy⟩
    exact Finset.mem_image.mpr ⟨_,hz,bKR C y hDy⟩
  have hchart : ∀ z∈sectionPoints,BQ C (yo z)=z := by
    intro z hz
    obtain ⟨A,hA,hzA⟩:=((hZ z).mp hz).1
    obtain ⟨P,_,rfl⟩:=Finset.mem_image.mp hA
    exact dIb hzA (hDZ z hz)
  have hcard:S.card=sectionPoints.card:= by
    apply zaG
    intro z hz w hw hwz
    rw [← hchart z hz,← hchart w hw,hwz]
  have hSbound:=hbound a b S (fun y hy=> by
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy
    have hD:eval (yo z) C.denom≠0:= by
      rw [← bpB]
      exact hDZ z hz
    obtain ⟨⟨A,hA,hzA⟩,ha,hb⟩:=(hZ z).mp hz
    obtain ⟨P,hP,rfl⟩:=Finset.mem_image.mp hA
    have hpy :=ePe hzA
    have hpair :=mem_pair.mp (zeroLocus_anti_mono (Ideal.mem_retainedMinimalPrimes.mp hP).1.le hpy)
    have hu:eval (yo z) (C.pullback a)=0:= by
      rw [bFu C a _ hD,hchart z hz,ha,G0]
    have hv :eval (yo z) (C.pullback b)=0:= by
      rw [bFu C b _ hD,hchart z hz,hb,G0]
    exact ⟨epg hfinite (avy.mpr ⟨hpair,hu,hv⟩) hD,hD⟩)
  have hbudget : ∑ A∈T,p9 A≤(d:ℚ) := by
    exact hsum.trans (Nat.cast_le.mpr (hcard ▸ hSbound))
  apply eLj T (fun A hA=>⟨(hT A hA).1,(hT A hA).2.1⟩) _ hinj _ hbudget
  · exact fun γ hγ=>TZ (hmarks γ hγ).1
  · intro γ hγ
    obtain ⟨_,hF,hG,hC⟩:=hmarks γ hγ
    obtain ⟨P,hP,hpt⟩:=G5
      (Ib f g) C.denom (cAE s γ) (mem_pair.mpr ⟨hF,hG⟩) hC.1
    refine ⟨ajF C P,Finset.mem_image.mpr ⟨P,hP,rfl⟩,?_⟩
    rw [← dIa hC]
    exact bWZ hpt hC.1
end
end YW
end
section
namespace akP
noncomputable section
open dN lB YW MvPolynomial
open scoped BigOperators
abbrev bbq:=Bool×oD AK
abbrev aha :=bbq→c9
abbrev Zm:=cy bbq c9
def aEL (p:aha) (j:Bool) :agy :=
 (p (j,none),fun i=>p (j,some i))
def ke (A:Al) (p:aha) :Al :=
  (A ⊔ oz {adD (aEL p t5)}) ⊔
    oz {adD (aEL p true)}
def aew (condition :aha→Prop) :Prop :=
 ∃ f :Zm,f≠0 ∧ ∀ p,eval p f≠0→ condition p
theorem aIB {A:Al} {p:aha} {z :alk} :
  z∈oj c9 (ke A p)↔z∈oj c9 A ∧
    eval z (adD (aEL p t5))=0 ∧
    eval z (adD (aEL p true))=0:= by
 simp only [ke,mem_zeroLocus_sup_span_singleton_iff,uz ,and_assoc]
theorem aew.and {f g:aha→Prop}
  (hf :aew f) (hg:aew g) :
  aew (fun p=>f p∧g p) := by
 obtain ⟨F,hF,hf⟩:=hf
 obtain ⟨G,hG,hg⟩:=hg
 refine ⟨F*G,mul_ne_zero hF hG,fun p hp => ?_⟩
 rw [lJ] at hp
 exact ⟨hf p (SW hp),hg p (Vz hp)⟩
theorem aew.b3e {ι:Type*} (s :nq ι)
   (condition :ι→aha→Prop)
   (h : ∀ i∈s,aew (condition i)) :
   aew (fun p => ∀ i∈s,condition i p) := by
 classical
 induction s using zcw with
 | empty =>
   exact ⟨1,JK,by simp⟩
 | insert i s hi ih =>
   simpa only [Finset.forall_mem_insert] using
     (h i (Finset.mem_insert_self i s)).and (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
theorem aew.d4x {condition :aha→Prop}
  (h:aew condition) : ∃ p,condition p:= by
 obtain ⟨f,hf,hc⟩:=h
 by_contra! hn
 apply hf
 apply MvPolynomial.funext
 intro p
 rw [qy]
 exact not_not.mp (mt (hc p) (hn p))
end
end akP
end
section
namespace aFV
noncomputable section
open dN lB YW akP MvPolynomial
abbrev dV:=t4 Zm
abbrev adl:=cy AK Zm
abbrev aRA:=cy AK dV
def ahd {k :Type} [ox k] (t:oD AK→k) :
    MvPolynomial AK k :=
  oq (t none) + ∑ i:AK,oq (t (some i))*lz i
def byh (j:Bool) :adl :=
 ahd (fun i=>lz (j,i))
def bHk (j:Bool) (i:oD AK) :dV :=
 aU Zm dV (lz (j,i))
def aU7 (j:Bool) :aRA :=
 ahd (bHk j)
def Cl (A:Al) :lI aRA :=
 A.map (mD (aU c9 dV))
def a4u (A:Al) :lI aRA :=
 Cl A ⊔ oz {aU7 t5}
def aFo (A:Al) :lI adl :=
  (A.map (mD (C:c9 →+* Zm)) ⊔
    oz {byh t5}) ⊔ oz {byh true}
def aN0 (J:lI adl) :lI aRA :=
 J.map (mD (aU Zm dV))
def aXS (J:lI adl) (p:aha) :Al :=
 J.map (mD (eval p))
def atV {k σ:Type} [nX k] (I:lI (cy σ k))
    (f :cy σ k) :Prop :=
  Xg (lV I f) ∧
    ∃ N :ℕ,∀ n≥N,∀ x∈p6 I (n+1),
      lV I f*x∈p6 I (n+1) →
      x∈p6 I n
end
end aFV
end
section
set_option backward.isDefEq.respectTransparency false
namespace akP
noncomputable section
open dN lB YW MvPolynomial Algebra
open scoped BigOperators
private theorem ct5 {k S R:Type} [nX k]
  [ox S] [uW S] [ox R] [uW R] [nI k S] [nI k R]
  (g:S →ₐ[k] R) (hg:th g) (hfin:g.Finite) :
  sS k R=sS k S:= by
 let algebra :=g.toRingHom.toAlgebra
 let:=algebra
 let:sH k S R := .of_algebraMap_eq' g.comp_algebraMap.symm
 let:Kz S R:=(JW S R).mpr hg
 let:qx S R:=hfin
 let:zVK S R:=zux S R
 rw [← EP k S (A:=R),Up (R:=S) (A:=R),zE]
private theorem gEf {k σ:Type} [nX k] [vl σ]
   {P:lI (cy σ k)} [P.IsPrime] :
   sS k (cy σ k ⧸ P)=((n5 P).natDegree :xm) := by
 obtain ⟨d,g,hg,hfin⟩:=z4J k (cy σ k ⧸ P)
 have hd: (n5 P).natDegree=d:= by
   simpa only [VC] using
     zwG g hfin hg
 rw [hd,ct5 g hg hfin]
 simp [Du]
private theorem gD5 {k R ι:Type} [nX k] [ox R] [uW R]
  [nI k R] :
  sS k (cy ι R)=sS k R+Cardinal.mk ι:= by
 let:Kz R (cy ι R) :=
  (JW _ _).mpr (C_injective ι R)
 rw [← EP k R (A:=cy ι R),zUx,
  Cardinal.lift_id]
private abbrev baO:=Bool×AK
private abbrev abD (P:Al) :=
 cy baO (PK ⧸ P)
private def aH9 (P:Al) :bbq→abD P
 | (j,some i)=>MvPolynomial.X (j,i)
 | (j,none) => -∑ i,MvPolynomial.X (j,i)*MvPolynomial.C (Ideal.Quotient.mk P (MvPolynomial.X i))
private theorem eJV {k σ:Type} [nX k] [t7 σ]
   {P:lI (cy σ k)} [P.IsPrime]
   (hd: (n5 P).natDegree≤1)
   (φ:cy (Bool×oD σ) k →ₐ[k]
     cy (Bool×σ) (cy σ k ⧸ P)) :
   ¬ th φ:= by
 intro hinj
 have hle :sS k (cy (Bool×oD σ) k) ≤
     sS k (cy (Bool×σ) (cy σ k ⧸ P)) :=
   trdeg_le_of_injective (R:=k) (A:=cy (Bool×oD σ) k)
     (A' := cy (Bool×σ) (cy σ k ⧸ P)) φ hinj
 let n:=Gr σ
 let d:=(n5 P).natDegree
 have hs :sS k (cy (Bool×oD σ) k)=((2*(n+1) :ℕ) :xm) := by
   simp [Du,n,Pr]
 have ht:sS k (cy (Bool×σ) (cy σ k ⧸ P)) =
     ((d+2*n:ℕ) :xm) := by
   rw [gD5,gEf]
   simp [Du,n,d,Pr,Mk,SL]
 have hcast: ((2*(n+1) :ℕ) :xm)≤((d+2*n:ℕ) :xm) := by
   simpa only [hs,ht] using hle
 exact (by omega : ¬ 2*(n+1)≤d+2*n) (by exact_mod_cast hcast)
private theorem d2t {P:Al} {p:aha}
    {z :alk} (hz :z∈oj c9 P)
    (hc : ∀ j,eval z (adD (aEL p j))=0) (f :Zm) :
    C5 (QL P ⟨z,hz⟩).toRingHom (fun i:baO=>p (i.1,some i.2))
      (p7 (R:=c9) (aH9 P) f)=eval p f := by
  let e :=C5 (QL P ⟨z,hz⟩).toRingHom
    (fun i:baO=>p (i.1,some i.2))
  have hcoord (i:AK) :
      QL P ⟨z,hz⟩ (lV P (lz i))=z i:= by
    change p7 z (lz i)=z i
    exact wR _ _
  have hcomp:e.comp (p7 (R:=c9) (aH9 P)).toRingHom=eval p:= by
    apply yQ
    · intro a
      change e (p7 (R:=c9) (aH9 P) (oq a)) =
        eval p (oq a)
      rw [Gi ,zdz,yl]
      exact (yL _ _ _).trans ((QL P ⟨z,hz⟩).commutes a)
    · rintro ⟨j,i⟩
      change e (p7 (R:=c9) (aH9 P) (lz (j,i))) =
        eval p (lz (j,i))
      rw [wR,wY]
      cases i with
      | none =>
        have hj:=hc j
        rw [b1X] at hj
        change p (j,none)+(∑ i,p (j,some i)*z i)=0 at hj
        have he : -(∑ i,p (j,some i)*z i)=p (j,none) :=
          (zZQ hj).symm
        rw [aH9,KA,pC,← he]
        refine ov (fun x :c9 => -x) (sI rfl ?_)
        intro i _
        rw [lJ]
        simp only [e,G1 ,yL,AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom,hcoord]
      | some i=>exact eval₂Hom_X' _ _ _
  exact vk hcomp f
private theorem dwN {P:Al} (hP:P.IsPrime) (hd:oy P≤1) :
  aew (fun p=>oj c9 (ke P p) = ∅) := by
 let:=hP
 let φ:Zm →ₐ[c9] abD P:=p7 (aH9 P)
 have hf : ¬ th φ:=eJV hd φ
 rw [zLn] at hf
 push Not at hf
 obtain ⟨f,hf,hf0⟩:=hf
 refine ⟨f,hf0,fun p hp=>Set.eq_empty_iff_forall_notMem.mpr fun z hz=>hp ?_⟩
 obtain ⟨hz,h0,h1⟩:=aIB.mp hz
 have hc : ∀ j,eval z (adD (aEL p j))=0:= by
  intro j
  cases j
  · exact h0
  · exact h1
 rw [← d2t hz hc f]
 rw [show (p7 (R:=c9) (aH9 P)) f=0 from hf,qy]
theorem cCy (J:Al) (hd:oy J≤1) :
  aew (fun p=>oj c9 (ke J p) = ∅) := by
 have hopen:=aew.b3e (J.retainedMinimalPrimes 1)
  (fun P p=>oj c9 (ke P p) = ∅) (fun P hP=> by
    have hm:=(Ideal.mem_retainedMinimalPrimes.mp hP).1
    exact dwN hm.isPrime ((Lf hm.le).trans hd))
 obtain ⟨f,hf,h⟩:=hopen
 refine ⟨f,hf,fun p hp=>Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_⟩
 obtain ⟨hz,h0,h1⟩:=aIB.mp hz
 obtain ⟨P,hP,hzP⟩:=G5 J 1 z hz (by simp)
 exact Set.eq_empty_iff_forall_notMem.mp (h p hp P hP) z
  (aIB.mpr ⟨hzP,h0,h1⟩)
end
end akP
end
section
namespace aFV
noncomputable section
open MvPolynomial
variable {k σ:Type} [nX k]
variable {I:lI (cy σ k)} {f :cy σ k}
private theorem guY (h:atV I f) :
    ∃ N :ℕ,∀ n≥N,∀ x :cy σ k ⧸ I,
      lV I f*x∈p6 I (n+1) →
      x∈p6 I n:= by
  obtain ⟨_,N,hN⟩:=h
  refine ⟨N,fun n hn x hx => ?_⟩
  have shrink (r :ℕ) (hr :x∈p6 I (n+r)) :
      x∈p6 I n:= by
    induction r with
    | zero=>exact hr
    | succ r ih =>
      exact ih (hN (n+r) (by omega) x hr
        (zhv I (by omega) hx))
  obtain ⟨m,hm⟩:=exists_mem_quotientDegreeLE I x
  exact shrink m (zhv I (by omega) hm)
variable [vl σ]
private theorem emV (hf :f.totalDegree≤1)
    (hreg:Xg (lV I f)) (n:ℕ)
    (hstrict : ∀ x :cy σ k ⧸ I,
      lV I f*x∈p6 I (n+1) →
        x∈p6 I n) :
    G4 (I ⊔ oz {f}) (n+1)+affineHilbertFunction I n =
      G4 I (n+1) := by
  let J:=I ⊔ oz {f}
  let hIJ:I≤J:=Df
  let U:=p6 I n
  let V:=p6 I (n+1)
  let W:=p6 J (n+1)
  let q:=(SU k hIJ).toLinearMap
  have hq (x :V) :q x∈W:= by
    obtain ⟨p,hp,he⟩:=mem_quotientDegreeLE.mp x.property
    rw [← he]
    exact GR hp
  let cut:V →ₗ[k] W:=(q.domRestrict V).codRestrict W hq
  have hsurj:vZ cut:= by
    intro y
    obtain ⟨p,hp,he⟩:=mem_quotientDegreeLE.mp y.property
    exact ⟨⟨lV I p,GR hp⟩,zg he⟩
  let μ:=(zzN k (lV I f)).domRestrict U
  have hμ (x :U) :μ x∈V:= by
    change lV I f*(x :cy σ k ⧸ I)∈p6 I (n+1)
    have h:=mul_mem_quotientDegreeLE (GR (I:=I) hf) x.property
    simpa only [Nat.add_comm 1 n] using h
  let m:=μ.codRestrict V hμ
  have hfzero :q (lV I f)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (G2 (Mj f))
  have hm (x :U) :m x∈wA cut:= by
    apply LinearMap.mem_ker.mpr
    apply zg
    change q (lV I f*x)=0
    change SU k hIJ (lV I f*x)=0
    rw [lJ]
    change q (lV I f)*q x=0
    rw [hfzero,vh]
  let e :=m.codRestrict (wA cut) hm
  have he_inj:th e := by
    intro x y hxy
    exact zg (hreg (ov
      (fun z :wA cut=>(z.1.1 :cy σ k ⧸ I)) hxy))
  have he_surj:vZ e := by
    intro y
    obtain ⟨p,hp⟩:=zh (I:=I) y.1.1
    have hy :q y.1.1=0:=ov
      (fun z :W=>(z :cy σ k ⧸ J)) (LinearMap.mem_ker.mp y.property)
    have hy' : lV J p=0:= by
      rw [← hp] at hy
      exact hy
    obtain ⟨s,hs,t,ht,hst⟩:=Submodule.mem_sup.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hy')
    obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp ht
    have hr :lV I f* lV I r=y.1.1 := by
      rw [← hp,← hst,qz ,Ideal.Quotient.eq_zero_iff_mem.mpr hs,C9,lJ]
    refine ⟨⟨lV I r,hstrict _ (hr.symm ▸ y.1.2)⟩,?_⟩
    exact zg (zg hr)
  have hker :=(LinearEquiv.ofBijective e ⟨he_inj,he_surj⟩).finrank_eq
  have hrank :=cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,Yi ,← hker] at hrank
  exact hrank
theorem cUK (hf :f.totalDegree≤1) (h:atV I f) :
   n5 (I ⊔ oz {f}) =
     FV 1 (n5 I) := by
 obtain ⟨N,hN⟩:=guY h
 obtain ⟨M,hM⟩:=NY I
 symm
 refine zpB (N₀:=max N M+1) fun n hn => ?_
 have hn' : 1≤n:= by omega
 have hcast: ((n - 1 :ℕ) :ℚ)=(n:ℚ) - 1 := by
   rw [Nat.cast_sub hn',G7]
 rw [zjN,← hcast,hM n (by omega),hM (n - 1) (by omega)]
 apply sub_eq_iff_eq_add.mpr
 have hs :=emV hf h.1 (n - 1) (hN _ (by omega))
 rw [G6 hn'] at hs
 exact_mod_cast hs.symm
end
end aFV
end
section
namespace akP
noncomputable section
open dN lB YW MvPolynomial
open scoped BigOperators
def c1 :Prop :=
  ∀ A:Al,A.IsPrime→ oy A=2 →
    aew (fun p =>
      oy (ke A p)=0∧p9 A=p9 (ke A p))
def c2 :Prop :=
  ∀ A:Al,A.IsPrime→ oy A=2 →
    aew (fun p=>(ke A p).IsRadical)
private theorem b0J {A:Al} {D:PK}
  (hA:A.IsPrime) (hd:oy A=2) (hD:D∉A) :
  oy (A ⊔ oz {D})≤1 := by
 have hc:=(MK
  hA hD (b:=D.totalDegree) zk).1
 change oy (A ⊔ oz {D})≤oy A - 1 at hc
 rwa [hd] at hc
private theorem dXe {A B:Al}
   (hA:A.IsPrime) (hB:B.IsPrime) (hdA:oy A=2) (hdB:oy B=2)
   (hne :A≠B) :oy (A ⊔ B)≤1 := by
 by_cases hAB:B≤A
 · obtain ⟨D,hDA,hDB⟩ : ∃ D∈A,D∉B :=
     Set.not_subset.mp (show ¬ A≤B from fun hBA=>hne (zd hBA hAB))
   have hle :B ⊔ oz {D} ≤ A ⊔ B :=
     Gj le_sup_right ((RJ _).mpr (zKg hDA))
   exact (Lf hle).trans
     (b0J hB hdB hDB)
 · obtain ⟨D,hDB,hDA⟩ : ∃ D∈B,D∉A:=Set.not_subset.mp hAB
   have hle :A ⊔ oz {D} ≤ A ⊔ B :=
     Gj Df ((RJ _).mpr (G2 hDB))
   exact (Lf hle).trans
     (b0J hA hdA hDA)
private theorem dVs {I:Al} (hI:I.IsRadical)
  (hd:oy I=0) {S:nq alk}
  (hS: (S:Set alk)=oj c9 I) :
  p9 I≤(S.card:ℚ) := by
 let:qx c9 (PK ⧸ I) :=
  zhp hd
 have hfinite :=finite_zeroLocus_of_finite_quotient (K:=c9) I
 let:t7 (oj c9 I) :=hfinite.fintype
 have hle :=LinearMap.finrank_le_finrank_of_injective
  (zeroLocusEvaluation_injective (K:=c9) I hI)
 rw [Module.finrank_fintype_fun_eq_card,← Nat.card_eq_fintype_card] at hle
 change pQ c9 (PK ⧸ I)≤(oj c9 I).ncard at hle
 rw [← hS,zik] at hle
 exact (affineDegree_eq_finrank I).trans_le (Nat.cast_le.mpr hle)
theorem of_children (h1 :c1) (h2 :c2) :YW.c2 := by
  classical
  intro T D hT
  let good (A:Al) (p:aha) :Prop :=
    (oy (ke A p)=0∧p9 A=p9 (ke A p)) ∧
      (ke A p).IsRadical∧oj c9 (ke (A ⊔ oz {D}) p) = ∅
  have hgood:aew (fun p => ∀ A∈T,good A p) := by
    apply aew.b3e
    intro A hA
    obtain ⟨hp,hd,hD⟩:=hT A hA
    exact (h1 A hp hd).and ((h2 A hp hd).and
      (cCy _ (b0J hp hd hD)))
  let pairs :=(T ×ˢ T).filter fun AB=>AB.1≠AB.2
  let avoid (AB:Al×Al) (p:aha) :Prop :=
    oj c9 (ke (AB.1 ⊔ AB.2) p) = ∅
  have havoid :aew (fun p => ∀ AB∈pairs,avoid AB p) := by
    apply aew.b3e
    intro AB hAB
    obtain ⟨hAB,hne⟩:=Finset.mem_filter.mp hAB
    obtain ⟨hA,hB⟩:=Finset.mem_product.mp hAB
    exact cCy _ (dXe (hT _ hA).1 (hT _ hB).1
      (hT _ hA).2.1 (hT _ hB).2.1 hne)
  obtain ⟨p,hp,hpair⟩:=(hgood.and havoid).d4x
  let points (A:Al) :nq alk :=
    if hA:A∈T then
      ((finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero
        (ke A p)).2 (hp A hA).1.1).toFinset
    else ∅
  have hpoints (A:Al) (hA:A∈T) (z :alk) :
      z∈points A↔z∈oj c9 (ke A p) := by
    simp [points,hA]
  refine ⟨aEL p t5 ,aEL p true,T.biUnion points,?_,?_,?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨A,hA,hzA⟩:=Finset.mem_biUnion.mp hz
      obtain ⟨hm,ha,hb⟩:=aIB.mp ((hpoints A hA z).mp hzA)
      exact ⟨⟨A,hA,hm⟩,ha,hb⟩
    · rintro ⟨⟨A,hA,hm⟩,ha,hb⟩
      exact Finset.mem_biUnion.mpr
        ⟨A,hA,(hpoints A hA z).mpr (aIB.mpr ⟨hm,ha,hb⟩)⟩
  · intro z hz hD
    obtain ⟨A,hA,hzA⟩:=Finset.mem_biUnion.mp hz
    obtain ⟨hm,ha,hb⟩:=aIB.mp ((hpoints A hA z).mp hzA)
    have hzD:z∈oj c9 (ke (A ⊔ oz {D}) p) :=
      aIB.mpr
        ⟨mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hm,by rwa [uz]⟩,ha,hb⟩
    simp [(hp A hA).2.2] at hzD
  · have hdisjoint:Set.PairwiseDisjoint (T:Set Al) points := by
      intro A hA B hB hne
      apply Finset.disjoint_left.mpr
      intro z hzA hzB
      have hAB: (A,B)∈pairs :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hA,hB⟩,hne⟩
      obtain ⟨hmA,ha,hb⟩:=aIB.mp ((hpoints A hA z).mp hzA)
      have hmB:=(aIB.mp ((hpoints B hB z).mp hzB)).1
      have hzAB:z∈oj c9 (ke (A ⊔ B) p) :=
        aIB.mpr ⟨by rw [zeroLocus_sup]; exact ⟨hmA,hmB⟩,ha,hb⟩
      have hv :oj c9 (ke (A ⊔ B) p) = ∅ := hpair (A,B) hAB
      simp [hv] at hzAB
    rw [Finset.card_biUnion hdisjoint,Nat.cast_sum]
    apply Wm
    intro A hA
    rw [(hp A hA).1.2]
    exact dVs (hp A hA).2.1 (hp A hA).1.1
      (Set.ext fun z=>hpoints A hA z)
end
end akP
end
section
namespace as8
noncomputable section
open dN lB YW akP MvPolynomial
abbrev baO:=Bool×AK
abbrev Oa (A:Al) :=PK ⧸ A
abbrev X6 (A:Al) :=t4 (Oa A)
abbrev abD (A:Al) :=cy baO (Oa A)
def coordinate (A:Al) (i:AK) :Oa A :=
 lV A (lz i)
def aH9 (A:Al) :bbq→abD A
 | (j,some i)=>MvPolynomial.X (j,i)
 | (j,none) => -∑ i,MvPolynomial.X (j,i)*MvPolynomial.C (coordinate A i)
def qw (A:Al) :Zm →ₐ[c9] abD A :=
 p7 (aH9 A)
def cTF (A:Al) :
    Zm →+* t4 (abD A) :=
  (aU (abD A) (t4 (abD A))).comp
    (qw A).toRingHom
end
end as8
end
section
namespace aFV
noncomputable section
open dN lB YW akP MvPolynomial
def c1 :Prop :=
  ∀ (k E :Type) [nX k] [nX E] [nI k E],
    ∀ (t:oD AK→E),GY k t →
      ∀ I:lI (cy AK k),
        atV (I.map (mD (aU k E))) (ahd t)
def c2 :Prop :=
  ∀ J:lI adl,qx dV (aRA ⧸ aN0 J) →
    aew (fun p =>
      qx c9 (PK ⧸ aXS J p) ∧
      pQ c9 (PK ⧸ aXS J p) =
        pQ dV (aRA ⧸ aN0 J))
private theorem b8x {R S T:Type} [ox R] [ox S] [ox T]
  (f :R →+* S) (g:S →+* T) :
  (mD (σ:=AK) g).comp (mD f) =
    mD (g.comp f) := by
 apply u5
 exact Ml f g
private theorem cZh {R S:Type} [ox R] [ox S]
  (f :R →+* S) (t:oD AK→R) :
  mD f (ahd t)=ahd (f ∘ t) := by
 simp only [ahd,qz ,pC,lJ,zi ,zS ,z3s]
private theorem efx (A:Al) :
  aN0 (aFo A)=a4u A ⊔ oz {aU7 true} := by
 unfold aN0 aFo a4u Cl aU7 bHk
 rw [Ok c9 Zm dV,
  zKm]
 simp only [Oc,Qx ,R9,x7,
  b8x,byh,cZh,Function.comp_def]
private theorem gt5 (A:Al) (p:aha) :
  aXS (aFo A) p=ke A p:= by
 have hcoeff : (eval p).comp (C:c9 →+* Zm)=LO GeoField :=
  u5 (fun x=>yl (f :=p) x)
 have hmap_id :mD (σ:=AK) (LO c9) =
   RingHom.id PK:=u5 MvPolynomial.map_id
 have hform (j:Bool) :
   mD (eval p) (byh j)=adD (aEL p j) := by
  simp only [byh,ahd,adD,aEL,qz ,pC,lJ,
   zi ,zS ,wY]
 unfold aXS aFo ke
 simp only [Oc,Qx ,R9,x7,
  b8x,hcoeff,hmap_id,Ideal.map_id,hform]
private theorem cTE (j:Bool) : (aU7 j).totalDegree≤1 := by
 unfold aU7 ahd
 refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
 apply WK
 intro i _
 exact (totalDegree_mul _ _).trans (by simp)
private theorem efB (h:c1) (A:Al) :
   atV (Cl A) (aU7 t5) ∧
     atV (a4u A) (aU7 true) := by
 let t:=bHk t5
 let u:=bHk true
 let L:=Ef c9 (oK t)
 let i:Zm →ₐ[c9] dV :=
   Hw c9 Zm dV
 have hall:=(MvPolynomial.algebraicIndependent_X bbq c9).map'
   (f :=i) (zm Zm dV)
 let e :oD AK ⊕ oD AK→bbq :=
   Nj (fun v=>(true,v)) (fun v=>(t5 ,v))
 have he :th e := by
   intro a b hab
   cases a <;> cases b <;> simp_all [e]
 have hind:GY c9 (Nj u t) := by
   have heval :Nj u t=(i ∘ lz) ∘ e := by
     funext a
     cases a <;> rfl
   rw [heval]
   exact hall.comp e he
 obtain ⟨ht,hu⟩:=AlgebraicIndependent.sumElim_iff.mp hind
 have hu' : GY L u :=
   IntermediateField.algebraicIndependent_adjoin_iff.mpr hu
 let tL:oD AK→L :=
   fun v=>⟨t v,IntermediateField.subset_adjoin c9 _ (Set.mem_range_self v)⟩
 let B:lI (cy AK L) :=
   A.map (mD (aU c9 L)) ⊔ oz {ahd tL}
 have hB:B.map (mD (aU L dV))=a4u A:= by
   unfold B a4u Cl aU7
   simp only [Oc,x7,b8x,Qx ,
     R9,cZh,← Ok]
   rfl
 have hsecond:=h L dV u hu' B
 rw [hB] at hsecond
 exact ⟨h c9 dV t ht A,hsecond⟩
theorem of_children (h1 :c1) (h2 :c2) :akP.c1 := by
 intro A _ hd
 let P:=n5 A
 let D:=FV 1 P
 have hP:P.natDegree=2 :=hd
 have hD:=Te
   (b:=(1 :ℚ)) (P:=P) JK (by omega :0<P.natDegree)
 have hDd:D.natDegree=1 := by simpa [D,hP] using hD.1
 have hDD:=Te
   (b:=(1 :ℚ)) (P:=D) JK (by omega :0<D.natDegree)
 have hbase :n5 (Cl A)=P :=
   Ey.ZI A
 obtain ⟨hreg₁,hreg₂⟩:=efB h1 A
 have hfirst:n5 (a4u A)=D:= by
   rw [a4u,cUK (cTE t5) hreg₁,hbase]
 have hgeneric:n5 (aN0 (aFo A)) =
     FV 1 D:= by
   rw [efx,cUK (cTE true) hreg₂,
     hfirst]
 have hdgen: (n5 (aN0 (aFo A))).natDegree=0:= by
   rw [hgeneric,hDD.1,hDd]
 let:qx dV (aRA ⧸ aN0 (aFo A)) :=
   zhp hdgen
 obtain ⟨g,hg,hopen⟩:=h2 (aFo A) F9
 refine ⟨g,hg,fun p hp => ?_⟩
 obtain ⟨hfin,hrank⟩:=hopen p hp
 let:qx c9 (PK ⧸ aXS (aFo A) p) :=hfin
 have hfiber :n5 (aXS (aFo A) p) =
     n5 (aN0 (aFo A)) := by
   rw [Zg ,Zg ,hrank]
 rw [gt5] at hfiber
 have hdim:oy (ke A p)=0:= by rw [oy ,hfiber,hdgen]
 refine ⟨hdim,?_⟩
 unfold p9
 rw [hP,hfiber,hgeneric,hDD.1,hDD.2,hDd,hD.2,hP]
 norm_num [Nat.factorial,P]
end
end aFV
end
section
set_option backward.isDefEq.respectTransparency false
namespace as8
noncomputable section
open dN lB YW akP MvPolynomial
private theorem euY (A:Al) (p:aha) :
  A≤ke A p :=
 le_sup_left.trans Df
private def K9 (A:Al) (p:aha) :
  abD A →+* (PK ⧸ ke A p) :=
 C5 (Ideal.Quotient.factor (euY A p))
  (fun i:baO=>aU c9 _ (p (i.1,some i.2)))
private theorem gnw (A:Al) (p:aha) :
  vZ (K9 A p) := by
 intro r
 obtain ⟨a,rfl⟩:=zh r
 exact ⟨C (lV A a),yL _ _ _⟩
private theorem dSQ (A:Al) (p:aha) (j:Bool) :
   adD (aEL p j)∈ke A p:= by
 cases j
 · exact zKg (G2 (G9 (by simp)))
 · exact G2 (G9 (by simp))
private theorem dcp (A:Al) (p:aha) :
    (K9 A p).comp (qw A).toRingHom =
      (aU c9 (PK ⧸ ke A p)).comp (eval p) := by
  apply yQ
  · intro a
    change K9 A p (qw A (oq a))=aU c9 _ (eval p (oq a))
    rw [qw,Gi ,zdz,yl,K9,
      yL]
    rfl
  · rintro ⟨j,i⟩
    change K9 A p (qw A (lz (j,i)))=aU c9 _ (eval p (lz (j,i)))
    rw [qw,wR,wY]
    cases i with
    | some i=>exact eval₂Hom_X' _ _ _
    | none =>
      let I:=ke A p
      have h:=Ideal.Quotient.eq_zero_iff_mem.mpr (dSQ A p j)
      rw [adD,qz ,pC] at h
      change aU c9 (PK ⧸ I) (p (j,none)) +
        (∑ i,lV I (oq (p (j,some i))*lz i))=0 at h
      rw [aH9,KA,pC,zZQ h]
      apply ov (fun y :PK ⧸ I => -y)
      apply sI rfl
      intro i _
      simp only [lJ,K9,G1 ,yL,coordinate,
        Ideal.Quotient.factor_mk]
      rfl
private theorem d4Z {P B:Type}
   [ox P] [ox B] [uW B] [nI P B] [WW P B]
   (h: ((aU B (t4 B)).comp (aU P B)).FormallyUnramified) :
   ∃ d:B,d≠0 ∧
     ((aU B (xL d)).comp (aU P B)).FormallyUnramified:= by
 let F:=t4 B
 let I:lI B := ⊥
 let L:=zf I
 have hFr :vj B L:= by
   change C4 (vH B) L
   rw [← Ideal.primeCompl_bot]
   infer_instance
 let e :F ≃ₐ[B] L:=z0R (vH B) F L
 let:Ww P F:= by
   rw [← zDh,Ok P B F]
   exact h
 let:Algebra.IsUnramifiedAt P I :=
   Algebra.FormallyUnramified.of_equiv (e.restrictScalars P)
 obtain ⟨d,hd,hu⟩:=Algebra.exists_formallyUnramified_of_isUnramifiedAt (R:=P) I
 refine ⟨d,(by simpa [I] using hd),?_⟩
 rw [← Ok P B (xL d),
   zDh]
 exact hu
theorem d4Y (A:Al) (hA:A.IsPrime)
    (h: (cTF A).FormallyUnramified) :
    ∃ d:abD A,d≠0 ∧
      ((aU (abD A) (xL d)).comp
        (qw A).toRingHom).FormallyUnramified:= by
  let:A.IsPrime :=hA
  let P:=Zm
  let B:=abD A
  let:nI P B:=(qw A).toRingHom.toAlgebra
  let:sH c9 P B :=
    RC (fun x=>((qw A).commutes x).symm)
  let:WW c9 B :=
    Algebra.FiniteType.trans (S:=Oa A) F9 F9
  let:WW P B :=
    Algebra.FiniteType.of_restrictScalars_finiteType c9 P B
  exact d4Z (P:=P) (B:=B) h
theorem fSS (A:Al) (p:aha)
   {d:abD A} {f :Zm}
   (hu: ((aU (abD A) (xL d)).comp
     (qw A).toRingHom).FormallyUnramified)
   (hf :qw A f∈oz {d}) (hp:eval p f≠0) :
   (ke A p).IsRadical:= by
 let T:=PK ⧸ ke A p
 let B:=abD A
 let g:=K9 A p
 let S:=xL d
 have hf' : g (qw A f)=aU c9 T (eval p f) :=
   vk (dcp A p) f
 have hd:IsUnit (g d) := by
   apply isUnit_of_dvd_unit ((map_dvd g) (Ideal.mem_span_singleton.mp hf))
   rw [hf']
   exact (isUnit_iff_ne_zero.mpr hp).map (aU c9 T)
 let g' : S →+* T:=ztx d hd
 have hg' : g'.comp (aU B S)=g:=zOe d hd
 have hs :vZ g' := by
   intro y
   obtain ⟨x,hx⟩:=gnw A p y
   exact ⟨aU B S x,(vk hg' x).trans hx⟩
 have h:=hu.comp (RingHom.FormallyUnramified.of_surjective (f :=g') hs)
 rw [← RingHom.comp_assoc,hg',dcp] at h
 let:Ww c9 T :=
   RingHom.formallyUnramified_algebraMap.mp (RingHom.FormallyUnramified.of_comp h)
 exact (Ideal.isRadical_iff_quotient_reduced _).mpr
   (Algebra.FormallyUnramified.isReduced_of_field c9 T)
end
end as8
end
section
set_option backward.isDefEq.respectTransparency false
namespace as8
noncomputable section
open dN lB YW akP MvPolynomial Algebra
private theorem ct5 {k S R:Type} [nX k]
  [ox S] [uW S] [ox R] [uW R] [nI k S] [nI k R]
  (g:S →ₐ[k] R) (hg:th g) (hfin:g.Finite) :
  sS k R=sS k S:= by
 let:nI S R:=g.toRingHom.toAlgebra
 let:sH k S R := .of_algebraMap_eq (fun x=>(g.commutes x).symm)
 let:Kz S R:=(JW S R).mpr hg
 let:qx S R:=hfin
 let:zVK S R:=zux S R
 rw [← EP k S (A:=R),Up (R:=S) (A:=R),zE]
theorem dgp (A:Al) (hA:A.IsPrime) (hd:oy A=2) :
   sS c9 (Oa A)=2 := by
 let:A.IsPrime :=hA
 obtain ⟨d,g,hg,hfin⟩:=z4J c9 (Oa A)
 have hdim:oy A=d:= by
   simpa only [VC] using
     zwG g hfin hg
 have hd' : d = 2 :=hdim.symm.trans hd
 rw [ct5 g hg hfin,hd']
 simp [Du]
theorem gxD (A:Al) (hA:A.IsPrime) (hd:oy A=2) :
  sS c9 (X6 A)=2 := by
 let:A.IsPrime :=hA
 let:X8 (Oa A) (X6 A) :=
  IsLocalization.isAlgebraic _ (vH (Oa A))
 rw [← EP c9 (Oa A) (A:=X6 A),
  Up (R:=Oa A) (A:=X6 A),zE,
  dgp A hA hd]
private theorem d00 (k R ι:Type) [nX k]
   [ox R] [uW R] [nI k R] [t7 ι] (hR:sS k R=2) :
   sS k (cy (Bool×ι) R) =
     ((2*(Gr ι+1) :ℕ) :xm) := by
 let:Kz R (cy (Bool×ι) R) :=
   (JW _ _).mpr (C_injective _ _)
 rw [← EP k R (A:=cy (Bool×ι) R),
   zUx,Cardinal.lift_id,hR]
 simp [Du,Pr,Nat.mul_add,Mk,FU]
private theorem bq2 (A:Al) (hA:A.IsPrime) (hd:oy A=2) :
   sS c9 (abD A) =
     ((2*(Gr AK+1) :ℕ) :xm) := by
 let:A.IsPrime :=hA
 exact d00 c9 (Oa A) AK
   (dgp A hA hd)
private theorem d03 (k ι:Type) [nX k] [t7 ι] :
  sS k (cy (Bool×oD ι) k) =
   ((2*(Gr ι+1) :ℕ) :xm) := by
 simp [Du,Pr]
private theorem enV (A:Al) (hA:A.IsPrime) (hd:oy A=2)
  (hinj:th (qw A)) :
  letI:=(qw A).toRingHom.toAlgebra
  X8 Zm (abD A) := by
 let:A.IsPrime :=hA
 let P:=Zm
 let B:=abD A
 let:nI P B:=(qw A).toRingHom.toAlgebra
 change X8 P B
 let:sH c9 P B :=
  .of_algebraMap_eq (fun x=>((qw A).commutes x).symm)
 let:Kz P B:=(JW P B).mpr hinj
 let n:=2*(Gr AK+1)
 have hP:sS c9 P=(n:xm) :=
  d03 c9 AK
 have hadd:=EP c9 P (A:=B)
 rw [hP,bq2 A hA hd] at hadd
 change (n:xm)+trdeg P B=(n:xm) at hadd
 have hz :sS P B=0:= by
  rcases Cardinal.add_eq_left_iff.mp hadd with hc | he
  · exact (Cardinal.natCast_lt_aleph0.not_ge ((le_max_left _ _).trans hc)).elim
  · exact he
 exact (trdeg_eq_zero_iff (R:=P) (A:=B)).mp hz
private theorem d4v {P B:Type} [ox P]
  [ox B] [uW B] [nI P B] {d:B} (hd:d≠0)
  (h:Z0 P d) : ∃ f :P,f≠0∧aU P B f∈oz {d} := by
 obtain ⟨p,hp,hp0⟩:=h
 obtain ⟨q,hq,hn⟩:=Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
 rw [qy ,FQ] at hq hn
 have hq0:z8 d q=0:= by
  rw [hq,lJ,qU,ZJ] at hp0
  exact (mul_eq_zero.mp hp0).resolve_left (pow_ne_zero _ hd)
 refine ⟨q.coeff 0,mt Polynomial.X_dvd_iff.mpr hn,Ideal.mem_span_singleton.mpr ?_⟩
 refine ⟨-Polynomial.aeval d q.divX,?_⟩
 have hh:=ov (z8 d) (Polynomial.X_mul_divX_add q)
 rw [qz ,lJ,ZJ,z8q,hq0] at hh
 rw [mul_neg]
 exact eq_neg_of_add_eq_zero_right hh
theorem d4y (A:Al) (hA:A.IsPrime) (hd:oy A=2)
   (d:abD A) (hd0:d≠0) :
   ∃ f :Zm,f≠0∧qw A f∈oz {d} := by
 let:A.IsPrime :=hA
 by_cases hinj:th (qw A)
 · let:nI Zm (abD A) :=(qw A).toRingHom.toAlgebra
   let:=enV A hA hd hinj
   exact d4v hd0 (Algebra.IsAlgebraic.isAlgebraic d)
 · rw [zLn] at hinj
   push Not at hinj
   obtain ⟨f,hf,hf0⟩:=hinj
   exact ⟨f,hf0,hf.symm ▸ (oz {d}).zero_mem⟩
end
end as8
end
section
set_option backward.isDefEq.respectTransparency false
namespace cyG
open dN lB YW akP aFV
open scoped TensorProduct
noncomputable section
private def aPw (R S σ:Type) [ox R] [ox S] [nI R S]
   (J:lI (cy σ R)) :
   S ⊗[R] (cy σ R ⧸ J) ≃ₐ[S]
     cy σ S ⧸ J.map (mD (aU R S)) := by
 let e :S ⊗[R] cy σ R ≃ₐ[S] cy σ S :=
   zoR R S
 have he :e.toRingHom.comp
     (Kl (A:=S) (R:=R)).toRingHom =
     mD (σ:=σ) (aU R S) := by
   apply u5
   intro p
   change e (1 ⊗ₜ[R] p)= _
   simpa only [e,one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul R S 1 p
 refine (zTd S (cy σ R) S J).trans
   (zpY _ _ e ?_)
 change J.map (mD (aU R S)) =
   (J.map (Kl (A:=S) (R:=R)).toRingHom).map e.toRingHom
 rw [x7,he]
private theorem d4T {R K M N ι:Type} [ox R] [ox K]
  [nI R K] [SD M] [Module R M] [SD N] [Module R N]
  [Module K N] [sH R K N] (S:Pk R) [C4 S K]
  (f :M →ₗ[R] N) [ XB S f] (v :ι→M) (x :M)
  (hx :f x∈yB K (oK (f ∘ v))) :
  ∃ s :S,(s :R)•x∈yB R (oK v) := by
 obtain ⟨a,ha⟩:=multiple_mem_span_of_mem_localization_span S K _ _ hx
 rw [Set.range_comp,← Xu] at ha
 obtain ⟨z,hz,he⟩:=ha
 change f z=(a :R)•f x at he
 rw [← f.map_smul] at he
 obtain ⟨t,ht⟩:=(IsLocalizedModule.eq_iff_exists S f).mp he.symm
 refine ⟨t*a,?_⟩
 change ((t:R)*(a :R))•x∈_
 rw [mul_smul,show (t:R)•((a :R)•x)=(t:R)•z from ht]
 exact (yB R (oK v)).smul_mem _ hz
private theorem d30 (R σ:Type) [ox R] [uW R] [t7 σ]
    (J:lI (cy σ R)) (n:ℕ)
    (b:y5 (Fin n) (t4 R)
      (t4 R ⊗[R] (cy σ R ⧸ J))) :
    ∃ d:R,d≠0 ∧
      Nonempty (y5 (Fin n) (xL d)
        (xL d ⊗[R] (cy σ R ⧸ J))) := by
  classical
  let K:=t4 R
  let S:=vH R
  let B:=cy σ R ⧸ J
  change y5 (Fin n) K (K ⊗[R] B) at b
  let f :B →ₐ[R] K ⊗[R] B:=Kl
  let:sH R K (K ⊗[R] B) :=XG
  let:XB S f.toLinearMap:= by
    change XB S (TensorProduct.mk R K B 1)
    infer_instance
  choose t ht using fun i=>zMS S f.toLinearMap (b i)
  let v :Fin n→B:= fun i=>(t i).1
  let b' := b.isUnitSMul (fun i=>Sv K (t i).2)
  have hv (i:Fin n) :b' i=f (v i) := by
    rw [Module.Basis.isUnitSMul_apply]
    exact (TI K ((t i).2 :R) (b i)).trans (ht i)
  have hrange :oK (f.toLinearMap ∘ v)=oK b' := by
    congr 1
    funext i
    exact (hv i).symm
  let x :σ→B:= fun i=>lV J (lz i)
  let a :Unit ⊕ (σ×Fin n)→B :=
    Nj (fun _=>1) fun ij=>v ij.2*x ij.1
  have hclear (j:Unit ⊕ (σ×Fin n)) :
      ∃ s :S,(s :R)•a j∈yB R (oK v) := by
    apply d4T (K:=K) S f.toLinearMap
    rw [hrange,b'.span_eq]
    trivial
  choose s hs using hclear
  let d:R := ∏ j,(s j:R)
  have hd:d≠0:=Finset.prod_ne_zero_iff.mpr
    (fun j _=>mem_nonZeroDivisors_iff_ne_zero.mp (s j).property)
  let L:=xL d
  let D:=L ⊗[R] B
  let:sH R L D:=XG
  let g:B →ₐ[R] D:=Kl
  let P:Re L D:=yB L (oK (g ∘ v))
  have hgen (z :B) (hz :z∈yB R (oK v)) :g z∈P:= by
    have hP:yB R (oK v)≤(P.restrictScalars R).comap g.toLinearMap:= by
      rw [VH]
      rintro _ ⟨i,rfl⟩
      exact Un ⟨i,rfl⟩
    exact hP hz
  have ha (j:Unit ⊕ (σ×Fin n)) :g (a j)∈P:= by
    have hunit :IsUnit (aU R L (s j:R)) :=
      IsLocalization.Away.isUnit_of_dvd d
        (Finset.dvd_prod_of_mem (fun i=>(s i:R)) (FR j))
    apply (P.smul_mem_iff_of_isUnit hunit).mp
    simpa only [FK,TI L] using hgen _ (hs j)
  have hmul (i:σ) :P≤P.comap (LinearMap.mulRight L (g (x i))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change g (v j)*g (x i)∈P
    rw [← lJ]
    exact ha (Sum.inr (i,j))
  have hone : (1 :D)∈P:= by
    have h:=ha (Sum.inl ())
    change (1 :D)∈P at h
    exact h
  have hall (z :B) :g z∈P:= by
    obtain ⟨p,rfl⟩:=zh z
    induction p using EK with
    | C r =>
      change g (aU R B r)∈P
      rw [g.commutes,t8 R L D,Algebra.algebraMap_eq_smul_one]
      exact P.smul_mem _ hone
    | add p q hp hq =>
      rw [qz ,qz]
      exact P.add_mem hp hq
    | mul_X p i hp =>
      rw [lJ,lJ]
      exact hmul i hp
  have hspan:P = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨⟨y,u⟩,hu⟩ :=
      zMS (JQ d) (TensorProduct.mk R L B 1) z
    apply (P.smul_mem_iff_of_isUnit (Sv L u)).mp
    change (u:R)•z=g y at hu
    rw [TI L,hu]
    exact hall y
  have hle :JQ d≤S :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hd)
  let:nI L K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe L K _ _ hle
  let:sH R L K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le L K _ _ hle
  let:sH L K (K ⊗[R] B) :=XG
  have hinj:th (aU L K) := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (JQ d) _).mpr
    intro r u
    rw [← t8 R L K,← t8 R L K]
    rw [(IsLocalization.injective L hle).eq_iff,(zm R K).eq_iff]
  let gK:D →ₗ[L] K ⊗[R] B :=
    TensorProduct.AlgebraTensorModule.map (zdh L K) (LinearMap.id :B →ₗ[R] B)
  have hcomp:gK ∘ (g ∘ v)=b' := by
    funext i
    rw [hv i]
    change (aU L K 1 ⊗ₜ[R] v i)=(1 ⊗ₜ[R] v i)
    rw [map_one]
  have hli:z14 L (g ∘ v) := by
    apply LinearIndependent.of_comp gK
    rw [hcomp]
    apply b'.linearIndependent.restrict_scalars
    simpa only [Algebra.smul_def,Ee] using hinj
  exact ⟨d,hd,⟨Module.Basis.mk hli hspan.ge⟩⟩
theorem proof :aFV.c2 := by
 intro J hfinite
 let R:=Zm
 let K:=dV
 let B:=adl ⧸ J
 let G:=aRA ⧸ aN0 J
 let n:=pQ K G
 let:qx K G:=hfinite
 let b:=(Module.finBasis K G).map (aPw R K AK J).symm.toLinearEquiv
 obtain ⟨d,hd,⟨b'⟩⟩:=d30 R AK J n b
 refine ⟨d,hd,fun p hp => ?_⟩
 let L:=xL d
 let E :=c9
 let ev :R →+* E :=vi p
 let:nI R E :=ev.toAlgebra
 let hu:IsUnit (ev d) :=isUnit_iff_ne_zero.mpr hp
 let g:L →+* E :=ztx d hu
 let:nI L E :=g.toAlgebra
 let:sH R L E :=
  IsScalarTower.of_algebraMap_eq' (zOe d hu).symm
 let e :=(Algebra.TensorProduct.cancelBaseChange R L E E B).trans
  (aPw R E AK J)
 let basis :y5 (Fin n) E (PK ⧸ aXS J p) :=
  (b'.baseChange E).map e.toLinearEquiv
 refine ⟨zwB basis,?_⟩
 change pQ E (PK ⧸ aXS J p)=n
 rw [Module.finrank_eq_card_basis basis,Fintype.card_fin]
end
end cyG
end
section
namespace bzG
noncomputable section
open MvPolynomial
open scoped TensorProduct nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem eM8 {A ι:Type*} [ox A] [t7 ι]
   (a :ι→A) (j:ι) (q:cy ι A)
   (hq: (∑ i,C (a i)*lz i)*q=0) :
   ∃ n:ℕ,C (a j)^n*q=0:= by
 classical
 let L:=xL (a j)
 let f :cy ι A →+* cy ι L:=mD (aU A L)
 let e :=(Vl L (Equiv.optionSubtypeNe j).symm).trans
   (p5 L {i:ι // i≠j})
 let F:cy ι A →+* IT (cy {i:ι // i≠j} L) :=
   e.toRingHom.comp f
 have hcoeff (i:ι) :
     (F (C (a i)*lz i)).coeff 1=if i=j then C (aU A L (a i)) else 0:= by
   by_cases hij:i=j
   · subst i
     simp [F,f,e,Polynomial.C_mul_X_eq_monomial]
   · simp [F,f,e,Equiv.optionSubtypeNe_symm_of_ne hij,hij]
 have hcoef : (F (∑ i,C (a i)*lz i)).coeff 1=C (aU A L (a j)) := by
   rw [pC,OJ]
   simp only [hcoeff]
   simp
 have hunit :IsUnit (C (aU A L (a j)) :cy {i:ι // i≠j} L) :=
   IsUnit.map C (z4z (a j))
 have hreg:F (∑ i,C (a i)*lz i)∈vH _ :=
   Polynomial.mem_nonzeroDivisors_of_coeff_mem 1 (by rw [hcoef]; exact hunit.mem_nonZeroDivisors)
 have hz :F q=0:=(mem_nonZeroDivisors_iff_left.mp hreg) _ (by
   simpa only [lJ,qy] using ov F hq)
 have hf :f q=0:=e.injective (by simpa [F] using hz)
 have hloc:C4 (JQ (C (σ:=ι) (a j))) (cy ι L) := by
   rw [← Submonoid.map_powers]
   infer_instance
 have hmap :aU (cy ι A) (cy ι L) q=0:=hf
 obtain ⟨m,hm⟩:=(IsLocalization.map_eq_zero_iff (JQ (C (σ:=ι) (a j)))
   (cy ι L) q).mp hmap
 obtain ⟨n,hn⟩:=m.property
 exact ⟨n,by simpa only [hn] using hm⟩
private theorem ec7 {R S:Type*} [ox R] [ox S] [nI R S]
    [Module.Flat R S] (I:lI R) (u v :R) (h:I.colon {u} ≤ I.colon {v}) :
    (I.map (aU R S)).colon {aU R S u} ≤
      (I.map (aU R S)).colon {aU R S v} := by
  let J:=I.map (aU R S)
  let e :S ⊗[R] (R ⧸ I) ≃ₐ[S] S ⧸ J :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
  let m (a :R) : (R ⧸ I) →ₗ[R] (R ⧸ I) :=
    zzN R (lV I a)
  have hker :wA (m u)≤wA (m v) := by
    intro x hx
    obtain ⟨p,rfl⟩:=zh x
    simpa [m,XJ,← lJ,SC,
      Au,qG,pz _ p] using
      (h (show p∈I.colon {u} by
        simpa [m,XJ,← lJ,SC,
          Au,qG,pz _ p] using hx) :
        p∈I.colon {v})
  have hbase :wA (In S S (m u)) ≤
      wA (In S S (m v)) := by
    rw [zai,zai]
    intro x hx
    obtain ⟨z,rfl⟩:=hx
    refine ⟨In S S (Submodule.inclusion hker) z,?_⟩
    induction z using z2P <;>
      simp_all [zbj]
  have he (a :R) (z :S ⊗[R] (R ⧸ I)) :
      e (In S S (m a) z) =
        lV J (aU R S a)*e z := by
    induction z using z2P with
    | tmul s x =>
      obtain ⟨p,rfl⟩:=zh x
      simp only [zbj,m,LinearMap.mulLeft_apply,
        ← lJ,e]
      change lV J ((a*p)•s) =
        lV J (aU R S a)* lV J (p•s)
      rw [← lJ]
      simp only [Algebra.smul_def,lJ,v9]
    | add x y hx hy=>rw [map_add,map_add,hx,hy,map_add,mul_add]
  intro p hp
  rw [Au,qG,← SC,
    lJ] at hp ⊢
  let z :=e.symm (lV J p)
  have hz :e z=lV J p:=e.apply_symm_apply _
  have hu:z∈wA (In S S (m u)) := by
    apply LinearMap.mem_ker.mpr
    apply e.injective
    rw [he,hz,qy]
    exact (pz _ _).trans hp
  have hv :=ov e (LinearMap.mem_ker.mp (hbase hu))
  rw [he,hz,qy ,pz] at hv
  exact hv
private theorem map_comp {R S T σ:Type*} [ox R] [ox S] [ox T]
  (f :R →+* S) (g:S →+* T) :
  (mD (σ:=σ) g).comp (mD f)=mD (g.comp f) :=
 u5 (Ml f g)
private theorem efK {k E ι:Type} [nX k] [nX E]
  [nI k E] {t:ι→E} (ht:GY k t) :
  (p7 t:cy ι k →ₐ[k] E).toRingHom.Flat := by
 let P:=cy ι k
 let F:=t4 P
 let f :P →+* E :=(p7 t).toRingHom
 have hf :th f :=ht
 let g:F →+* E :=zIj (K:=F) hf
 have hg:g.comp (aU P F)=f := by
  apply u5
  intro x
  change g (aU P F x)=f x
  exact zoc (K:=F) hf x
 change f.Flat
 rw [← hg]
 exact (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (vH P))).comp
  (RingHom.Flat.of_isField (Field.toIsField F) g)
private theorem dNy {R:Type*} [ox R] [IsNoetherianRing R]
  (I:lI R) (u v :R) (h : ∀ q,u*q∈I → ∃ n:ℕ,v^n*q∈I) :
  ∃ n:ℕ,I.colon {u} ≤ I.colon {v^n} := by
 classical
 let J:=I.colon {u}
 obtain ⟨s,hs⟩:=J.fg_of_isNoetherianRing
 have hx (a :s) :u*a.1∈I:= by
  have hm: (a :R)∈J:=hs ▸ Un a.property
  simpa only [J,Au,qG,pz (a :R) u] using hm
 choose n hn using fun a :s=>h a (hx a)
 refine ⟨s.attach.sup n,?_⟩
 change J≤I.colon {v^s.attach.sup n}
 rw [← hs]
 apply Submodule.span_le.mpr
 intro a ha
 let b:s :=⟨a,ha⟩
 have hb:n b≤ s.attach.sup n:=Xx (s.mem_attach b)
 apply Submodule.mem_colon_singleton.mpr
 rw [qG,pz a,← G6 hb,Et,v9]
 exact I.mul_mem_left _ (hn b)
theorem bHq {k E σ ι:Type} [nX k] [nX E] [nI k E]
   [vl σ] [t7 ι] [vl ι] {t:ι→E} (ht:GY k t)
   (I:lI (cy σ k)) (a :ι→cy σ k)
   (j:ι) (q:cy σ E)
   (hq: (∑ i,C (t i)*mD (aU k E) (a i))*q ∈
     I.map (mD (aU k E))) :
   ∃ n:ℕ,(mD (aU k E) (a j))^n*q ∈
     I.map (mD (aU k E)) := by
 let P:=cy ι k
 let R:=cy σ k
 let U:=cy σ P
 let i:R →+* U:=mD C
 let B:=I.map i
 let u:U := ∑ l,C (lz l)*i (a l)
 let F:U →+* cy ι (R ⧸ I) :=
   (mD (lV I)).comp (z7 k σ ι).toRingHom
 have hi (p:R) : (z7 k σ ι) (i p)=C p:= by
   have h: (z7 k σ ι).symm (C p)=i p:= Qy p
   rw [← h,zIH]
 have hFi (p:R) :F (i p)=C (lV I p) := by
   change (mD (lV I)) ((z7 k σ ι) (i p))= _
   rw [hi,zi]
 have hFX (l:ι) :F (C (lz l))=lz l:= by
   change (mD (lV I))
     ((z7 k σ ι) (C (lz l)))= _
   rw [commAlgEquiv_C_X,zS]
 have hFu:F u = ∑ l,C (lV I (a l))*lz l:= by
   simp only [u,pC,lJ,hFi,hFX,pz]
 have hF:vG F=B:= by
   let e :=z7 k σ ι
   rw [show F=(mD (lV I)).comp e.toRingHom from rfl,
     ← RingHom.comap_ker,zRA,Ideal.mk_ker]
   change (I.map C).comap e.toRingHom=I.map i
   have hC:C=e.toRingHom.comp i:=u5 (fun p=>(hi p).symm)
   rw [hC,← x7]
   exact UZ e.toRingHom e.bijective
 obtain ⟨n,hn⟩:=dNy B u (i (a j)) (by
   intro p hp
   have hzero :F (u*p)=0:=RingHom.mem_ker.mp (hF.symm ▸ hp)
   rw [lJ,hFu] at hzero
   obtain ⟨n,hn⟩:=eM8 (fun l=>lV I (a l)) j (F p) hzero
   refine ⟨n,hF ▸ RingHom.mem_ker.mpr ?_⟩
   simpa only [lJ,qU,hFi] using hn)
 let ev :P →+* E :=(p7 t).toRingHom
 let f :U →+* cy σ E :=mD ev
 let:nI P E :=ev.toAlgebra
 have hf :f.Flat :=RingHom.Flat.isStableUnderBaseChange P E U (cy σ E)
   (efK ht)
 let:nI U (cy σ E) :=f.toAlgebra
 have :Module.Flat U (cy σ E) :=hf
 have hev :ev.comp (C:k →+* P)=aU k E :=
   u5 (fun x=>Gi t x)
 have hfi:f.comp i=mD (aU k E) := by
   rw [show f=mD ev from rfl,show i=mD C from rfl,
     map_comp,hev]
 have hB:B.map f=I.map (mD (aU k E)) := by
   rw [show B=I.map i from rfl,x7,hfi]
 have hu:f u = ∑ l,C (t l)*mD (aU k E) (a l) := by
   simp only [u,pC,lJ]
   refine sI rfl fun l _ => ?_
   rw [show f (i (a l))=(f.comp i) (a l) from rfl,hfi]
   change mD ev (C (lz l))*_ = _
   rw [zi ,show ev (lz l)=t l from wR t l]
 have h:=ec7 (R:=U) (S:=cy σ E) B u (i (a j)^n) hn
 change (B.map f).colon {f u} ≤ (B.map f).colon {f (i (a j)^n)} at h
 rw [hB,hu,qU,show f (i (a j))=(f.comp i) (a j) from rfl,hfi] at h
 refine ⟨n,?_⟩
 have hmem:q∈(I.map (mD (aU k E))).colon
     {∑ l,C (t l)*mD (aU k E) (a l)} := by
   apply Submodule.mem_colon_singleton.mpr
   rw [qG,pz]
   exact hq
 simpa only [Au,qG,pz q] using h hmem
end
end bzG
end
section
namespace as8
noncomputable section
open dN lB YW akP
def c1 :Prop :=
  ∀ A:Al,A.IsPrime→ oy A=2 →
    ∃ (i:Fin 2→AK)
      (b:y5 (Fin 2) (X6 A) Ω[ X6 A⁄c9]),
      ∀ j,b j=Aa c9 (X6 A)
        (aU (Oa A) (X6 A) (coordinate A (i j)))
def c2 :Prop :=
  ∀ (A:Al),A.IsPrime →
    ∀ (i:Fin 2→AK)
      (b:y5 (Fin 2) (X6 A) Ω[ X6 A⁄c9]),
      (∀ j,b j=Aa c9 (X6 A)
        (aU (Oa A) (X6 A) (coordinate A (i j)))) →
      (cTF A).FormallyUnramified
theorem of_children (h1 :c1) (h2 :c2) :akP.c2 := by
 intro A hA hd
 obtain ⟨i,b,hb⟩:=h1 A hA hd
 obtain ⟨d,hd0,hu⟩:=d4Y A hA (h2 A hA i b hb)
 obtain ⟨f,hf0,hf⟩:=d4y A hA hd d hd0
 exact ⟨f,hf0,fun p hp=>fSS A p hu hf hp⟩
end
end as8
end
section
namespace cyH
noncomputable section
open dN lB YW as8
open KaehlerDifferential nonZeroDivisors
private def gpK {k E :Type} [nX k] [nX E] [nI k E]
   {ι:Type} {x :ι→E} (hx :GY k x)
   (hsep:ZK (Ef k (oK x)) E) :
   y5 ι E Ω[E⁄k] := by
 let P:=cy ι k
 let T:=Ef k (oK x)
 let e :t4 P ≃ₐ[k] T:=hx.aevalEquivField
 let f :P →+* T:=e.toRingHom.comp (aU P (t4 P))
 letI:nI P T:=f.toAlgebra
 letI:nI P E :=((aU T E).comp f).toAlgebra
 letI:sH P T E := .of_algebraMap_eq' rfl
 letI:sH k P E := .of_algebraMap_eq fun a=> by
   change aU k E a=aU T E (e (aU P (t4 P) (aU k P a)))
   rw [← t8 k P (t4 P),e.commutes,
     ← t8 k T E]
 let eP:t4 P ≃ₐ[P] T :=
   { e.toRingEquiv with commutes' := fun _=>rfl }
 letI:vj P T:=IsFractionRing.of_algEquiv eP
 letI:Yc P T := .of_isLocalization (vH P)
 letI:ZK T E :=hsep
 letI:Yc T E := .of_isSeparable T E
 letI:Yc P E := .comp P T E
 exact ((mvPolynomialBasis k ι).baseChange E).map (tensorKaehlerEquivOfFormallyEtale k P E)
private theorem gtr (A:Al) :
    yB (X6 A) (oK (fun i:AK =>
      D c9 (X6 A)
        (aU (Oa A) (X6 A) (coordinate A i)))) = ⊤ := by
  let R:=Oa A
  let K:=X6 A
  let f :PK →ₐ[c9] K :=
    (Hw c9 R K).comp (Zi c9 A)
  let v :AK→Ω[K⁄c9] := fun i=>D c9 K (f (lz i))
  let W:=yB K (oK v)
  change W = ⊤
  have hpoly (p:PK) :D c9 K (f p)∈W:= by
    induction p using EK with
    | C a =>
      change D c9 K (f (aU c9 PK a))∈W
      rw [f.commutes,Derivation.map_algebraMap]
      exact W.zero_mem
    | add p q hp hq =>
      rw [qz ,qz]
      exact W.add_mem hp hq
    | mul_X p i hp =>
      rw [lJ,Ea]
      exact W.add_mem (W.smul_mem _ (Un ⟨i,rfl⟩)) (W.smul_mem _ hp)
  apply top_unique
  rw [← span_range_map_derivation_of_isLocalization c9 R K (vH R)]
  apply Submodule.span_le.mpr
  rintro _ ⟨r,rfl⟩
  obtain ⟨p,rfl⟩:=zh r
  rw [z3s,map_D]
  exact hpoly p
theorem proof :as8.c1 := by
 classical
 intro A hA hd
 let:A.IsPrime :=hA
 let R:=Oa A
 let K:=X6 A
 let:zl5 R K := .of_isLocalization K (vH R)
 let:zl5 c9 K := .comp c9 R K
 obtain ⟨s,hs,hsep⟩:=exists_isTranscendenceBasis_and_isSeparable_of_perfectField c9 K
 have hsCard:Gr s=2 := by
   apply Nat.cast_injective (R:=xm)
   exact (Du s).symm.trans
     (hs.cardinalMk_eq_trdeg.trans (gxD A hA hd))
 have hsep' : ZK
     (Ef c9 (oK ((↑) :s→K))) K:= by
   rw [show oK ((↑) :s→K)=(s :Set K) from Subtype.range_coe]
   exact hsep
 let bSep:=gpK hs.1 hsep'
 let v :AK→Ω[K⁄c9] := fun i =>
   D c9 K (aU R K (coordinate A i))
 obtain ⟨κ,a,_,ha,hli⟩:=exists_linearIndependent' K v
 let b:y5 κ K Ω[K⁄c9] :=
   Module.Basis.mk hli (ha.trans (gtr A)).ge
 let e :κ ≃ Fin 2 :=(b.indexEquiv bSep).trans (Fintype.equivFinOfCardEq hsCard)
 refine ⟨a ∘ e.symm,b.reindex e,fun j => ?_⟩
 rw [Module.Basis.reindex_apply,Module.Basis.mk_apply]
 rfl
end
end cyH
end
section
set_option backward.isDefEq.respectTransparency false
namespace cyI
noncomputable section
open dN lB YW akP as8
open MvPolynomial
private theorem eMW {ι K:Type*} [t7 ι] [nX K]
   (i:Fin 2→ι) (q:ι→Fin 2→K)
   (hq : ∀ s t,q (i s) t=if s=t then 1 else 0) :
   let entry :Bool→Fin 2→cy (Bool×ι) K :=
     fun r s => ∑ t,lz (r,t)*C (q t s)
   entry t5 0*entry true 1-entry t5 1*entry true 0≠0:= by
 classical
 intro entry
 let Ig (r :Bool) :Fin 2 :=if r then 1 else 0
 let value (v :Bool×ι) :K:=if v.2=i (Ig v.1) then 1 else 0
 have heval (r :Bool) (s :Fin 2) :eval value (entry r s)=q (i (Ig r)) s := by
   change eval value (∑ t,lz (r,t)*C (q t s))= _
   simp only [pC,lJ,wY ,yl]
   rw [Qw (i (Ig r))]
   · simp [value]
   · intro t _ ht
     simp [value,ht]
   · simp
 intro hz
 have he :=ov (eval value) hz
 simp [heval,hq,Ig] at he
private theorem eow {ι R K L:Type*} [ox R] [uW R]
   [nX K] [nI R K] [vj R K]
   [nX L] [nI (cy ι R) L] [vj (cy ι R) L]
   [nI K L]
   (hcoef : ∀ r :R,aU K L (aU R K r)=aU (cy ι R) L (C r)) :
   th (p7 (R:=K) fun t:ι =>
     aU (cy ι R) L (lz t)) := by
 let B:=cy ι R
 let B' := cy ι K
 let L' := t4 B'
 let j:B →+* B' := mD (aU R K)
 let j_inj:th j :=
   MvPolynomial.map_injective (aU R K) (zm R K)
 let e :L →+* L' := IsFractionRing.map j_inj
 have he (p:B) :e (aU B L p)=aU B' L' (j p) :=
   IsLocalization.map_eq _ p
 have hK:e.comp (aU K L)=(aU B' L').comp C:= by
   apply IsFractionRing.ringHom_ext (A:=R)
   intro r
   change e (aU K L (aU R K r))=aU B' L' (C (aU R K r))
   rw [hcoef,he]
   exact ov (aU B' L') (zi (σ:=ι) (aU R K) r)
 let f :B' →ₐ[K] L:=p7 (fun t:ι=>aU B L (lz t))
 have hf :e.comp f.toRingHom=aU B' L' := by
   apply yQ
   · intro r
     change e (f (C r))=aU B' L' (C r)
     rw [show f (C r)=aU K L r from Gi _ _]
     exact vk hK r
   · intro t
     change e (f (lz t))=aU B' L' (lz t)
     rw [show f (lz t)=aU B L (lz t) from wR _ _,he]
     exact ov (aU B' L') (zS (σ:=ι) (aU R K) t)
 intro p q hpq
 apply zm B' L'
 rw [← hf]
 exact ov e hpq
private theorem gs3 {F M:Type*} [nX F] [SD M] [Module F M]
    (a b c d:F) (x y :M) (hdet:a*d - b*c≠0)
    (h₀:a•x+b•y=0) (h₁:c•x+d•y=0) :x=0∧y=0:= by
  constructor <;> apply (zBU hdet).mp
  · calc
      (a*d - b*c)•x=d•(a•x+b•y) - b•(c•x+d•y) := by
        simp only [sub_smul,smul_add,smul_smul,pz d a,pz d b]
        abel
      _=0:= by rw [h₀,h₁,zR,zR,FQ]
  · calc
      (a*d - b*c)•y=a•(c•x+d•y) - c•(a•x+b•y) := by
        simp only [sub_smul,smul_add,smul_smul,pz c a,pz c b]
        abel
      _=0:= by rw [h₀,h₁,zR,zR,FQ]
private theorem enW {ι k R P K L:Type*} [t7 ι]
    [ox k] [ox R] [uW R] [ox P] [nI k R] [nI k P]
    [nX K] [nI R K] [vj R K] [nI k K] [sH k R K]
    [nX L] [nI (cy (Bool×ι) R) L] [vj (cy (Bool×ι) R) L]
    (parameter :P →ₐ[k] cy (Bool×ι) R) (coord:ι→R)
    (linear :Bool→ι→P) (constant:Bool→P)
    (hlinear : ∀ r t,parameter (linear r t)=lz (r,t))
    (hconstant : ∀ r,parameter (constant r) = -∑ t,lz (r,t)*C (coord t))
    (i:Fin 2→ι) (b:y5 (Fin 2) K Ω[K⁄k])
    (hb : ∀ s,b s=Aa k K (aU R K (coord (i s)))) :
    ((aU (cy (Bool×ι) R) L).comp parameter.toRingHom).FormallyUnramified:= by
  classical
  let B:=cy (Bool×ι) R
  let:nI P L:=((aU B L).comp parameter.toRingHom).toAlgebra
  change Ww P L
  let coef :R →+* L:=(aU B L).comp C
  have hcoef_inj:th coef :=
    (zm B L).comp (C_injective _ _)
  let:nI K L:=(zIj hcoef_inj:K →+* L).toAlgebra
  have hcoef (r :R) :aU K L (aU R K r)=aU B L (C r) :=
    zoc hcoef_inj r
  let baseToL:k →+* L:=(aU K L).comp (aU k K)
  let:nI k L:=baseToL.toAlgebra
  let:sH k K L:=RC (fun _=>rfl)
  let:sH k P L := .of_algebraMap_eq fun c=> by
    change aU K L (aU k K c)=aU B L (parameter (aU k P c))
    calc
      _=aU K L (aU R K (aU k R c)) :=
        ov (aU K L) (t8 k R K c)
      _=aU B L (C (aU k R c)) :=hcoef _
      _ = _:=ov (aU B L) (parameter.commutes c).symm
  let D:=Aa P L
  let liftD:=KaehlerDifferential.map k P K L
  have hnatural (r :R) :
      liftD (Aa k K (aU R K r)) =
        D (aU B L (C r)) :=
    (KaehlerDifferential.map_D k P K L _).trans (ov D (hcoef r))
  let z (t:ι) :K:=aU R K (coord t)
  let x (r :Bool) (t:ι) :L:=aU B L (lz (r,t))
  let q (t:ι) (s :Fin 2) :K:=b.repr (Aa k K (z t)) s
  let v (s :Fin 2) :=liftD (b s)
  let entry (r :Bool) (s :Fin 2) :L := ∑ t,x r t*aU K L (q t s)
  have hvar (r :Bool) (t:ι) :D (aU B L (lz (r,t)))=0:= by
    have h:=D.map_algebraMap (linear r t)
    change D (aU B L (parameter (linear r t)))=0 at h
    rwa [hlinear] at h
  have hconst (r :Bool) : ∑ t,x r t•D (aU B L (C (coord t)))=0:= by
    have h:=D.map_algebraMap (constant r)
    change D (aU B L (parameter (constant r)))=0 at h
    simpa only [hconstant,KA,pC,lJ,Ea ,hvar,
      zR,zE,neg_eq_zero] using h
  have hcoord (t:ι) :
      D (aU B L (C (coord t))) = ∑ s,aU K L (q t s)•v s := by
    calc
      _=liftD (Aa k K (z t)) :=(hnatural (coord t)).symm
      _=liftD (∑ s,q t s•b s) :=ov liftD (b.sum_repr _).symm
      _ = _:= by simp only [pC,FK,IsScalarTower.algebraMap_smul,v]
  have hrow (r :Bool) : ∑ s,entry r s•v s=0:= by
    calc
      _ = ∑ s,∑ t,(x r t*aU K L (q t s))•v s := by
        simp only [entry,Finset.sum_smul]
      _ = ∑ t,∑ s,(x r t*aU K L (q t s))•v s :=Finset.sum_comm
      _=0:= by
        simpa only [hcoord,PM,smul_smul] using hconst r
  have hq (s t:Fin 2) :q (i s) t=if s=t then 1 else 0:= by
    change b.repr (Aa k K (z (i s))) t= _
    rw [← hb s,b.repr_self_apply]
  let f :cy (Bool×ι) K →ₐ[K] L:=p7 (fun t=>x t.1 t.2)
  have hf :th f :=eow hcoef
  let polyEntry (r :Bool) (s :Fin 2) :cy (Bool×ι) K :=
    ∑ t,lz (r,t)*C (q t s)
  have hfEntry (r :Bool) (s :Fin 2) :f (polyEntry r s)=entry r s := by
    simp only [polyEntry,entry,f,pC,lJ,wR,Gi]
  have hdet:entry t5 0*entry true 1-entry t5 1*entry true 0≠0:= by
    have h:=eMW i q hq
    change polyEntry t5 0*polyEntry true 1 - polyEntry t5 1*polyEntry true 0≠0 at h
    intro hz
    apply h
    apply hf
    simpa only [yU,lJ,qy ,hfEntry] using hz
  have hv :=gs3 (entry t5 0) (entry t5 1) (entry true 0) (entry true 1)
    (v 0) (v 1) hdet (by simpa only [Fin.sum_univ_two] using hrow t5)
    (by simpa only [Fin.sum_univ_two] using hrow true)
  have hLift:liftD =0:= by
    apply b.ext
    intro s
    change v s=0
    fin_cases s
    · exact hv.1
    · exact hv.2
  have hC (r :R) :D (aU B L (C r))=0:= by
    rw [← hnatural r,hLift,LinearMap.zero_apply]
  have hpoly (p:B) :D (aU B L p)=0:= by
    induction p using EK with
    | C r=>exact hC r
    | add p q hp hq=>simp only [map_add,hp,hq,add_zero]
    | mul_X p t hp =>
        obtain ⟨r,t⟩:=t
        simp only [lJ,Ea ,hp,hvar,zR,zE]
  have hall (y :L) :D y=0:= by
    obtain ⟨⟨p,d⟩,he⟩:=IsLocalization.surj (vH B) y
    have hd:aU B L (d:B)≠0 :=
      fun hz=>zyw d.2 ((IsFractionRing.to_map_eq_zero_iff (K:=L)).mp hz)
    have h:=ov D he
    simp only [Ea ,hpoly,zR,C9] at h
    exact (zBU hd).mp h
  refine ⟨(subsingleton_iff_forall_eq 0).mpr ?_⟩
  suffices h: (⊤ : Re L Ω[L⁄P]) ≤ ⊥ by
    exact fun y=>h (show y∈(⊤ : Re L Ω[L⁄P]) from trivial)
  rw [← KaehlerDifferential.span_range_derivation P L,VH]
  rintro _ ⟨y,rfl⟩
  exact hall y
theorem proof :as8.c2 := by
 intro A hA i b hb
 let:A.IsPrime :=hA
 exact enW
  (ι:=AK) (k :=c9) (R:=Oa A) (P:=Zm)
  (K:=X6 A) (L:=t4 (as8.abD A))
  (qw A) (coordinate A)
  (fun r t=>lz (r,some t)) (fun r=>lz (r,none))
  (fun r t=>wR _ (r,some t)) (fun r=>wR _ (r,none)) i b hb
end
end cyI
end
section
namespace cyF
noncomputable section
open dN lB YW MvPolynomial
private theorem cqa {f g:oZ} (hf :f≠0) (hrel :IsRelPrime f g)
    {P:lI oZ} (hP:P∈(Ib f g).minimalPrimes) :
    (n5 P).natDegree=2 := by
  rw [Ib,Ideal.span_insert] at hP
  let:=hP.isPrime
  obtain ⟨Q,hQ,hQP⟩:=zXL
    (show oz {f} ≤ P from le_sup_left.trans hP.le)
  let:=hQ.isPrime
  have hgQ:g∉Q:= by
    intro hg
    obtain ⟨y,hy,hgy⟩:=Ideal.exists_mul_mem_of_mem_minimalPrimes hQ hg
    exact hy (Ideal.mem_span_singleton.mpr
      (hrel.dvd_of_dvd_mul_left (Ideal.mem_span_singleton.mp hgy)))
  have hcut:P∈(Q ⊔ oz {g}).minimalPrimes :=
    ⟨⟨hP.isPrime,Gj hQP (le_sup_right.trans hP.le)⟩,fun J hJ hJP ↦
      hP.2 ⟨hJ.1,Gj (hQ.le.trans (le_sup_left.trans hJ.2))
        (le_sup_right.trans hJ.2)⟩ hJP⟩
  have hQdim:=natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hf hQ
  rw [VC] at hQdim
  have hPdim:=Pf hgQ hcut
  omega
private abbrev VF (C:t6) (P:lI oZ) :=
 xL (lV P C.denom)
private def localize (C:t6) (P:lI oZ) :oZ →ₐ[c9] VF C P :=
 (Hw c9 (oZ ⧸ P) (VF C P)).comp
   (Zi c9 P)
private def aOc (C:t6) (P:lI oZ) :VF C P :=
 IsLocalization.Away.invSelf (lV P C.denom)
private theorem cYF (C:t6) (P:lI oZ) :
  localize C P C.denom*aOc C P=1 :=
 IsLocalization.Away.mul_invSelf (lV P C.denom)
private def qR (C:t6) (P:lI oZ) :
  PK →ₐ[c9] VF C P :=
 p7 fun i ↦ localize C P (C.numerator i)*aOc C P
private theorem dH8 (C:t6) (P:lI oZ) (q:oZ) :
  qR C P (t3 au8 q)=localize C P q:= by
 have h: (qR C P).comp (t3 au8)=localize C P:= by
  apply zpI
  intro i
  change qR C P (t3 au8 (lz i)) =
   localize C P (lz i)
  rw [rename_X,qR,wR,
   show C.numerator (au8 i)=lz i*C.denom from C.initial i,
   lJ,v9,cYF,Ee]
 exact Kv h q
section Evaluation
variable {C:t6} {P:lI oZ} {y :KE}
private def Bt (hy :y∈oj c9 P) : (oZ ⧸ P) →ₐ[c9] GeoField :=
 zTA P (p7 y) fun q hq ↦ hy q hq
private def amk (hy :y∈oj c9 P) (hD:eval y C.denom≠0) :
  VF C P →ₐ[c9] GeoField :=
 IsLocalization.Away.liftAlgHom (f :=Bt hy) (lV P C.denom)
  (isUnit_iff_ne_zero.mpr hD)
private theorem aII (hy :y∈oj c9 P)
  (hD:eval y C.denom≠0) (q:oZ) :
  amk hy hD (localize C P q)=eval y q :=
 IsLocalization.Away.lift_eq (g:=(Bt hy).toRingHom)
  (lV P C.denom) (isUnit_iff_ne_zero.mpr hD) (lV P q)
private theorem bfV (hy :y∈oj c9 P)
   (hD:eval y C.denom≠0) (q:PK) :
   amk hy hD (qR C P q)=eval (BQ C y) q:= by
 have hu:=ov (amk hy hD) (cYF C P)
 rw [lJ,aII,map_one] at hu
 have hi:amk hy hD (aOc C P)=(eval y C.denom)⁻¹:= by
   rw [← one_div]
   apply (eq_div_iff hD).mpr
   exact (pz _ _).trans hu
 have h: (amk hy hD).comp (qR C P)=p7 (BQ C y) := by
   apply zpI
   intro i
   change amk hy hD (qR C P (lz i)) =
     p7 (BQ C y) (lz i)
   rw [qR,wR,lJ,aII,hi,wR,BQ,div_eq_mul_inv]
 exact Kv h q
end Evaluation
private theorem bHO (C:t6) (P:lI oZ) [P.IsPrime]
    (hD:C.denom∉P) :ajF C P=vG (qR C P).toRingHom:= by
  ext q
  change q∈ajF C P↔qR C P q=0
  constructor
  · intro hq
    obtain ⟨n,a,ha⟩:=IsLocalization.Away.surj (lV P C.denom) (qR C P q)
    obtain ⟨p,rfl⟩:=zh a
    change qR C P q*localize C P C.denom^n=localize C P p at ha
    have hp:p∈P:= by
      have hmul :C.denom*p∈P:= by
        rw [← Iw (K:=c9) P]
        intro y hy
        change eval y (C.denom*p)=0
        by_cases hyD:eval y C.denom=0
        · rw [lJ,hyD,vh]
        · have hz :eval (BQ C y) q=0 :=
            hq _ ⟨y,⟨hy,hyD⟩,rfl⟩
          have he :=ov (amk hy hyD) ha
          rw [lJ,qU,bfV,aII,aII,
            hz,vh] at he
          rw [lJ,← he,G0]
      exact (‹P.IsPrime›.mem_or_mem hmul).resolve_left hD
    have hp0:localize C P p=0:= by
      change aU (oZ ⧸ P) (VF C P) (lV P p)=0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp,qy]
    rw [hp0] at ha
    exact ((z4z (S:=VF C P)
      (lV P C.denom)).pow n).mul_right_cancel (ha.trans (vh _).symm)
  · intro hq
    rintro _ ⟨y,⟨hy,hyD⟩,rfl⟩
    change eval (BQ C y) q=0
    rw [← bfV hy hyD,hq,qy]
private theorem aTz (C:t6) (P:lI oZ) [P.IsPrime]
   (hD:C.denom∉P) :
   (ajF C P).IsPrime∧oy (ajF C P)=(n5 P).natDegree := by
 have hne :lV P C.denom≠0:=mt Ideal.Quotient.eq_zero_iff_mem.mp hD
 let:uW (VF C P) :=Localization.Away.isDomain hne
 have hreg:Xg (lV P C.denom) :=(IsRegular.of_ne_zero hne).1
 unfold oy
 rw [bHO C P hD]
 refine ⟨zgL _,zd ?_ ?_⟩
 · let e :=awayPresentationEquiv P C.denom
   exact (natDegree_affineHilbertPolynomial_le_of_injective
     (e.symm.toAlgHom.comp (Ideal.kerLiftAlg (qR C P)))
     (e.symm.injective.comp (Ideal.kerLiftAlg_injective (qR C P)))).trans
     (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le P C.denom)
 · exact natDegree_affineHilbertPolynomial_le_of_away_range P C.denom hreg (qR C P)
     (fun q ↦ ⟨t3 au8 q,dH8 C P q⟩) zk
theorem proof :YW.c1 := by
 intro f g hf _ hfg C P hP
 obtain ⟨hmin,hD⟩:=Ideal.mem_retainedMinimalPrimes.mp hP
 let:=hmin.isPrime
 obtain ⟨hprime,hdim⟩:=aTz C P hD
 exact ⟨hprime,hdim.trans (cqa hf hfg hmin)⟩
end
end cyF
end
section
set_option backward.isDefEq.respectTransparency false
namespace ac1
noncomputable section
open aR oR B7
open scoped Polynomial
def c1 :Prop :=
  ∀ f :af 3,∃ (m:ℕ) (v :rS→af 3),
    ∀ (F:Type) [nX F] (k :ao →+* F) (U:F[X]) (x :F),
      U.natDegree<bf→jW k U f=0 →
      ee k x (rD x U) (pU f)≠0 →
      ∀ a :rS,ee k x (rD x U) (pU f)^m*U.coeff a.val =
        ee k x (rD x U) (v a)
end
end ac1
end
section
namespace bam
noncomputable section
open aR oR B7 ac1 Polynomial
open scoped BigOperators
private abbrev exponent:ℕ:=2*bf
private def ayl (f :af 3) :ℕ→af 3
 | 0=>separant f^exponent*MvPolynomial.X 0
 | 1=>separant f^exponent*MvPolynomial.X 1
 | 2=>separant f^exponent*MvPolynomial.X 2
 | j+3 =>
   let scale :=2*(↑(j+3).factorial:ao)⁻¹
   pU f^(exponent - (2*j+1)) *
     (oq (oY scale)*AR f j)
private def bCH (f :af 3) (length:ℕ) : (af 3)[X] :=
 u9 (-MvPolynomial.C qJ)
  (∑ i:Fin length,Kh i.val (ayl f i.val))
section Evaluation
variable {F:Type*} [nX F]
private theorem d1W (k :ao →+* F) (U:F[X]) (x :F) (f :af 3)
    (hf :jW k U f=0) (n:ℕ) (hn:n<bf) :
    ee k x (rD x U) (ayl f n) =
      ee k x (rD x U) (pU f)^exponent*(qm n U).eval x := by
  let e :=ee k x (rD x U)
  let s :=e (pU f)
  change e (ayl f n)=s^exponent*(qm n U).eval x
  have eX (i:Fin 3) :e (lz i)=(qm i.val U).eval x :=
    G1 _ _ _
  rcases n with _ | _ | _ | j
  · rw [ayl,lJ,qU,eX]
    rfl
  · rw [ayl,lJ,qU,eX]
    rfl
  · rw [ayl,lJ,qU,eX]
    rfl
  have hc:e (AR f j) =
      s^(2*j+1)*((G3^[j + 1]) (qm 2 U)).eval x := by
    simp only [s,e,← bdt,bFn _ _ _ hf,eval_mul,eval_pow]
  have hscale :e (oq (oY (2*(↑(j+3).factorial:ao)⁻¹))) =
      2*(↑(j+3).factorial:F)⁻¹:= by
    simp [e,ee,Pj]
  have hfact : (↑(j+3).factorial:F)≠0:= by
    have hg:=lB.ahA
      (hn.trans (by decide :bf<K1.p))
    simpa only [Il] using (map_ne_zero_iff k k.injective).mpr hg
  have hderiv :
      2*((G3^[j + 1]) (qm 2 U)).eval x =
        (↑(j+3).factorial:F)*(qm (j+3) U).eval x := by
    have ho: (G3^[j+3]) U =
        ((j+3).factorial:F[X])*qm (j+3) U:= by
      rw [← z6T,zqa,J4]
    simpa only [eval_mul,eval_ofNat,eval_natCast] using
      ov (Polynomial.eval x) ((bPp U j).trans ho)
  have hp:exponent - (2*j+1)+(2*j+1)=exponent:= by
    dsimp only [exponent] at *
    omega
  calc
    e (ayl f (j+3)) =
        s^(exponent - (2*j+1))*s^(2*j+1) *
          ((↑(j+3).factorial:F)⁻¹ *
            (2*((G3^[j + 1]) (qm 2 U)).eval x)) := by
      rw [ayl,lJ,qU,lJ,hscale,hc]
      ring
    _ = _:= by
      rw [← Et,hp,hderiv,← v9 ((↑(j+3).factorial:F)⁻¹),
        NI hfact,uh]
private theorem d1X (k :ao →+* F) (U:F[X]) (x :F)
   (f :af 3) (length:ℕ) (hL:length≤bf)
   (hU:U.natDegree<length) (hf :jW k U f=0) :
   (bCH f length).map (ee k x (rD x U)) =
     oY (ee k x (rD x U) (pU f)^exponent)*U:= by
 let e :=ee k x (rD x U)
 let s :=e (pU f)
 change (bCH f length).map e=oY (s^exponent)*U
 have hx :e (oq qJ)=x := by simp [e,ee]
 apply taylor_injective x
 rw [bCH,Polynomial.map_taylor,KA,hx,taylor_taylor,
   LQ,taylor_zero,Polynomial.map_sum,taylor_mul,taylor_C]
 simp only [map_monomial]
 have hdeg: (u9 x U).natDegree<length:= by rwa [NX]
 conv_rhs =>
   rw [Polynomial.as_sum_range' (u9 x U) length hdeg,← zdx]
 rw [zxw]
 refine sI rfl fun i _ => ?_
 rw [d1W k U x f hf _ (i.isLt.trans_le hL),Ob ,C_mul_monomial]
end Evaluation
theorem proof :ac1.c1 := by
 intro f
 refine ⟨exponent,fun a=>(bCH f bf).coeff a.val,?_⟩
 intro F _ k U x hU hf _ a
 have h:=ov (fun P:F[X]=>P.coeff a.val)
  (d1X k U x f bf zk hU hf)
 simpa only [Eg ,coeff_C_mul] using h.symm
end
end bam
end
section
namespace dnd
noncomputable section
open aR oR B7 ac1
open scoped Polynomial nonZeroDivisors
private abbrev Dual (B:Type*) :=TrivSqZeroExt B B
private def b1c {B:Type*} (a b:B) :Dual B:=(a,b)
private abbrev fstHom (B:Type*) [ox B] :Dual B →+* B :=
 (TrivSqZeroExt.fstHom B B B).toRingHom
private def b7y {A L B:Type*} [ox A] [uW A] [nX L] [nX B]
  [nI A L] [vj A L] (g:A →+* Dual B)
  (hg:th ((fstHom B).comp g)) :L →+* Dual B :=
 IsLocalization.lift (M:=A⁰) (g:=g) fun d =>
  TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr (by
    change ((fstHom B).comp g) (d:A)≠0
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp d.2) (hg (h.trans (qy _).symm))))
private theorem cXw {A L B:Type*} [ox A] [uW A] [nX L] [nX B]
  [nI A L] [vj A L] (g:A →+* Dual B)
  (hg:th ((fstHom B).comp g)) (a :A) :
  b7y (L:=L) g hg (aU A L a)=g a :=
 IsLocalization.lift_eq _ _
private def a6I {B:Type*} [ox B] (g:ao[X] →+* B) :ao[X] →+* Dual B where
 toFun p:=(g p,g p.derivative)
 map_zero' := by apply IU <;> simp
 map_one' := by apply IU <;> simp
 map_add' p q:= by
  apply IU
  · exact qz g p q
  · change g (p+q).derivative=g p.derivative+g q.derivative
    rw [qz ,qz]
 map_mul' p q:= by
  apply IU
  · exact lJ g p q
  · change g (p*q).derivative=g p*g q.derivative+g p.derivative*g q
    rw [Polynomial.derivative_mul,qz ,lJ,lJ,FU]
section Evaluation
variable {B:Type*} [nX B] (e :nW →+* B)
private abbrev adF:dF →+* B:=e.comp oq
private abbrev aG5:ao[X] →+* B :=
 (adF e).comp (aU ao[X] dF)
private abbrev Lz :af 3 →+* B:=e.comp Bu
private abbrev acj (i:Fin 3) :B:=e (lz i)
private def bCU:dF →+* Dual B :=
 b7y (A:=ao[X]) (L:=dF) (B:=B) (a6I (aG5 e))
  ((adF e).injective.comp (zm ao[X] dF))
private theorem bXB (p:ao[X]) :
  bCU e (aU ao[X] dF p)=a6I (aG5 e) p :=
 cXw _ _ _
private theorem dMc (a :dF) : (bCU e a).fst=adF e a := by
 have h: (fstHom B).comp (bCU e)=adF e := by
  apply zuW (ao[X]⁰)
  apply u5
  intro p
  exact ov TrivSqZeroExt.fst (bXB e p)
 exact vk h a
private def ahF (v :Fin 3→B) :nW →+* Dual B :=
 C5 (bCU e) (fun i=>b1c (acj e i) (v i))
private def rowJet (v :Fin 3→B) :af 3 →+* Dual B :=
 C5 (a6I (aG5 e)) (fun i=>b1c (acj e i) (v i))
private theorem b3W (v :Fin 3→B) (b:nW) :
    (ahF e v b).fst=e b:= by
  have h: (fstHom B).comp (ahF e v)=e := by
    apply yQ
    · intro a
      change (ahF e v (oq a)).fst= _
      simpa only [ahF,yL,adF,JM]
        using dMc e a
    · intro i
      change (ahF e v (lz i)).fst= _
      rw [ahF,G1]
      rfl
  exact vk h b
private theorem b3X (v :Fin 3→B) (b:af 3) :
    ahF e v (Bu b)=rowJet e v b:= by
  have h: (ahF e v).comp Bu=rowJet e v := by
    apply yQ
    · intro a
      simpa only [JM,Bu,zi ,ahF,rowJet,
        yL] using bXB e a
    · intro i
      simp [ahF,rowJet,Bu]
  exact vk h b
private theorem fY6 (v :Fin 3→B) (b:af 3) :
  (rowJet e v b).fst=Lz e b:= by
 rw [← b3X,b3W]
 rfl
@[simp] private theorem alJ (b:af 3) (m:Fin 3 →₀ ℕ) :
    (DU b).coeff m=(b.coeff m).derivative := by
  classical
  rw [DU,zqN]
  simp only [MvPolynomial.coeff_monomial,X4]
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,qy]
private theorem a2C (p:ao[X]) :
  DU (oq p:af 3)=oq p.derivative := by
 classical
 ext m
 by_cases h:0=m <;> simp [MvPolynomial.coeff_C,h]
private theorem a2D (b c:af 3) :
  DU (b+c)=DU b+DU c:= by
 ext m
 simp
private theorem bnc (b:af 3) (i:Fin 3) :
  DU (b*lz i)=DU b*lz i:= by
 classical
 ext m
 rw [alJ,z0S,z0S]
 split_ifs <;> simp
private theorem fY8 (v :Fin 3→B) (b:af 3) :
    (rowJet e v b).snd=Lz e (DU b) +
      ∑ i,v i*Lz e (Dw i b) := by
  classical
  let E :=Lz e
  let J:=rowJet e v
  change (J b).snd=E (DU b) + ∑ i,v i*E (Dw i b)
  induction b using EK with
  | C a =>
    simp [J,E,rowJet,Bu,a2C]
    rfl
  | add b c hb hc =>
    simp only [qz ,TrivSqZeroExt.snd_add,hb,hc,a2D,mul_add,
      PA]
    ring
  | mul_X b j hb =>
    have hJ:J (lz j)=b1c (acj e j) (v j) := by simp [J,rowJet]
    have hE :E (lz j)=acj e j:= by simp [E,Bu]
    rw [lJ,hJ,bnc,lJ,hE]
    change (J b).fst*v j+(J b).snd*acj e j= _
    rw [show (J b).fst=E b from fY6 e v b]
    simp only [hb,MvPolynomial.pderiv_mul,qz ,lJ,hE,mul_add,
      PA]
    have h₁: (∑ i,v i*(E (Dw i b)*acj e j)) =
        (∑ i,v i*E (Dw i b))*acj e j:= by
      simp only [Ye,v9]
    have h₂: (∑ i,v i*(E b*E (Dw i (lz j)))) =
        v j*E b:= by
      simp [MvPolynomial.pderiv_X,Pi.single_apply,mul_ite]
    rw [h₁,h₂]
    ring
variable (f :af 3)
private abbrev bh1 :B := -Lz e (D3 f)/Lz e (pU f)
private def yS:Fin 3→B := ![acj e 1, 2*acj e 2,bh1 e f]
private theorem c81 (b:af 3) :
   (rowJet e (yS e f) b).snd=Lz e (D3 b) +
     bh1 e f*Lz e (pU b) := by
 rw [fY8,Fin.sum_univ_three]
 simp [D3,pU,yS,Lz,Bu,Pj,add_assoc]
private theorem b9y (hs :Lz e (pU f)≠0) :
  Lz e (pU f)*bh1 e f = -Lz e (D3 f) := by
 rw [bh1,← mul_div_assoc,mul_div_cancel_left₀ _ hs]
private def cWE (I:lI nW) (hI:I=Jy f)
    (hz :Lz e f=0) (hs :Lz e (pU f)≠0) :
    nW ⧸ I →+* Dual B :=
  Ideal.Quotient.lift I (ahF e (yS e f)) (by
    intro b hb
    rw [hI] at hb
    have h:ahF e (yS e f) (GZ f)=0:= by
      apply IU
      · rw [b3W,TrivSqZeroExt.fst_zero]
        exact hz
      · change (ahF e (yS e f) (Bu f)).snd=0
        rw [b3X,c81,pz (bh1 e f),b9y e f hs,
          LQ]
    obtain ⟨g,rfl⟩:=Ideal.mem_span_singleton.mp hb
    rw [lJ,h,vh])
end Evaluation
section FractionField
variable {A B:Type*} [ox A] [uW A] [nX B] [nI A B] [vj A B]
private def arv (q:A →+* Dual B)
  (hq: (fstHom B).comp q=aU A B) :B →+* Dual B :=
 b7y (L:=B) q (by rw [hq]; exact zm A B)
private theorem cS0 (q:A →+* Dual B)
  (hq: (fstHom B).comp q=aU A B) (a :A) :
  arv q hq (aU A B a)=q a :=
 cXw _ _ _
private theorem cS1 (q:A →+* Dual B)
  (hq: (fstHom B).comp q=aU A B) (b:B) : (arv q hq b).fst=b:= by
 have h: (fstHom B).comp (arv q hq)=LO _:= by
  apply zuW (A⁰)
  apply u5
  intro a
  change (arv q hq (aU A B a)).fst= _
  rw [cS0]
  exact vk hq a
 exact vk h b
private def b3R (q:A →+* Dual B)
    (hq: (fstHom B).comp q=aU A B) :KH ℕ B B :=
  Derivation.mk'
    ((TrivSqZeroExt.sndHom (R:=B) (M:=B)).toAddMonoidHom.comp
      (arv q hq).toAddMonoidHom).toNatLinearMap (by
        intro a b
        change (arv q hq (a*b)).snd =
          a*(arv q hq b).snd+b*(arv q hq a).snd
        rw [lJ]
        change (arv q hq a).fst*(arv q hq b).snd +
          (arv q hq a).snd*(arv q hq b).fst= _
        rw [cS1,cS1,pz (arv q hq a).snd b])
private theorem edM (q:A →+* Dual B)
  (hq: (fstHom B).comp q=aU A B) (a :A) :
  b3R q hq (aU A B a)=(q a).snd:= by
 change (arv q hq (aU A B a)).snd= _
 rw [cS0]
end FractionField
section Descent
variable {A B:Type*} [ox A] [nX B] [nI A B]
private abbrev arw (q:nW →+* A) :nW →+* B :=
 (aU A B).comp q
private theorem cMH (q:nW →+* A) (f :af 3)
  (hk :vG q=Jy f) :Lz (arw (B:=B) q) f=0:= by
 have hm:GZ f∈vG q:= by
  rw [hk]
  exact Mj _
 change aU A B (q (GZ f))=0
 rw [RingHom.mem_ker.mp hm,qy]
private def bEb (q:nW →+* A) (f :af 3)
   (hq:vZ q) (hk :vG q=Jy f)
   (hs :Lz (arw (B:=B) q) (pU f)≠0) :A →+* Dual B :=
 (cWE (arw q) f (vG q) hk (cMH q f hk) hs).comp
   (q.quotientKerEquivOfSurjective hq).symm.toRingHom
private theorem cKC (q:nW →+* A) (f :af 3)
  (hq:vZ q) (hk :vG q=Jy f)
  (hs :Lz (arw (B:=B) q) (pU f)≠0) (b:nW) :
  bEb q f hq hk hs (q b)=ahF (arw q) (yS (arw q) f) b:= by
 change cWE (arw q) f _ hk (cMH q f hk) hs
  ((q.quotientKerEquivOfSurjective hq).symm (q b))= _
 rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
 rfl
private theorem dWy (q:nW →+* A) (f :af 3)
  (hq:vZ q) (hk :vG q=Jy f)
  (hs :Lz (arw (B:=B) q) (pU f)≠0) :
  (fstHom B).comp (bEb q f hq hk hs)=aU A B:= by
 apply u5
 intro a
 obtain ⟨b,rfl⟩:=hq a
 change (bEb q f hq hk hs (q b)).fst= _
 rw [cKC]
 exact b3W (arw q) (yS (arw q) f) b
private theorem cNv [uW A] [vj A B]
   (q:nW →+* A) (f :af 3)
   (hq:vZ q) (hk :vG q=Jy f)
   (hs :Lz (arw (B:=B) q) (pU f)≠0) :
   ∃ D:KH ℕ B B,∀ b:nW,
     D (arw q b)=(ahF (arw q) (yS (arw q) f) b).snd:= by
 refine ⟨b3R (bEb q f hq hk hs) (dWy q f hq hk hs),?_⟩
 intro b
 change b3R _ _ (aU A B (q b))= _
 rw [edM,cKC]
end Descent
section Cutoff
variable {B:Type*} [nX B] (e :nW →+* B) (f :af 3) (D:KH ℕ B B)
variable (hD : ∀ b:nW,D (e b)=(ahF e (yS e f) b).snd)
include hD in
private theorem boZ (p:ao[X]) :
  D (aG5 e p)=aG5 e p.derivative := by
 change D (e (oq (aU ao[X] dF p)))= _
 rw [hD,ahF,yL,bXB]
 rfl
include hD in
private theorem aUa (i:Fin 3) :D (acj e i)=yS e f i:= by
 change D (e (lz i))= _
 rw [hD,ahF,G1]
 rfl
include hD in
private theorem dWm (b:af 3) :
   D (Lz e b)=Lz e (D3 b) +
     bh1 e f*Lz e (pU b) := by
 change D (e (Bu b))= _
 rw [hD,b3X,c81]
variable (hs :Lz e (pU f)≠0)
include hD hs in
private theorem a3K (b:af 3) :
  Lz e (Ev f b)=Lz e (pU f)*D (Lz e b) := by
 rw [dWm e f D hD,mul_add,← v9,b9y e f hs]
 simp [Ev,pU,Vs]
private theorem bXl {F:Type*} [nX F] (δ:KH ℕ F F) (s z :F) (a :ℕ) :
   s*(s*δ (s^a*z))-(a :F)*(s^a*z)*(s*δ s) =
     s^(a+2)*δ z := by
 cases a with
 | zero=>simp [pow_two,mul_assoc]
 | succ a =>
   rw [δ.leibniz,δ.leibniz_pow,Et s (a+1) 2,pow_succ' s a]
   simp only [Nat.succ_sub_one,qG,J4 ,pow_two]
   ring
include hD hs in
private theorem b1O (n:ℕ) :
   Lz e (AR f n)=Lz e (pU f)^(2*n+1) *
    ((D:B→B)^[n + 1]) (acj e 2) := by
 induction n with
 | zero =>
   change Lz e (-D3 f)=Lz e (pU f)^1*D (acj e 2)
   rw [KA,pow_one,aUa e f D hD]
   exact (b9y e f hs).symm
 | succ n ih =>
   rw [AR]
   simp only [yU,lJ,Il,a3K e f D hD hs]
   rw [ih,show 2*(n+1)+1=(2*n+1)+2 by omega,
    zLk _ (n+1)]
   exact bXl _ _ _ _
include hD in
private theorem b6B (n:ℕ) :
   ((D:B→B)^[n+2]) (acj e 0) =
     2*((D:B→B)^[n]) (acj e 2) := by
 induction n with
 | zero =>
   change D (D (acj e 0))=2*acj e 2
   rw [aUa e f D hD,show yS e f 0=acj e 1 by rfl,aUa e f D hD]
   rfl
 | succ n ih =>
   rw [show n+1+2=(n+2)+1 by omega,Function.iterate_succ_apply',ih,
     zLk]
   simp only [two_mul,qz]
end Cutoff
end
end dnd
end
section
namespace dne
noncomputable section
open aR ac1 Polynomial
open scoped BigOperators Differential
variable {F:Type*} [nX F]
private theorem factorial_ne_zero [CharP F K1.p] {n:ℕ} (hn:n<K1.p) :
  (n.factorial:F)≠0:= by
 intro hz
 have hp:=zVj F K1.p (by decide)
 exact (GF hn) (hp.dvd_factorial.mp ((Xo F K1.p _).mp hz))
variable [zyu F]
private def avG (a :F) (n:ℕ) :F :=
 ((LR :F→F)^[n]) a/n.factorial
private theorem c1M [CharP F K1.p] (a :F) (n:ℕ) (hn:n+1<K1.p) :
  (avG a n)′ = ((n:F)+1)*avG a (n+1) := by
 let D:KH ℤ F F:=LR
 have hd:D (avG a n)=(n.factorial:F)⁻¹*D (((D:F→F)^[n]) a) :=
  D.leibniz_div_const _ (n.factorial:F) (D.map_natCast _)
 change D (avG a n)= _
 rw [hd,avG,zLk,
  zwO,SL,Nat.cast_succ]
 have hfac: (n.factorial:F)≠0:=factorial_ne_zero (by omega)
 have hs : (n:F)+1≠0:= by
  intro hz
  apply factorial_ne_zero (F:=F) hn
  rw [zwO,SL,Nat.cast_succ,hz,vh]
 field_simp [hfac,hs] <;> rfl
private def GV (L:ℕ) (a :F) :F[X] :=
 ∑ n∈Finset.range L,Kh n (avG a n)
private theorem bnk (L:ℕ) (a :F) (n:ℕ) :
  (GV L a).coeff n=if n<L then avG a n else 0:= by
 classical
 simp only [GV,OJ,coeff_monomial,X4 ,
  Finset.mem_range]
private theorem dVo {L:ℕ} (hL:0<L) (a :F) : (GV L a).natDegree<L:= by
 apply lt_of_le_of_lt _ (show L - 1<L by omega)
 apply zMZ
 intro n hn
 exact (natDegree_monomial_le _).trans (zxM (Finset.mem_range.mp hn))
private theorem eyP [CharP F K1.p] {L:ℕ} (hL:L<K1.p) (a :F)
   (hcut: ((LR :F→F)^[L]) a=0) :
   u8 (GV L a)=G3 (GV L a) := by
 ext n
 simp only [zyh,VO,bnk]
 by_cases hn:n+1<L
 · rw [ite_eq_left (show n<L by omega),ite_eq_left hn,
     c1M a n (hn.trans hL),pz ]
 · rw [Nr hn,vh]
   by_cases h:n<L
   · have he :n+1=L:= by omega
     have hz :avG a L=0:= by rw [avG,hcut,zero_div]
     rw [zYo h,c1M a n (by rwa [he]),he,hz,G0 ]
   · rw [Nr h,qy]
omit [zyu F] in
private theorem dso (x :F) (P:F[X]) :
  z8 (qJ - C x) P=u9 (-x) P:= by
 rw [taylor_apply,C_neg,← Vs ,Polynomial.aeval_def,Polynomial.comp,
  zrE]
private theorem eyQ (x :F) (hx :x′ = 1) (P:F[X])
  (hP:u8 P=G3 P) :
  u8 (u9 (-x) P)=0:= by
 let _:zyu F[X] :=⟨u8⟩
 let _:DifferentialAlgebra F F[X] :=⟨by
  intro a
  change u8 (C a)=C a′
  exact Differential.mapCoeffs_C a⟩
 have hshift: (qJ - C x :F[X])′ = -1 := by
  change u8 (qJ - C x) = -1
  simp [hx]
 rw [← dso]
 change (z8 (qJ - C x) P)′ = 0
 rw [zkK,hP,hshift,mul_neg_one,LQ]
private theorem cZe (k :ao →+* F) (hk : ∀ a :ao,(k a)′ = 0)
   {U:F[X]} (hU:u8 U=0) (f :af 3) :
   u8 (jW k U f)=0:= by
 have hcoeff (n:ℕ) : (U.coeff n)′ = 0:= by
   simpa only [zyh,z9] using
     ov (fun P:F[X]=>P.coeff n) hU
 have hj (i:Fin 3) :u8 (qm i.val U)=0:= by
   ext n
   simp [hasseDeriv_coeff,Ea ,qG,hcoeff]
 induction f using EK with
 | C P =>
   change u8 (C5 (P7 k) _ (oq P))=0
   rw [yL]
   ext n
   simp [hk]
 | add f g hf hg =>
   rw [qz ,qz ,hf,hg,zE]
 | mul_X f i hf =>
   have hXi:jW k U (lz i)=qm i.val U:= by
     simp [jW]
   rw [lJ,hXi,Ea ,hf,hj]
   simp
private theorem cMy [CharP F K1.p]
    (x :F) (hx :x′ = 1) (P:F[X]) (hP:P.natDegree<K1.p)
    (hconst:u8 P=0) (hroot :P.eval x=0) :P=0:= by
  suffices aux : ∀ n (Q:F[X]),Q.natDegree=n→Q.natDegree<K1.p →
      u8 Q=0→Q.eval x=0→Q=0 by
    exact aux P.natDegree P rfl hP hconst hroot
  intro n
  induction n using z0n with
  | h n ih =>
    intro Q hdeg hchar hQ hzero
    by_cases hn:n=0
    · rw [eq_C_of_natDegree_eq_zero (hdeg.trans hn),eval_C] at hzero
      rw [eq_C_of_natDegree_eq_zero (hdeg.trans hn),hzero,qy]
    have hlt:Q.derivative.natDegree<n:= by
      rw [← hdeg]
      exact natDegree_derivative_lt (fun h=>hn (hdeg.symm.trans h))
    have hnp:n<K1.p:=hdeg ▸ hchar
    have hderiv :Q.derivative.eval x=0:= by
      have he :=zkK x Q
      simpa only [z99,hQ,hzero,hx,qy ,eval_zero,Ee,C9,
        eq_comm] using he
    have hconstant:u8 Q.derivative=0:= by
      have hc (i:ℕ) : (Q.coeff i)′ = 0:= by
        simpa only [zyh,z9] using
          ov (fun A:F[X]=>A.coeff i) hQ
      ext i
      simp [VO,Ea ,qG,hc]
    have hz :=ih _ hlt _ rfl (hlt.trans hnp) hconstant hderiv
    have hcast: (n:F)≠0:= by
      intro h
      exact (GF hnp)
        (Nat.le_of_dvd (zOl hn) ((Xo F K1.p _).mp h))
    have htop:=ov (fun A:F[X]=>A.coeff (n - 1)) hz
    have hn' : n - 1+1=n:=G6 (zOl hn)
    have hcast' : ((n - 1 :ℕ) :F)+1=(n:F) := by
      simpa only [Mk,G7] using ov (fun j:ℕ=>(j:F)) hn'
    rw [VO,hcast',hn',z9] at htop
    have hleading:Q.leadingCoeff=0:= by
      rw [SM,hdeg]
      exact (mul_eq_zero.mp htop).resolve_right hcast
    exact leadingCoeff_eq_zero.mp hleading
private theorem Uj [CharP F K1.p] {L:ℕ} (hL:3≤L) (hchar :L<K1.p)
   (x :F) (y :Fin 3→F) (hx :x′ = 1) (hval : (y 0)′ = y 1)
   (hfirst: (y 1)′ = 2*y 2) (hcut: ((LR :F→F)^[L]) (y 0)=0) :
   ∃ U:F[X],U.natDegree<L∧u8 U=0∧rD x U=y := by
 let U:=u9 (-x) (GV L (y 0))
 have hU:U.natDegree<L:= by
   rw [show U=u9 (-x) (GV L (y 0)) from rfl,NX]
   exact dVo (by omega) _
 have hc:u8 U=0 :=
   eyQ x hx _ (eyP hchar _ hcut)
 refine ⟨U,hU,hc,?_⟩
 funext i
 have hi:i.val<L:=i.isLt.trans_le hL
 rw [rD,← Ob ,show U=u9 (-x) (GV L (y 0)) from rfl,
   taylor_taylor,LQ,taylor_zero,bnk,zYo hi]
 fin_cases i
 · simp [avG]
 · simpa [avG] using hval
 · change avG (y 0) 2=y 2
   rw [avG,zLk,Function.iterate_one,hval,hfirst]
   have htwo: (2 :F)≠0:= by
     have h2 :=factorial_ne_zero (F:=F) (n:=2) (by decide)
     norm_num at h2
     exact h2
   norm_num
   exact (div_eq_iff htwo).2 (pz _ _)
end
end dne
end
section
namespace dnl
noncomputable section
open cu gT pI Ty Polynomial
open scoped Classical
private abbrev Variables :=oD (oD (Fin 2))
private abbrev Flat :=cy Variables FX
private def unflatten:Flat ≃+* Jet :=
 (p5 FX (oD (Fin 2))).toRingEquiv.trans
   (Polynomial.mapEquiv (p5 FX (Fin 2)).toRingEquiv)
private theorem cuq (q:Flat) :
    unflatten q =
      (p5 FX (oD (Fin 2)) q).map
        (p5 FX (Fin 2)).toRingHom:=rfl
private theorem cSJ (P:Jet) (j i:ℕ) (d:Fin 2 →₀ ℕ) :
   (unflatten.symm P).coeff ((d.optionElim i).optionElim j) =
     ((P.coeff j).coeff i).coeff d:= by
 have h:=ov (fun Q:Jet=>((Q.coeff j).coeff i).coeff d)
   (unflatten.apply_symm_apply P)
 rw [cuq,Eg] at h
 change (((p5 FX (Fin 2)
   ((p5 FX (oD (Fin 2)) (unflatten.symm P)).coeff j)).coeff i).coeff d)
   = _ at h
 rw [z9x,z9x] at h
 exact h
private def aue :Fin 4 ≃ Variables :=
 finSuccEquivLast.trans (Equiv.optionCongr wB)
private def aqH :Ambient ≃+* Jet :=
 (Vl FX aue).toRingEquiv.trans unflatten
private theorem bOX:iJ=aqH.symm.toRingHom:= by
  have h:iJ.comp aqH.toRingHom=LO Ambient:= by
    apply yQ
    · intro a
      change iJ (unflatten (t3 aue (oq a)))= _
      simp [cuq,iJ,A7,oi,pZ]
    · intro k
      change iJ (unflatten (t3 aue (lz k)))= _
      have hseed (i:Fin 2) :aue i.castSucc.castSucc=some (some i) := by
        unfold aue
        rw [Vq,VS]
        change some (wB i.castSucc)= _
        rw [VS]
      have h0:aue 0=some (some 0) :=hseed 0
      have h1 :aue 1=some (some 1) :=hseed 1
      have h2 :aue 2=some none := by
        change aue (Sd 2).castSucc= _
        unfold aue
        rw [Vq,VS]
        change some (wB (Sd 2))= _
        rw [S1]
      have h3:aue 3=none := by
        change aue (Sd 3)= _
        unfold aue
        rw [Vq,S1]
        rfl
      fin_cases k <;>
        simp [cuq,h0,h1,h2,h3,iJ,A7,oi,pZ]
  apply u5
  intro P
  have hp:=Kv h (aqH.symm P)
  change iJ (aqH (aqH.symm P))=aqH.symm P at hp
  rwa [RingEquiv.apply_symm_apply] at hp
private def kO:Variables→ℕ:= fun o=>o.elim 1 (fun a=>a.elim 1 fun _=>0)
private def Tl:Variables→ℕ:= fun o=>o.elim 0 (fun a=>a.elim 0 fun _=>1)
private theorem ep2 (j i:ℕ) (d:Fin 2 →₀ ℕ) :
  ((d.optionElim i).optionElim j).weight kO=i+j:= by
 unfold kO
 rw [WX ,Finsupp.weight_elim_one_zero,
  z6S,uh,Nat.add_comm]
private theorem goI (j i:ℕ) (d:Fin 2 →₀ ℕ) :
  ((d.optionElim i).optionElim j).weight Tl=d.degree := by
 unfold Tl
 rw [WX ,WX ,
  vh,C9,vh,C9,← Finsupp.degree_eq_weight_one]
private def asb (weight:Variables→ℕ) (P:Jet) :ℕ :=
 (unflatten.symm P).weightedTotalDegree weight
private theorem c80 (weight:Variables→ℕ) {P Q:Jet}
   (hP:P≠0) (hQ:Q≠0) :
   asb weight (P*Q)=asb weight P+asb weight Q:= by
 unfold asb
 rw [lJ,MvPolynomial.weightedTotalDegree_mul]
 · simpa using hP
 · simpa using hQ
private theorem c8Z (weight:Variables→ℕ) (P:Jet) (n:ℕ) :
    asb weight P≤n ↔
      ∀ j i (d:Fin 2 →₀ ℕ),((P.coeff j).coeff i).coeff d≠0 →
        ((d.optionElim i).optionElim j).weight weight≤n:= by
  rw [asb,MvPolynomial.weightedTotalDegree,zUp]
  constructor
  · intro h j i d hd
    apply h
    exact MvPolynomial.mem_support_iff.mpr (by rwa [cSJ])
  · intro h e he
    have heq : (e.some.some.optionElim (e.some none)).optionElim (e none)=e := by
      rw [zX5,zX5]
    rw [← heq]
    exact h _ _ _ (by rw [← cSJ,heq]; exact MvPolynomial.mem_support_iff.mp he)
private theorem b6G (P:Jet) (b:ℕ) :
   asb kO P≤b ↔
     ∀ j i,(P.coeff j).coeff i≠0→i+j≤b:= by
 rw [c8Z]
 simp only [ep2]
 constructor
 · intro h j i hji
   obtain ⟨d,hd⟩:=Finset.nonempty_iff_ne_empty.mpr
     (fun hz=>hji (MvPolynomial.support_eq_empty.mp hz))
   exact h j i d (MvPolynomial.mem_support_iff.mp hd)
 · intro h j i d hd
   exact h j i (fun hz=>hd (by simp [hz]))
private theorem Qc (P:Jet) (u:ℕ) :
  asb Tl P≤u ↔ ∀ j i,((P.coeff j).coeff i).totalDegree≤u:= by
 rw [c8Z]
 simp only [goI,MvPolynomial.totalDegree,zUp,
  zuk]
 exact ⟨fun h j i d hd=>h j i d hd,fun h j i d hd=>h j i d hd⟩
private theorem eHH {H :Equation} (hH :H≠0) :
   H.natDegree≤asb kO (C H) ∧
    gY H≤asb Tl (C H) := by
 constructor
 · have htop:H.coeff H.natDegree≠0:= by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hH
   simpa using (b6G _ _).mp zk 0 H.natDegree (by simpa using htop)
 · apply Pv
   intro i _
   simpa using (Qc (C H) _).mp zk 0 i
private theorem aUy {P D T:Jet} {H :Equation} {s :Shape}
   (hP:P≠0) (hH :H≠0) (hcap:oU P s)
   (hf :P=D *(C H*T)) :
   gY H≤ s.U∧H.natDegree≤ s.B ∧
     oU T (aea s (gY H) H.natDegree) := by
 have hprod:D *(C H*T)≠0:= by rw [← hf]; exact hP
 have hD:=SW hprod
 have hCT:=Vz hprod
 have hC:=SW hCT
 have hT:=Vz hCT
 have hB:asb kO P≤ s.B :=
   (b6G _ _).mpr fun j i h=>(hcap j i h).1
 have hU:asb Tl P≤ s.U:=(Qc _ _).mpr fun j i=> by
   by_cases h: (P.coeff j).coeff i=0
   · simp [h]
   · exact (hcap j i h).2.2
 have hJ:P.natDegree≤ s.J:= by
   have hp:P.coeff P.natDegree≠0:= by
     rw [coeff_natDegree]
     exact leadingCoeff_ne_zero.mpr hP
   obtain ⟨i,hi⟩:=support_nonempty.mpr hp
   exact (hcap _ i (mem_support_iff.mp hi)).2.1
 rw [hf,c80 _ hD hCT,c80 _ hC hT] at hB hU
 rw [hf,natDegree_mul hD hCT,natDegree_mul hC hT] at hJ
 obtain ⟨hOrd,hSeed⟩:=eHH hH
 refine ⟨by omega,by omega,?_⟩
 have hbT:asb kO T≤ s.B - H.natDegree := by omega
 have huT:asb Tl T≤ s.U - gY H := by omega
 intro j i hij
 have hb:=(b6G T _).mp hbT j i hij
 have hu:=(Qc T _).mp huT j i
 have hjT:=le_natDegree_of_ne_zero (show T.coeff j≠0 from fun hz=>hij (by simp [hz]))
 exact ⟨hb,Nat.le_min.mpr ⟨by omega,by omega⟩,hu⟩
private theorem c1e (D:Jet)
   (h : ∀ G:Jet,Irreducible G→G∣D→G.natDegree=0) :D.natDegree=0:= by
 induction D using WfDvdMonoid.induction_on_irreducible with
 | zero=>exact natDegree_zero
 | unit D hD =>exact natDegree_eq_zero_of_isUnit hD
 | mul Q G hQ hG ih =>
   rw [natDegree_mul hG.ne_zero hQ,h G hG (dvd_mul_right _ _),
     ih (fun F hF hd=>h F hF (zfC hd G)),C9]
private theorem b1e {P F:Jet} {s :Shape} (A:NO P s)
  (h:F∣A.residual) :F∣P :=
 calc
  F∣Gw A.equation*A.residual :=
    zfC (α:=Jet) h (Gw A.equation)
  _=P:=A.factorization.symm
end
end dnl
end
section
set_option backward.isDefEq.respectTransparency false
namespace axk
noncomputable section
open E7 (poleOrder)
open agN (bGE a6F)

open aeF (FZ ajJ Os toFunction)
open XX (OG EO bdy ach ad4 aFr)
open scoped BigOperators Polynomial WithZero
def c1 :Prop :=
  ∀ (k F:Type) [nX k] [nX F] [nI k F] (x :F),
    Yo k x→qx (Ef k {x}) F →
      qx k[X] (ach (k :=k) x)
def c2 :Prop :=XX.c2
def c3:Prop :=XX.c4
def c4 :Prop :=XX.c5
section Poles
variable {k F:Type} [nX k] [nX F] [nI k F]
private theorem ccb:Monotone (fun a :ℤᵐ⁰=>(WithZero.log a).toNat) := by
 intro a b hab
 by_cases ha :a=0
 · simp [ha]
 · exact Int.toNat_le_toNat ((WithZero.log_le_log ha
    (ne_of_gt ((WithZero.pos_iff_ne_zero.mpr ha).trans_le hab))).mpr hab)
private theorem pole_add (p:pG k F) (a b:F) :
   pL p.value (a+b)≤ max (pL p.value a) (pL p.value b) :=
 (ccb (p.value.map_add a b)).trans ccb.map_max.le
private theorem pole_mul (p:pG k F) (a b:F) :
   pL p.value (a*b)≤pL p.value a+poleOrder p.value b:= by
 unfold pL
 obtain rfl | ha :=G8 a 0
 · simp
 obtain rfl | hb:=G8 b 0
 · simp
 rw [lJ,WithZero.log_mul (by simpa using ha) (by simpa using hb)]
 omega
private theorem pole_scalar (p:pG k F) (a :k) :
   pL p.value (aU k F a)=0:= by
 obtain rfl | ha :=G8 a 0
 · simp [pL]
 · simp [pL,p.on_constants a ha]
private theorem eMN (p:pG k F) {x :F} (hx :Z0 k x) :
   pL p.value x=0:= by
 let:p.value.IsTrivialOn k :=⟨p.on_constants⟩
 obtain rfl | hx0:=G8 x 0
 · simp [pL]
 · have hv :p.value x=1 := by
     by_contra h
     exact (Valuation.transcendental_of_ne_one k x hx0 h) hx
   simp [pL,hv]
private theorem poles_and_degree (h1 :c1) (h2 :c2) (hF:Mw k F) (x :F) :
    (fun p:pG k F=>pL p.value x).HasFiniteSupport ∧
      (∀ p:pG k F,pL p.value x≠0 →
        NW k (EO p)) ∧
      aFr (k :=k) x=FZ k x := by
  by_cases hx :Z0 k x
  · have hp : ∀ p:pG k F,pL p.value x=0 :=
      fun p=>eMN p hx
    refine ⟨?_,fun p h=>(h (hp p)).elim,?_⟩
    · simp [Function.HasFiniteSupport,N0 ,hp]
    · simp [aFr,FZ,hx,hp]
  · have hfinite :=bGE hF hx
    exact h2 k F x hx hfinite (h1 k F x hx hfinite)
private theorem bu6 (h1 :c1) (h2 :c2) (hF:Mw k F) (p:pG k F) :
  NW k (EO p) := by
 obtain ⟨a,ha⟩:=p.normalized (WithZero.exp 1)
 have h:pL p.value a≠0:= by simp [pL,ha]
 exact (poles_and_degree h1 h2 hF a).2.1 p h
end Poles
section Pencil
variable {k F:Type} [nX k] [nX F] [nI k F]
local instance :nI (t9 k) (t9 F) :=Os k (F:=F)
private theorem bqw {p:pG k F} {q:pG (t9 k) (t9 F)}
   (h:OG p q) (x :F) :q.value (RatFunc.C x)=p.value x := by
 obtain rfl | hx :=G8 x 0
 · simp
 · simpa [Polynomial.support_C hx] using h (oY x)
private theorem btE {p q:pG k F} (h:p.value=q.value) :p=q:= by
 cases p
 cases q
 cases h
 rfl
private theorem b4w {p:pG k F} {q r :pG (t9 k) (t9 F)}
   (hq:OG p q) (hr :OG p r) :q=r := by
 apply btE
 apply Valuation.ext
 intro a
 induction a using RatFunc.induction_on with
 | _ P Q hQ=>rw [q.value.map_div,r.value.map_div,hq P,hq Q,hr P,hr Q]
private def qW (x y :F) :t9 F:=RatFunc.C x+RatFunc.X*RatFunc.C y
private theorem b4v {p:pG k F} {q:pG (t9 k) (t9 F)}
    (h:OG p q) (x y :F) :
    pL q.value (qW x y)=max (pL p.value x) (pL p.value y) := by
  let P:F[X] :=oY x+Polynomial.X*oY y
  have hP:aU F[X] (t9 F) P=qW x y := by
    simp only [P,qW,qz ,lJ,RatFunc.algebraMap_C,zYR]
  have hc0:P.coeff 0=x := by simp [P]
  have hc1 :P.coeff 1=y := by simp [P]
  have hrest (i:ℕ) (hi:2≤ i) :P.coeff i=0:= by
    obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hi
    simp [P,FU]
  have hmax :P.support.sup (fun i=>p.value (P.coeff i))=max (p.value x) (p.value y) := by
    apply zd
    · apply Pv
      intro i _
      by_cases h0:i=0
      · simp [h0,hc0]
      by_cases h1 :i=1
      · simp [h1,hc1]
      · simp [hrest i (by omega)]
    · have hcoeff (i:ℕ) :p.value (P.coeff i)≤P.support.sup (fun j=>p.value (P.coeff j)) := by
        by_cases hi:P.coeff i=0
        · simp [hi]
        · exact Xx (f := fun j=>p.value (P.coeff j))
            (Polynomial.mem_support_iff.mpr hi)
      exact max_le (hc0 ▸ hcoeff 0) (hc1 ▸ hcoeff 1)
  unfold pL
  rw [← hP,h P,hmax,ccb.map_max]
private theorem pencil_pole_degree (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (hF:Mw k F) (x y :F) :
    (∑ᶠ p:pG k F,ze p*max (pL p.value x) (pL p.value y)) =
      ajJ k x y := by
  classical
  let lift (p:pG k F) :=(bdy p).choose
  have hlift (p:pG k F) :OG p (lift p) :=(bdy p).choose_spec
  have hinj:th lift:= by
    intro p r he
    apply btE
    apply Valuation.ext
    intro a
    rw [← bqw (hlift p),← bqw (hlift r),he]
  let g (q:pG (t9 k) (t9 F)) :=ze q*pL q.value (qW x y)
  have hsupp:N0 g⊆oK lift:= by
    intro q hq
    rcases h4 k F (bu6 h1 h2 hF) q with htriv | ⟨p,hp⟩
    · have halg:aU (t9 k) (t9 F) RatFunc.X=RatFunc.X:= by
        simpa only [Polynomial.map_X,zYR] using
          (ad4 (k :=k) (F:=F) qJ)
      have hX:q.value (RatFunc.X:t9 F)=1 := by
        rw [← halg]
        exact q.on_constants _ RatFunc.X_ne_zero
      have hle :q.value (qW x y)≤1 := by
        unfold qW
        apply (q.value.map_add _ _).trans
        rw [lJ,hX,uh]
        exact max_le (htriv x) (htriv y)
      exact (hq (by simp [g,(a6F _ _).2 hle])).elim
    · exact ⟨p,b4w (hlift p) hp⟩
  have hsum: (∑ᶠ q,g q) = ∑ᶠ q∈oK lift,g q:= by
    rw [← finsum_mem_support g]
    apply zJX
    intro q hq
    simp [hq,hsupp hq]
  calc
    _ = ∑ᶠ p,g (lift p) := by
      apply finsum_congr
      intro p
      simp only [g,b4v (hlift p),h3 k F p (bu6 h1 h2 hF p) _ (hlift p)]
    _ = ∑ᶠ q∈oK lift,g q:=(finsum_mem_range hinj).symm
    _=aFr (k :=t9 k) (qW x y) :=hsum.symm
    _=ajJ k x y :=(poles_and_degree h1 h2 (eKW hF) _).2.2
end Pencil
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :K1_14_2_2_7_3_3.c1 := by
  classical
  intro k A _ _ _ _ hft hdim x y
  let F:=t4 A
  have hF:Mw k F:=affine_curve_field hdim
  let order (p:pG k F) (a :A) :=pL p.value (yJ a)
  have hdegree (a :A) :=poles_and_degree h1 h2 hF (yJ a)
  obtain ⟨T,hT⟩:=hft.out
  let E :Set (pG k F) := ⋃ a : ↥T,N0 (fun p=>order p a.1)
  have hE :E.Finite :=Set.finite_iUnion fun a : ↥T=>(hdegree a.1).1
  let S:=hE.toFinset
  have hz (p:pG k F) (hp:p∉S) (a :A) :order p a=0:= by
    have ha :a∈Algebra.adjoin k (↑T:Set A) := by rw [hT]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem b hb =>
      by_contra hne
      apply hp
      exact hE.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨⟨b,hb⟩,hne⟩)
    | algebraMap c =>
      simpa [order,yJ,t8 k A F] using
        pole_scalar (F:=F) p c
    | add a b _ _ ha hb =>
      exact Nat.eq_zero_of_le_zero (by simpa [order,toFunction,ha,hb] using
        (pole_add p (yJ  a) (yJ  b)).trans (show
          max (order p a) (order p b)≤0 by simp [ha,hb]))
    | mul a b _ _ ha hb =>
      exact Nat.eq_zero_of_le_zero (by simpa [order,toFunction,ha,hb] using
        (pole_mul p (yJ  a) (yJ  b)).trans (show
          order p a+order p b≤0 by simp [ha,hb]))
  let e :=S.equivFin.symm
  have hsum (g:pG k F→ℕ) (hg : ∀ p∉S,g p=0) :
      (∑ i,g (e i)) = ∑ᶠ p,g p:= by
    rw [e.sum_comp (fun p:S=>g p),Finset.sum_coe_sort]
    exact (finsum_eq_finsetSum_of_support_subset _ (fun p hp=> by
      by_contra h
      exact hp (hg p h))).symm
  refine ⟨{
    places :=S.card
    order := fun i=>order (e i)
    weight:= fun i=>ze (e i:pG k F)
    scalar := fun i c=> by
      simpa [order,yJ,t8 k A F] using
        pole_scalar (F:=F) (e i) c
    add:= fun i a b=> by simpa [order,yJ] using pole_add (e i:pG k F) (yJ a) (yJ b)
    mul := fun i a b=> by simpa [order,yJ] using pole_mul (e i:pG k F) (yJ a) (yJ b)
    degree_eq := fun a=>(hsum (fun p=>ze p*order p a)
      (fun p hp=> by simp [hz p hp a])).trans (hdegree a).2.2
    pencil_eq := ?_ }⟩
  exact (hsum (fun p=>ze p*max (order p x) (order p y))
    (fun p hp=> by simp [hz p hp x,hz p hp y])).trans
      (pencil_pole_degree h1 h2 h3 h4 hF _ _)
end
end axk
end
section
namespace czd
open XX (adp)
open aKx (adjoin_inv b29 bqn bql
 cch)
open scoped Polynomial
theorem proof :axk.c1 := by
 intro k F _ _ _ x hx hfinite
 have hxi:Yo k x⁻¹:= fun h=>hx (IsAlgebraic.inv_iff.mp h)
 let K:=Ef k ({x⁻¹} : Set F)
 let:nI k[X] F:=adp x⁻¹
 let:nI k[X] K:=bql x⁻¹ hxi
 have :vj k[X] K:=(bqn hxi).1
 have :sH k[X] K F:=(bqn hxi).2
 have :qx K F:= by
  change qx (Ef k ({x⁻¹} : Set F)) F
  rwa [adjoin_inv]
 exact b29 k[X] K F (cch k)
end czd
end
section
namespace czf
theorem proof :axk.c3 :=
 bRM.proof
end czf
end
section
namespace aA3
noncomputable section
open aR oR we aiJ
open scoped Polynomial
def point (a :GD) :mK →+* dF :=
 vi fun j=>aU cH dF (a j)
theorem c4l (a :GD) (i:Fin bf) :
  point a (lz i)=aU cH dF (a i) :=
 wY i
theorem c4k (a :GD) (c:dF) :
  point a (oq c)=c :=
 yl c
def bQx (f :af 3) (S:cH[X]) :Prop :=
  ∀ k :ℕ,k+3≤bf →
    2*Of (AR f k) S =
      Of (pU f) S^(2*k+1) *
        (((k+3).factorial:cH[X])*qm (k+3) S)
end
end aA3
end
section
namespace aA3
noncomputable section
open aR oR we aiJ Polynomial
open scoped BigOperators
private abbrev incl:cH[X] →+* dF:=aU _ _
theorem bnu (a :GD) :
  (JC a).natDegree<bf := by
 apply TZ
 apply zMZ
 intro j _
 exact (natDegree_monomial_le _).trans (zxM j.isLt)
private def azQ {n:ℕ} (a :Fin n→cH) :cH[X] :=
 ∑ j:Fin n,Kh j.val (a j)
private theorem cb2 {n:ℕ} (a :Fin n→cH) (i:Fin n) :
   (azQ a).coeff i.val=a i:= by
 classical
 rw [azQ,OJ,Qw i]
 · exact coeff_monomial_same _ _
 · intro j _ h
   exact coeff_monomial_of_ne _ (fun e=>h (Fin.ext e.symm))
 · simp
private theorem eMh (a :GD) :
 azQ (n:=bf) a=JC a :=rfl
def yZ (a :GD) :nW →+* dF :=
 (point a).comp tO.toRingHom
theorem btJ (a :GD) (b:nW) :
 point a (tO b)=yZ a b:=rfl
private theorem bFq (a :GD) (i:Fin 3) :
  yZ a (lz i)=incl (qm i.val (JC a)) := by
 change point a (p7 _ (lz i))= _
 rw [wR]
 simp only [B7.KT,JC,pC]
 refine sI rfl fun j _ => ?_
 rw [hasseDeriv_monomial,← C_mul_X_pow_eq_monomial]
 simp only [lJ,c4k,c4l,adE,qU]
 rw [← zrE,← t8 cH cH[X] dF]
 simp only [Il]
 ac_rfl
private theorem b1U (a :GD) (c:dF) :
  yZ a (oq c)=c:= by
 change point a (p7 _ (oq c))= _
 rw [Gi ,zKm,c4k]
theorem aHI (a :GD) (P:af 3) :
   yZ a (GZ P)=incl (Of P (JC a)) := by
 unfold GZ Of
 rw [znM]
 change (yZ a |>.comp (mD a4j)) P =
   (incl.comp (C5 (P7 (aU ao cH))
     (fun j:Fin 3=>qm j.val (JC a)))) P
 apply vk
 apply yQ
 · intro p
   simp only [JM,zi ,yL,
     b1U,a4j,Polynomial.coe_mapRingHom]
 · intro i
   simp only [JM,zS ,G1 ,bFq]
private theorem factorial_ne_zero {n:ℕ} (h:n<K1.p) :
  (n.factorial:dF)≠0:= by
 let g:K1.K →+* dF:=(aU ao dF).comp embed
 intro hz
 have hK: (n.factorial:K1.K)=0 :=
  g.injective (by simpa only [Il,qy] using hz)
 have hp:=zVj K1.K K1.p (by decide)
 exact (GF h) (hp.dvd_factorial.mp ((Xo K1.K K1.p _).mp hK))
private abbrev exponent:ℕ:=2*bf
def apq (f :af 3) :nW:=GZ (pU f)
private def bf5 (f :af 3) :ℕ→nW
 | 0=>apq f^exponent*MvPolynomial.X 0
 | 1=>apq f^exponent*MvPolynomial.X 1
 | 2=>apq f^exponent*MvPolynomial.X 2
 | k+3=>MvPolynomial.C (2/((k+3).factorial:dF)) *
     apq f^(exponent - (2*k+1))*GZ (AR f k)
private theorem d2H (f :af 3) (a :GD)
   (hrec:bQx f (JC a))
   (j:ℕ) (hj:j<bf) :
   yZ a (bf5 f j) =
     yZ a (apq f)^exponent*incl (qm j (JC a)) := by
 rcases j with _ | _ | _ | k
 · simp only [bf5,lJ,qU,bFq]
   rfl
 · simp only [bf5,lJ,qU,bFq]
   rfl
 · simp only [bf5,lJ,qU,bFq]
   rfl
 let s :=yZ a (apq f)
 let y :=incl (qm (k+3) (JC a))
 let u:=yZ a (GZ (AR f k))
 let c:dF:=(k+3).factorial
 have he :2*u=s^(2*k+1)*(c*y) := by
   have h:=ov incl (hrec k (Nat.le_of_lt hj))
   simpa only [lJ,qU,Pj,Il,← aHI,u,s,y,c,apq] using h
 have hc:c≠0:=factorial_ne_zero (hj.trans (by decide :bf<K1.p))
 have hk :2*k+1≤exponent:= by
   change 2*k+1≤2*bf
   omega
 simp only [bf5,lJ,qU,b1U]
 change 2/ c*s^(exponent - (2*k+1))*u=s^exponent*y
 rw [div_eq_mul_inv]
 calc
   _=(s^(exponent - (2*k+1))*c⁻¹)*(2*u) := by ac_rfl
   _=(s^(exponent - (2*k+1))*s^(2*k+1))*(c⁻¹*c)*y := by
     rw [he]
     ac_rfl
   _ = _:= by rw [← Et,G6 hk,NI hc,Ee]
private theorem eef (S:cH[X]) (j:ℕ) :
   (u9 adE (S.map (aU cH dF))).coeff j =
     incl (qm j S) := by
 rw [Ob ,Zt,zhI]
 have h:Polynomial.eval₂RingHom (aU cH dF) adE=incl:= by
   apply z86
   · intro a
     rw [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
     exact t8 cH cH[X] dF a
   · exact Polynomial.eval₂_X _ _
 exact vk h _
private def weight (j i:ℕ) :dF :=
 ((qJ-Polynomial.C adE)^j).coeff i
private theorem eo9 (S:cH[X]) (m i:ℕ) (hS:S.natDegree< m) :
    (∑ j:Fin m,weight j.val i*incl (qm j.val S)) =
      aU cH dF (S.coeff i) := by
  let P:=S.map (aU cH dF)
  have hn: (u9 adE P).natDegree< m:= by
    rw [NX]
    exact Polynomial.natDegree_map_le.trans_lt hS
  have hsum: (∑ j:Fin m,oY ((u9 adE P).coeff j.val) *
      (qJ-Polynomial.C adE)^j.val)=P :=
    (Polynomial.sum_fin (fun j (c:dF) =>
      oY c*(qJ-Polynomial.C adE)^j)
      (fun _=> by rw [Polynomial.C_0,vh])
      (Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hn))).trans
      (Polynomial.sum_taylor_eq P adE)
  calc
    _ = ∑ j:Fin m,(oY ((u9 adE P).coeff j.val) *
        (qJ-Polynomial.C adE)^j.val).coeff i:= by
      refine sI rfl fun j _ => ?_
      rw [weight,coeff_C_mul,show (u9 adE P).coeff j.val =
        incl (qm j.val S) from eef _ _,pz]
    _=P.coeff i:= by rw [← OJ,hsum]
    _ = _:=Eg _ _
private theorem b6w (a :GD) (i:Fin bf) :
    (∑ j:Fin bf,weight j.val i.val*incl (qm j.val (JC a))) =
      aU cH dF (a i) :=
  (eo9 _ bf i.val (bnu a)).trans
    (ov (aU cH dF)
      ((ov (fun p:cH[X]=>p.coeff i.val) (eMh a).symm).trans
        (cb2 (n:=bf) a i)))
def VT (f :af 3) (i:Fin bf) :nW :=
 ∑ j:Fin bf,oq (weight j.val i.val)*bf5 f j.val
private theorem eMw (a :GD) (i:Fin bf)
   (b u:nW) (n:ℕ) :
   point a (lz i*tO b^n - tO u) =
     aU cH dF (a i)*yZ a b^n - yZ a u:= by
 rw [yU,lJ,c4l,qU,btJ,btJ]
theorem fUY (f :af 3) (a :GD) (i:Fin bf)
   (hrec:bQx f (JC a)) :
   point a (lz i*tO (apq f)^(2*bf) -
     tO (VT f i))=0:= by
 rw [eMw,HZ,VT,pC,← b6w a i,Ye]
 refine sI rfl fun j _ => ?_
 rw [lJ,b1U,d2H f a hrec j.val j.isLt]
 exact (v9 _ _ _).trans (ov (fun z=>weight j.val i.val*z) (pz _ _))
end
end aA3
end
section
namespace aA3
noncomputable section
open aR oR we aiJ
open scoped Polynomial
def c1 :Prop :=
  ∀ Q:Bk,Q.IsPrime →
    (gN Q).IsPrime ∧
      ∀ b:mK,b∈gN Q ↔
        ∀ a∈oj cH Q,point a b=0
def c2 :Prop :=
  ∀ (f :af 3) (S:cH[X]),S.natDegree<bf →
    Of f S=0→bQx f S
private theorem cNT (base :c1) {Q:Bk} (hQ:Q.IsPrime) :
    (gN Q).comap (mD (aU cH dF))= Q:= by
  let _:=hQ
  ext p
  rw [Ts ,(base Q hQ).2]
  have h (a :GD) :
      point a (mD (aU cH dF) p) =
        aU cH dF (vi a p) :=
    (zsn (aU cH dF) a p).symm
  simp only [h,map_eq_zero_iff _ (aU cH dF).injective]
  change p∈Bf cH (oj cH Q)↔p∈Q
  rw [Iw]
private theorem d2c (rec:c2) (f :af 3) (S:cH[X])
   (hS:S.natDegree<bf) (hf :Of f S=0)
   (k :ℕ) (hk :k+3=bf) :
   Of (AR f k) S=0:= by
 have h:=rec f S hS hf k hk.le
 have hd:S.natDegree<k+3:=hk.symm ▸ hS
 rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree S (k+3) hd,G0 ,G0] at h
 have htwo: (2 :cH[X])≠0:= by
   let g:K1.K →+* cH[X] :=
     Polynomial.C.comp ((aU ao cH).comp embed)
   have hne : (2 :K1.K)≠0:= by decide
   exact fun hz=>hne (g.injective (by simpa only [Pj,qy] using hz))
 exact (mul_eq_zero.mp h).resolve_left htwo
private theorem d2C (rec:c2) (f :af 3) (S:cH[X])
  (hS:S.natDegree<bf) (hf :Of f S=0) :
  Of (Dm f) S=0 :=
 d2c rec f S hS hf (bf-3) rfl
private theorem c7B (base :c1) (rec:c2) (f :af 3) (i:Fin bf)
   {Q:Bk} (h:acU f Q) :
   lz i*tO (apq f)^(2*bf) -
     tO (VT f i)∈gN Q:= by
 rw [(base Q h.prime).2]
 intro a ha
 exact fUY f a i
   (rec f _ (bnu a) (h.solves a ha))
private theorem eed (base :c1) (rec:c2) {f :af 3} {Q:Bk}
    (h:acU f Q) :
    cS6 f≤lA Q:= by
  have aiq (b:af 3)
      (hb : ∀ a∈oj cH Q,
        Of b (JC a)=0) :GZ b∈lA Q:= by
    change tO (GZ b)∈gN Q
    rw [(base Q h.prime).2]
    intro a ha
    rw [btJ,aHI,hb a ha,qy]
  exact Gj ((RJ _).mpr (aiq f h.solves))
    ((RJ _).mpr
      (aiq (Dm f) fun a ha =>
        d2C rec f _ (bnu a) (h.solves a ha)))
private theorem b31 (base :c1) {f :af 3} {Q:Bk}
  (h:acU f Q) :
  apq f∉lA Q:= by
 obtain ⟨a,ha,hs⟩:=h.regular
 intro hm
 have hz :=((base Q h.prime).2 (tO (GZ (pU f)))).mp hm a ha
 rw [btJ,aHI] at hz
 exact hs ((zm _ dF) (hz.trans (qy _).symm))
private theorem eEn {R:Type*} [ox R] (a b c d:R) :
  (a*b)*(c*d)=(a*c)*(b*d) :=
 mul_mul_mul_comm a b c d
private theorem fU1 (base :c1) (rec:c2) (f :af 3) (p:mK) :
    ∃ (u:nW) (n:ℕ),∀ Q:Bk,acU f Q →
      p*tO (apq f)^n - tO u∈gN Q:= by
  let s :=apq f
  induction p using EK with
  | C c =>
    refine ⟨oq c,0,fun Q _ => ?_⟩
    simp [tO]
  | add p q ihp ihq =>
    obtain ⟨u,n,hu⟩:=ihp
    obtain ⟨v,m,hv⟩:=ihq
    refine ⟨u*s^m+v*s^n,n+m,fun Q h => ?_⟩
    let π:=lV (gN Q)
    have hU:=Ideal.Quotient.eq_zero_iff_mem.mpr (hu Q h)
    have hV:=Ideal.Quotient.eq_zero_iff_mem.mpr (hv Q h)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π ((p+q)*tO s^(n+m) -
      tO (u*s^m+v*s^n))=0
    simp only [yU,lJ,qz ,qU,Et] at hU hV ⊢
    linear_combination π (tO s)^m*hU + π (tO s)^n*hV
  | mul_X p i ih =>
    obtain ⟨u,n,hu⟩:=ih
    refine ⟨u*VT f i,n+2*bf,fun Q h => ?_⟩
    let π:=lV (gN Q)
    have hU:=Ideal.Quotient.eq_zero_iff_mem.mpr (hu Q h)
    have hV:=Ideal.Quotient.eq_zero_iff_mem.mpr (c7B base rec f i h)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π ((p*lz i)*tO s^(n+2*bf) -
      tO (u*VT f i))=0
    simp only [yU,lJ,qU,Et,HZ] at hU hV ⊢
    calc
      _=(π p*π (tO s)^n) *
        (π (lz i)*π (tO s)^(2*bf)) :=
        eEn (π p) (π (lz i))
          (π (tO s)^n) (π (tO s)^(2*bf))
      _ = _:= by rw [hU,hV]
private theorem c0j (base :c1) {f :af 3} {Q:Bk}
   (h:acU f Q) {p:mK} {u:nW} {n:ℕ}
   (heq :p*tO (apq f)^n - tO u∈gN Q) :
   p∈gN Q↔u∈lA Q:= by
 have hp:=(base Q h.prime).1
 have hs :tO (apq f)^n∉gN Q :=
   fun hm=>b31 base h (hp.mem_of_pow_mem n hm)
 change p∈gN Q↔tO u∈gN Q
 constructor
 · intro hm
   exact ((gN Q).sub_mem_iff_right (Ideal.mul_mem_right _ _ hm)).mp heq
 · intro hm
   exact (hp.mem_or_mem (((gN Q).sub_mem_iff_left hm).mp heq)).resolve_right hs
theorem of_children (base :c1) (rec:c2) :aiJ.c1 := by
 intro f
 constructor
 · intro Q h
   refine ⟨(base Q h.prime).1,eed base rec h,b31 base h,?_⟩
   intro i
   refine ⟨VT f i,apq f^(2*bf),?_,?_⟩
   · intro hm
     exact b31 base h (((base Q h.prime).1).comap tO |>.mem_of_pow_mem _ hm)
   · rw [qU,pz]
     exact c7B base rec f i h
 · intro A hA B hB hij
   change acU f A at hA
   change acU f B at hB
   have he :gN A=gN B:= by
     ext p
     obtain ⟨u,n,h⟩:=fU1 base rec f p
     rw [c0j base hA (h A hA),c0j base hB (h B hB),hij]
   rw [← cNT base hA.prime,← cNT base hB.prime,he]
end
end aA3
end
section
namespace bRk
noncomputable section
open aR we aiJ aA3
open scoped Polynomial nonZeroDivisors
private abbrev bAf :=eT bf
private abbrev ak8:=cy (Fin bf) cH[X]
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Ek :Pk ak8 :=
 (vH cH[X]).map oq
private def transpose :ak8 ≃+* bAf[X] :=
 ((RP cH (Fin bf)).symm.trans
   (p5 cH (Fin bf))).toRingEquiv
private theorem dhX (i:Fin bf) :
  transpose (lz i)=oY (lz i) := by
 change p5 cH (Fin bf)
  ((RP cH (Fin bf)).symm (lz i))= _
 rw [← MvPolynomial.optionEquivRight_X_some cH,
  TH,zQa]
private theorem ct3 (d:cH[X]) :
    transpose (oq d)=d.map (oq:cH →+* bAf) := by
  have he :transpose.toRingHom.comp oq =
      P7 (oq:cH →+* bAf) := by
    apply z86
    · intro c
      change transpose (oq (oY c))=(oY c).map oq
      rw [Zf]
      change p5 cH (Fin bf)
        ((RP cH (Fin bf)).symm
          (oq (oY c)))= _
      rw [← MvPolynomial.optionEquivRight_C cH,
        TH,MvPolynomial.optionEquivLeft_C]
    · change transpose (oq qJ)=Polynomial.X.map oq
      rw [Polynomial.map_X]
      change p5 cH (Fin bf)
        ((RP cH (Fin bf)).symm
          (oq qJ))= _
      rw [← MvPolynomial.optionEquivRight_X_none cH,
        TH,WY]
  exact vk he d
private def Fl:bAf →+* ak8 :=
 mD oY
private theorem gD2 :transpose.toRingHom.comp Fl=Polynomial.C:= by
 apply yQ
 · intro c
   change transpose (Fl (oq c))=oY (oq c)
   rw [Fl,zi ,ct3,Zf]
 · intro i
   change transpose (Fl (lz i))=oY (lz i)
   rw [Fl,zS ,dhX]
private def aEe (Q:Bk) :lI ak8 :=
 Q.map Fl
private theorem c4J (Q:Bk) :
  aEe Q=(Q.map oY).comap transpose.toRingHom:= by
 have hm: (aEe Q).map transpose.toRingHom= Q.map Polynomial.C:= by
  rw [aEe,x7,gD2]
 rw [← hm]
 exact (UZ transpose.toRingHom transpose.bijective).symm
private theorem c0d (Q:Bk) (p:ak8) :
  p∈aEe Q ↔ ∀ n,(transpose p).coeff n∈Q:= by
 rw [c4J,Ts]
 change transpose p∈Q.map oY↔_
 exact Ideal.mem_map_C_iff
private theorem dWh (Q:Bk) (hQ:Q.IsPrime) :
  Disjoint (Ek :Set ak8) (aEe Q:Set ak8) := by
 refine Set.disjoint_left.mpr ?_
 intro p hp hmem
 obtain ⟨d,hd,rfl⟩:=Submonoid.mem_map.mp hp
 apply zyw hd
 apply Polynomial.ext
 intro n
 rw [z9]
 have hn:=(c0d Q _).mp hmem n
 rw [ct3,Eg] at hn
 by_contra hne
 exact hQ.ne_top (Q.eq_top_of_isUnit_mem hn ((isUnit_iff_ne_zero.mpr hne).map oq))
private theorem extend_eq (Q:Bk) :
   gN Q=(aEe Q).map (aU ak8 mK) := by
 have h: (aU cH[X] dF).comp oY =
     algebraMap cH dF :=
   u5 fun c=>(t8 cH cH[X] dF c).symm
 rw [gN,aEe,x7,Zh,Fl]
 congr 1
 apply u5
 intro p
 change mD (aU cH dF) p =
   mD _ (mD oY p)
 rw [Ml,h]
private theorem eMs (a :GD) (p:ak8) :
    point a (aU ak8 mK p) =
      aU cH[X] dF ((transpose p).map (vi a)) := by
  have he : (vi fun i=>oY (a i)) =
      (P7 (vi a)).comp transpose.toRingHom:= by
    apply yQ
    · intro d
      change vi (fun i=>oY (a i)) (oq d) =
        (transpose (oq d)).map (vi a)
      rw [yl,ct3]
      ext n
      simp only [Eg ,yl]
    · intro i
      change vi (fun j=>oY (a j)) (lz i) =
        (transpose (lz i)).map (vi a)
      rw [wY ,dhX,Zf ,wY]
  have hcoords : (fun i=>aU cH dF (a i)) =
      (aU cH[X] dF) ∘ (fun i=>oY (a i)) :=
    funext fun i=>t8 cH cH[X] dF (a i)
  rw [Zh,point,hcoords,← zsn,he]
  rfl
private theorem eFE (Q:Bk) [Q.IsPrime] (p:ak8) :
    p∈aEe Q ↔
      ∀ a∈oj cH Q,
        point a (aU ak8 mK p)=0:= by
  rw [c0d]
  simp only [eMs,map_eq_zero_iff _ (zm cH[X] dF),
    Polynomial.ext_iff,Eg ,z9]
  have coeff_iff (n:ℕ) : (transpose p).coeff n∈Q ↔
      ∀ a∈oj cH Q,vi a ((transpose p).coeff n)=0:= by
    change _↔(transpose p).coeff n ∈
      Bf cH (oj cH Q)
    rw [Iw]
  exact ⟨fun h a ha n=>(coeff_iff n).mp (h n) a ha,
    fun h n=>(coeff_iff n).mpr (fun a ha=>h a ha n)⟩
private theorem cS4 (a :GD) (p:ak8) (s :Ek) :
   point a (zzm mK p s)=0 ↔
     point a (aU ak8 mK p)=0:= by
 have he :=ov (point a) (IsLocalization.mk'_spec mK p s)
 rw [lJ] at he
 have hu:=(Sv mK s).map (point a)
 rw [← he,mul_eq_zero,or_iff_left hu.ne_zero]
theorem proof :aA3.c1 := by
  intro Q hQ
  let _:=hQ
  have hp: (aEe Q).IsPrime := by
    rw [c4J]
    exact ((Ideal.isPrime_map_C_iff_isPrime Q).mpr hQ).comap _
  have hd:=dWh Q hQ
  refine ⟨?_,?_⟩
  · rw [extend_eq]
    exact znL Ek mK _ hp hd
  · intro b
    obtain ⟨p,s,rfl⟩:=zcf Ek b
    have hmem:zzm mK p s∈gN Q↔p∈aEe Q:= by
      rw [extend_eq,IsLocalization.mk'_mem_iff]
      change p∈((aEe Q).map (aU ak8 mK)).under
        ak8↔_
      rw [ztT Ek mK hp hd]
    rw [hmem,eFE Q p]
    exact ⟨fun h a ha=>(cS4 a p s).mpr (h a ha),
      fun h a ha=>(cS4 a p s).mp (h a ha)⟩
end
end bRk
end
section
namespace bRl
open aR oR we ac1 Polynomial
open scoped Polynomial
private theorem d5B (P:af 3) (S:cH[X]) :
  Of P S=jW (aU ao cH) S P:= by
 rw [Of,znM]
 rfl
theorem proof :aA3.c2 := by
 intro f S _ hf k _
 simp only [d5B] at hf ⊢
 rw [bam.bFn _ _ _ hf k,
  mul_left_comm (2 :cH[X]),bam.bPp,
  ← z6T,zqa,J4]
end bRl
end
section
namespace bRi
noncomputable section
open zP aaq as3 MvPolynomial
variable {A:Fin 4→nq Exponent}
private theorem b0c (hz : ∀ j,0∈A j) :
  ew A (ab5 A hz)=1 := by
 classical
 rw [ab5,GW,map_prod]
 apply Finset.prod_eq_one
 intro j _
 simp [ew,monomial_zero']
private theorem bYC (hz : ∀ j,0∈A j) :
  (ab5 A hz).IsWeightedHomogeneous (jT A) (fun _=>1) := by
 classical
 have hweight: (∑ j:Fin 4,(xW j 1 :Cy))=fun _=>1 := by
  funext j
  simp [Ze,Pi.single_apply]
 rw [← hweight,ab5,GW]
 exact IsWeightedHomogeneous.prod _ _ _ fun j _ =>
  isWeightedHomogeneous_X (fZ A) (jT A) (⟨j,⟨0,hz j⟩⟩:Slot A)
theorem proof :as3.c1 := by
 classical
 intro A hz hv i f hf
 obtain ⟨⟨d,hfd⟩,hfI⟩:=hf
 let s :nq (Fin 4) :=Finset.univ.filter fun j=>j.val< i.val+1
 have hs : (↑s :Set (Fin 4)) = {j | j.val< i.val+1} := by
   ext j
   simp [s]
 have hfspan:ew A f∈yB (af A) (ve A '' ↑s) := by
   rw [hs]
   exact hfI
 rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hfspan
 obtain ⟨c,hc⟩:=hfspan
 simp only [qG] at hc
 choose q hq using fun j=>btB hz hv (c j)
 let n:=Finset.univ.sup q+1
 let D:Degree :=(fun _=>n)+d
 have hsingle (j l:Fin 4) : (xW j 1 :Cy) l≤1 := by
   by_cases h:l=j
   · simp [h]
   · simp [Pi.single_eq_of_ne h]
 have hpad (j:Fin 4) : (fun _=>q j)≤D - xW j 1 := by
   intro l
   have hqj:q j≤Finset.univ.sup q:=Xx (FR j)
   have hj:=hsingle j l
   change q j≤Finset.univ.sup q+1+d l-(xW j 1 :Cy) l
   omega
 have hdegree (j:Fin 4) :D - xW j 1+Pi.single j 1=D:= by
   funext l
   have hj:=hsingle j l
   change D l-(xW j 1 :Cy) l+(xW j 1 :Cy) l=D l
   apply G6
   change (xW j 1 :Cy) l≤Finset.univ.sup q+1+d l
   omega
 have hlift (j:Fin 4) : ∃ r∈Kx A (D - xW j 1),ew A r=c j:= by
   have hm:=a6w hz (hpad j) (hq j)
   rw [← aOJ] at hm
   exact hm
 choose r hr hrd using hlift
 let g := ∑ j∈s,r j*T2 A j
 have hgd:g∈Kx A D:= by
   apply Y4
   intro j _
   rw [← hdegree j]
   exact (show (r j).IsWeightedHomogeneous _ _ from hr j).mul
     (show (T2 A j).IsWeightedHomogeneous _ _ from aN7 j)
 have hg:ew A g=ew A f := by
   simpa only [g,pC,lJ,hrd,aNd] using hc
 have hgcut:g∈oz (T2 A '' {j:Fin 4 | j.val< i.val+1}) := by
   apply Ideal.sum_mem
   intro j hj
   exact Ideal.mul_mem_left _ _ (G9 ⟨j,(Finset.mem_filter.mp hj).2,rfl⟩)
 have hweight:n•(fun _=>1 :Cy)=fun _=>n:= by
   funext j
   simp [MO]
 have hpower :=(bYC hz).pow n
 rw [hweight] at hpower
 have hprod: (ab5 A hz^n*f).IsWeightedHomogeneous (jT A) D :=
   hpower.mul hfd
 have hrel :ab5 A hz^n*f - g∈Se A 0:= by
   apply G9
   refine ⟨⟨D,hprod.sub hgd⟩,?_⟩
   rw [yU,lJ,qU,b0c,one_pow,uh,hg,sub_self]
   exact (mo A 0).zero_mem
 refine ⟨n,?_⟩
 have hrem:ab5 A hz^n*f - g∈ke A (i.val+1) :=
   Submodule.mem_sup_left hrel
 have hcut:g∈ke A (i.val+1) :=
   Submodule.mem_sup_right hgcut
 simpa only [sub_add_cancel] using (ke A (i.val+1)).add_mem hrem hcut
end
end bRi
end
section
set_option backward.isDefEq.respectTransparency false
namespace cyL
noncomputable section
open aR dN BO MvPolynomial
open scoped BigOperators nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev a3S (C:lI oZ) (a :uJ) :lI (adi a) :=
 C.map (mD (aU c9 (dV a)))
private theorem ef4 (C:lI oZ) (a :uJ) (hC:C.IsPrime) :
    (a3S C a).IsPrime∧adK a∉a3S C a := by
  classical
  let A:=cy (uL a) c9
  let R:=cy (uL a) oZ
  let T:=cy (Fin 4) A
  let S:=adi a
  let e :R ≃ₐ[c9] T:=z7 c9 (uL a) (Fin 4)
  let I:lI R:=C.map oq
  let I' : lI T:=I.map e.toRingHom
  let M:Pk T:=(vH A).map oq
  have :C4 M S:=MvPolynomial.isLocalization (vH A) (dV a)
  have :=hC
  have hI:I.IsPrime := by
    rw [show I=vG (mD (σ:=uL a) (lV C)) by
      rw [zRA,Ideal.mk_ker]]
    exact zgL _
  have hback :I'.comap e.toRingHom=I:=UZ _ e.bijective
  have hI' : I'.IsPrime := by
    have :=hI
    exact Ideal.map_isPrime_of_surjective (f :=e.toRingHom) e.surjective
      (by rw [(RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective]; exact bot_le)
  have hdisj:Disjoint (M:Set T) (I' : Set T) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨s,hs,rfl⟩ hmem
    have hpre :e.symm (oq s)∈I:= by
      rw [← hback,Ts]
      change e (e.symm (oq s))∈I'
      rw [zIH]
      exact hmem
    change z7 c9 (Fin 4) (uL a) (oq s)∈I at hpre
    rw [Qy] at hpre
    obtain ⟨m,hm⟩:=support_nonempty.mpr (zyw hs)
    have hc:=MvPolynomial.mem_map_C_iff.mp hpre m
    rw [MvPolynomial.coeff_map] at hc
    exact hC.ne_top (C.eq_top_of_isUnit_mem hc
      (IsUnit.map _ (isUnit_iff_ne_zero.mpr (mem_support_iff.mp hm))))
  have hJ:I'.map (aU T S)=a3S C a := by
    simp only [I',I,a3S,x7]
    congr 1
    apply u5
    intro p
    change aU T S (e (oq p))=mD _ p
    rw [Qy ,Zh,Ml]
    congr 1
  refine ⟨hJ ▸ znL M S I' hI' hdisj,?_⟩
  let G:R := ∑ m∈Bz a,
    lz m*oq (∏ i:Fin 4,lz i^(m i).val)
  have hG:aU T S (e G)=adK a := by
    unfold G adK
    simp only [pC,lJ]
    apply sI rfl
    intro m _
    dsimp only [e]
    rw [commAlgEquiv_X,Qy]
    simp only [map_prod,qU,zS]
    change (mD (aU A (dV a))) (oq (lz m)) *
      (∏ i:Fin 4,(mD (aU A (dV a)) (lz i)) ^
        (m i).val)= _
    simp only [zi ,zS ,A]
  intro hmem
  have hG' : aU T S (e G)∈I'.map (aU T S) := by rwa [hJ,hG]
  have hG'' : e G∈I' := by
    rw [← ztT M S hI' hdisj]
    exact hG'
  have hGI:G∈I:= by
    rw [← hback]
    exact hG''
  have hzero : (0:uL a)∈Bz a := by simp [Bz]
  have hone :G.coeff (GB (0:uL a) 1)=1 := by
    have hterm (m:uL a) :
        (lz m*oq (∏ i:Fin 4,lz i^(m i).val) :R).coeff
          (GB (0:uL a) 1)=if m=0 then 1 else 0:= by
      rw [pz ,coeff_C_mul,coeff_X]
      by_cases hm:m=0
      · subst m
        simp
      · have hs :GB m 1≠GB (0:uL a) (1 :ℕ) := by
          intro hs
          exact hm (Finsupp.single_left_injective (JK : (1 :ℕ)≠0) hs)
        simp [hs,hm]
    calc
      G.coeff (GB (0:uL a) 1) =
          ∑ m∈Bz a,if m=0 then (1 :oZ) else 0:= by
        dsimp only [G]
        rw [zqN]
        exact sI rfl fun m _=>hterm m
      _=1 := by simp [hzero]
  exact hC.ne_top ((Ideal.eq_top_iff_one C).mpr (hone ▸ MvPolynomial.mem_map_C_iff.mp hGI _))
end
noncomputable section
open aR dN BO Dr aiK MvPolynomial
open scoped BigOperators Pointwise TensorProduct
variable {k :Type*} [nX k]
private def OV (I:lI (cy (Fin 4) k)) (p:uJ) :
   Re k (cy (Fin 4) k ⧸ I) :=
 (Dv k (vw p)).map (Zi k I).toLinearMap
instance (I:lI (cy (Fin 4) k)) (p:uJ) :qx k (OV I p) := by
 have :qx k (Dv k (vw p)) :=
  zwB (basisRestrictSupport k _)
 exact Module.Finite.map _ _
private theorem dEM (I:lI (cy (Fin 4) k)) {p q:uJ}
  (hb:p.b≤q.b) (hj:p.j≤q.j) (ht:p.t≤q.t) :
  OV I p≤OV I q:= by
 apply Submodule.map_mono
 apply restrictSupport_mono
 intro e he
 rw [OW] at he ⊢
 exact ⟨he.1.trans (by omega),he.2.1.trans (by omega),he.2.2.trans (by omega)⟩
private theorem dEN {I:lI (cy (Fin 4) k)} {p q:uJ}
  {f :cy (Fin 4) k} (hf :f∈Dv k (vw q))
  {x :cy (Fin 4) k ⧸ I} (hx :x∈OV I p) :
  lV I f*x∈OV I (p.plus q) := by
 classical
 obtain ⟨g,hg,rfl⟩:=hx
 refine ⟨f * g,?_,lJ (lV I) _ _⟩
 intro e he
 obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_add.mp (support_mul f g he)
 have hu' := (OW q u).mp (hf hu)
 have hv' := (OW p v).mp (hg hv)
 simp only [OW,Finsupp.add_apply,NZ]
 omega
private theorem aDS {S:Set (Fin 4 →₀ ℕ)} {n:ℕ} {e :Fin 4 →₀ ℕ}
   (he :e∈n•S) :
   ∃ P:cy S k,P.totalDegree≤n∧Gn k S P=xu e 1 := by
 induction n generalizing e with
 | zero =>
   rw [zero_smul,Set.mem_zero] at he
   subst e
   exact ⟨1,by simp,by simp⟩
 | succ n ih =>
   rw [succ_nsmul] at he
   obtain ⟨u,hu,v,hv,rfl⟩:=he
   obtain ⟨P,hP,hmap⟩:=ih hu
   refine ⟨P*lz ⟨v,hv⟩,?_,?_⟩
   · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)
   · rw [lJ,hmap,monomialMap_X,monomial_mul_monomial,Ee]
private theorem cD3 (I:lI (cy (Fin 4) k))
   (p:uJ) (hp:Nq p) (n:ℕ) :
   G4 (I.comap (Gn k (vw p)).toRingHom) n =
     pQ k (OV I (p.scale n)) := by
 classical
 let φ:=Gn k (vw p)
 let J:=I.comap φ.toRingHom
 let g:=Ideal.quotientMapₐ I φ (zk :J≤Ideal.comap φ.toRingHom I)
 have hg (P:cy (vw p) k) :
     g (lV J P)=lV I (φ P) :=rfl
 have hmap : (p6 J n).map g.toLinearMap=OV I (p.scale n) := by
   apply zd
   · rintro _ ⟨x,hx,rfl⟩
     obtain ⟨P,hP,rfl⟩:=mem_quotientDegreeLE.mp hx
     refine ⟨φ P,?_,hg P |>.symm⟩
     change φ P∈Dv k (vw (p.scale n))
     rw [← aIH p hp n]
     exact monomialMap_mem_restrictSupport_nsmul (biS p) hP
   · rw [OV,restrictSupport_eq_span,Xu,VH]
     rintro _ ⟨_,⟨e,he,rfl⟩,rfl⟩
     rw [← aIH p hp n] at he
     obtain ⟨P,hP,hφ⟩:=aDS (k :=k) he
     exact ⟨lV J P,GR hP,by simp [hg,φ,hφ]⟩
 have hinj:th g.toLinearMap:=Ideal.quotientMap_injective
 change pQ k (p6 J n)= _
 rw [← hmap]
 exact (zW6 _ hinj _).finrank_eq
section ScalarExtension
variable {E :Type*} [nX E] [nI k E]
private def Pd (I:lI (cy (Fin 4) k)) :
   E ⊗[k] (cy (Fin 4) k ⧸ I) ≃ₐ[E]
     cy (Fin 4) E ⧸ I.map (mD (aU k E)) := by
 let e :=zoR (σ:=Fin 4) k E
 let j:cy (Fin 4) k →ₐ[k] E ⊗[k] cy (Fin 4) k :=
   Kl
 have hc:e.toRingHom.comp j.toRingHom=mD (aU k E) := by
   apply u5
   intro p
   change e (1 ⊗ₜ[k] p)= _
   simp [e]
 refine (zTd (R:=k) E _ E I).trans
   (zpY _ _ e ?_)
 exact ((x7 (I:=I) j.toRingHom e.toRingHom).trans
   (ov (fun f=>I.map f) hc)).symm
private theorem cSe (I:lI (cy (Fin 4) k)) (p:uJ) :
   pQ E (OV (I.map (mD (aU k E))) p) =
     pQ k (OV I p) := by
 let e :=(Pd (E :=E) I).toLinearEquiv
 have h: ((OV I p).baseChange E).map e.toLinearMap =
     OV (I.map (mD (aU k E))) p:= by
   simp only [OV,restrictSupport_eq_span,Xu,Submodule.baseChange_span,
     Set.image_image]
   congr 1
   apply Set.image_congr
   intro m _
   change Pd (E :=E) I (1 ⊗ₜ[k] (lV I (xu m 1))) =
     lV _ (xu m 1)
   simp [Pd,MvPolynomial.map_monomial]
 rw [← h,← (zW6 e.toLinearMap e.injective _).finrank_eq,
   ← (Submodule.toBaseChange.toLinearEquiv E (OV I p)).finrank_eq,Module.finrank_baseChange]
end ScalarExtension
private theorem gCo {f :cy (Fin 4) k} {n:ℕ}
  (hf :f.totalDegree≤n) :f∈Dv k (vw ((⟨3, 3,1⟩:uJ).scale n)) := by
 intro e he
 have h:=(Kc he).trans hf
 rw [z9d _ _ (fun _=>rfl),zmL] at h
 simp only [OW,Fa]
 omega
private theorem egb (h:uJ) :
   adK (h.scale 6) ∈
     Dv (dV (h.scale 6)) (vw (h.scale 3)) := by
 classical
 apply Y4
 intro m hm
 rw [MvPolynomial.prod_X_pow,C_mul_monomial]
 rw [monomial_mem_restrictSupport]
 left
 obtain ⟨hb,hj,ht⟩:=(Finset.mem_filter.mp hm).2
 simp only [OW,Finsupp.indicator_of_mem (FR _),Fa]
 simp only [zmL,Fa] at hb hj ht
 change 0*(m 0).val+1*(m 1).val+2*(m 2).val+3*(m 3).val≤6*h.j at hj
 omega
end
noncomputable section
open aR Dr MvPolynomial
private abbrev xo:Shape :=⟨3, 3,1⟩
private theorem fTb {k :Type*} [nX k]
    (I:lI (cy (Fin 4) k)) (hI:I.IsPrime)
    (hdim: (n5 I).natDegree=1)
    (g:cy (Fin 4) k) (hg:g∉I)
    (q:uJ) (hsupport :g∈Dv k (vw q)) :
    ∃ N :ℕ,∀ n≥N,∀ m:ℕ,
      m*pQ k (cy (Fin 4) k ⧸ (I ⊔ oz {g})) +
        pQ k (OV I (xo.scale n)) ≤
      pQ k (OV I ((xo.scale n).plus (q.scale m))) := by
  have :=hI
  let J:=I ⊔ oz {g}
  have hJ: (n5 J).natDegree=0:= by
    have h:=(MK
      hI hg zk).1
    change (n5 J).natDegree≤_ at h
    rw [hdim] at h
    omega
  have :=(natDegree_affineHilbertPolynomial_eq_zero_iff (I:=J)).mp hJ
  obtain ⟨N,hN⟩:=exists_quotientDegreeLE_eq_top J
  refine ⟨N,fun n hn m => ?_⟩
  let W:= fun m=>OV I ((xo.scale n).plus (q.scale m))
  let c:=lV I g
  have hc:c≠0:=mt Ideal.Quotient.eq_zero_iff_mem.mp hg
  let cut:=SU k (Df :I≤J)
  have hstep (m:ℕ) :pQ k (cy (Fin 4) k ⧸ J) +
      pQ k (W m)≤pQ k (W (m+1)) := by
    let π:=cut.toLinearMap.domRestrict (W (m+1))
    have hπ:vZ π:= by
      intro x
      have hx :x∈p6 J n:= by rw [hN n hn]; trivial
      obtain ⟨f,hf,rfl⟩:=mem_quotientDegreeLE.mp hx
      have hbase :lV I f∈OV I (xo.scale n) :=
        ⟨f,gCo hf,rfl⟩
      have hincl:OV I (xo.scale n)≤W (m+1) :=
        dEM I (S2 ..) (S2 ..) (S2 ..)
      exact ⟨⟨lV I f,hincl hbase⟩,rfl⟩
    have hshape : ((xo.scale n).plus (q.scale m)).plus q =
        (xo.scale n).plus (q.scale (m+1)) := by
      cases q
      simp only [NZ,Fa ,Nat.add_mul,uh,Nat.add_assoc]
    have hmul (x :W m) :c*(x :cy (Fin 4) k ⧸ I)∈W (m+1) := by
      rw [show W (m+1)=OV I (((xo.scale n).plus (q.scale m)).plus q) by
        rw [hshape]]
      exact dEN hsupport x.property
    let μ:=((zzN k c).domRestrict (W m)).codRestrict (W (m+1)) hmul
    have hμ:th μ:= fun x y hxy =>
      zg (mul_left_cancel₀ hc (ov zza hxy))
    have hcut:cut c=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (G2 (Mj g))
    have hker :LinearMap.range μ≤wA π:= by
      rintro _ ⟨x,rfl⟩
      apply LinearMap.mem_ker.mpr
      change cut (c*x.val)=0
      rw [lJ,hcut,vh]
    have hrank :=π.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hπ,Yi] at hrank
    change pQ k (cy (Fin 4) k ⧸ J) +
      pQ k (wA π)=pQ k (W (m+1)) at hrank
    have hbound:pQ k (W m)≤pQ k (wA π) :=(LinearMap.finrank_range_of_inj hμ).symm.trans_le
      (Submodule.finrank_mono hker)
    omega
  change m*pQ k (cy (Fin 4) k ⧸ J) +
    pQ k (OV I (xo.scale n))≤pQ k (W m)
  induction m with
  | zero =>
    have hzero :W 0=OV I (xo.scale n) := by
      dsimp only [W]
      congr 1
      simp only [NZ,Fa ,Nat.zero_mul,Nat.add_zero]
    rw [hzero,Nat.zero_mul,Nat.zero_add]
  | succ m ih =>
    have hs :=hstep m
    rw [Nat.succ_mul]
    omega
end
noncomputable section
open aR dN BO Dr aiK lB MvPolynomial Filter
private theorem aCx (p:uJ) (hp:Nq p) :
  vZ (Gn c9 (vw p)) := by
 apply monomialMap_surjective
 intro i
 have ⟨hb,hj,ht⟩:=hp
 fin_cases i <;> norm_num [OW,Finsupp.single_apply] <;> omega
private theorem cYh (a b:ℚ) :
    (oY a*qJ+Polynomial.C b).natDegree≤1 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · calc
      (oY a*qJ).natDegree ≤
          (oY a).natDegree+(qJ:IT ℚ).natDegree :=
        Polynomial.natDegree_mul_le
      _≤1 := by simp
  · simp
private theorem aHH {P:IT ℚ} (h:P.natDegree≤1) (x :ℚ) :
  P.eval x=P.coeff 1*x+P.coeff 0:= by
 conv_lhs=>rw [Polynomial.eq_X_add_C_of_natDegree_le_one h]
 simp
theorem proof :bjC.c3:= by
  intro C h hC hdim hh _
  let a :=h.scale 6
  let E :=dV a
  let I:=a3S C a
  let g:=adK a
  let d:=pN C a
  let p:=xo.plus h
  have hbase :Nq xo:=⟨by decide,by decide,by decide⟩
  have hp:Nq p:= by
    obtain ⟨hb,hj⟩:=hh
    change 3+h.j≤3+h.b∧3*(1+h.t)≤3+h.j∧0<1+h.t
    omega
  have hdI: (n5 I).natDegree=1 := by
    change (n5 (C.map (mD (aU c9 E)))).natDegree=1
    rw [Ey.ZI]
    exact hdim
  obtain ⟨hI,hg⟩:=ef4 C a hC
  obtain ⟨N,hN⟩:=fTb I hI hdI g hg (h.scale 3) (egb h)
  let B:=C.comap (Gn c9 (vw xo)).toRingHom
  let P:=C.comap (Gn c9 (vw p)).toRingHom
  obtain ⟨NB,hNB⟩:=NY B
  obtain ⟨NP,hNP⟩:=NY P
  have hdB: (n5 B).natDegree≤1 :=
    (z1R _
      (aCx xo hbase) C).trans hdim |>.le
  have hdP: (n5 P).natDegree≤1 :=
    (z1R _
      (aCx p hp) C).trans hdim |>.le
  let basePoly :=n5 B
  let sumPoly :=n5 P
  let lower :=oY ((d:ℚ)+3*basePoly.coeff 1)*qJ+Polynomial.C (basePoly.coeff 0)
  let upper :=oY (3*sumPoly.coeff 1)*qJ+Polynomial.C (sumPoly.coeff 0)
  have hgrowth : ∀ᶠ m:ℕ in atTop,lower.eval (m:ℚ)≤upper.eval (m:ℚ) := by
    filter_upwards [eventually_ge_atTop (N+NB+NP)] with m hm
    have hr :=hN (3*m) (by omega) m
    have hshape : (xo.scale (3*m)).plus ((h.scale 3).scale m)=p.scale (3*m) := by
      cases h
      dsimp [p,NZ,Fa]
      congr 1 <;> ring
    change m*d+Module.finrank E (OV I (xo.scale (3*m))) ≤
      pQ E (OV I ((xo.scale (3*m)).plus ((h.scale 3).scale m))) at hr
    rw [hshape] at hr
    change m*d +
        pQ (dV a) (OV (a3S C a) (xo.scale (3*m))) ≤
      pQ (dV a) (OV (a3S C a) (p.scale (3*m))) at hr
    rw [cSe (E :=dV a) C (xo.scale (3*m)),
      cSe (E :=dV a) C (p.scale (3*m)),
      ← cD3 C xo hbase,← cD3 C p hp] at hr
    change m*d+affineHilbertFunction B (3*m)≤G4 P (3*m) at hr
    have he : (m:ℚ)*d+basePoly.eval ((3*m:ℕ) :ℚ)≤ sumPoly.eval ((3*m:ℕ) :ℚ) := by
      rw [hNB (3*m) (by omega),hNP (3*m) (by omega)]
      exact_mod_cast hr
    rw [aHH hdB,aHH hdP] at he
    push_cast at he
    simp [lower,upper]
    linarith
  have hslope :=Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (cYh _ _) (cYh _ _) hgrowth
  have hc: (d:ℚ)+3*basePoly.coeff 1≤3*sumPoly.coeff 1 := by
    simpa [lower,upper,Polynomial.coeff_add,Polynomial.coeff_mul_X] using hslope
  change (d:ℚ)≤6*((sumPoly.coeff 1 - basePoly.coeff 1)/(2 :ℚ)^1)
  norm_num
  linarith
end
end cyL
end
section
set_option backward.isDefEq.respectTransparency false
namespace wT
noncomputable section
open MvPolynomial
variable {F:Type*} [nX F]
private theorem bNf (G:cy (Fin 4) F) (a b:ℕ)
  (hA:G.weightedTotalDegree ME≤a)
  (hB:G.weightedTotalDegree MD ≤b) :
  G.weightedTotalDegree LV≤a+b:= by
 apply Pv
 intro e he
 have ha :=(le_weightedTotalDegree ME he).trans hA
 have hb:=(le_weightedTotalDegree MD he).trans hB
 simp [ME,MD,LV,Finsupp.weight_apply,
  z9d,Fin.sum_univ_succ,qG] at ha hb ⊢
 omega
open K1
end
end wT
end
section
namespace dm7
noncomputable section
open aR oR MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
private def Mt:af 2 ≃ₐ[ao[X]] (af 1)[X] :=
 (Vl ao[X] wB).trans (p5 ao[X] (Fin 1))
private abbrev Ka :af 1 ≃ₐ[ao[X]] ao[X][X] :=
 uniqueAlgEquiv ao[X] (Fin 1)
private theorem aUW (f :af 2) : (Mt f).natDegree=f.degreeOf 1 := by
 change (p5 _ _ (t3 wB f)).natDegree=f.degreeOf 1
 rw [natDegree_optionEquivLeft]
 exact degreeOf_rename_of_injective finSuccEquivLast.injective (Sd 1)
private theorem bqd (f :af 2) :
  Mt (Dw 1 f)=(Mt f).derivative := by
 change p5 _ _ (t3 wB (Dw 1 f)) =
  (p5 _ _ (t3 wB f)).derivative
 rw [← pderiv_rename finSuccEquivLast.injective,
  show wB (1 :Fin 2)=none from S1 ,
  optionEquivLeft_pderiv_none]
private theorem aYc (g:af 1) (S:ao[X]) :
  (Ka g).eval S=vi (jet S) g:= by
 have h:=eval₂_uniqueAlgEquiv (f :=g) (φ:=LO ao[X]) (a :=jet S)
 have hzero :jet S (default :Fin 1)=S:= by
  change qm 0 S=S
  simp
 simpa only [Polynomial.eval₂_id,MvPolynomial.eval₂_id,hzero] using h
private theorem aDh (f :af 2) (S:ao[X]) :
   ((Mt f).map (vi (jet S))).eval (jet S (1 :Fin 2)) =
     cK f S:= by
 rw [Mt,AlgEquiv.trans_apply,renameEquiv_apply,← optionEquivLeft_elim_eval,
   eval_rename,cK]
 apply ov (fun x :Fin 2→ao[X]=>vi x f)
 funext i
 fin_cases i <;> rfl
private theorem cu8 (g:af 1) : (Ka g).natDegree≤g.totalDegree := by
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro k hk
 rw [Ka,coeff_uniqueAlgEquiv]
 by_contra hn
 have h:=Kc (mem_support_iff.mpr hn)
 change (GB (default :Fin 1) k).degree≤g.totalDegree at h
 rw [Finsupp.degree_single] at h
 exact (GF hk) h
private theorem aUV (f :af 2) (k :ℕ) (hk :k≤f.totalDegree) :
  k+(Ka ((Mt f).coeff k)).natDegree≤f.totalDegree := by
 change k+(Ka ((p5 _ _ (t3 wB f)).coeff k)).natDegree≤_
 have hdeg: (t3 wB f).totalDegree=f.totalDegree :=
  totalDegree_renameEquiv wB f
 have hh:=totalDegree_coeff_optionEquivLeft_add_le ao[X] (Fin 1)
  (t3 wB f) k
  (by rw [hdeg]; exact hk)
 rw [hdeg] at hh
 exact (Nat.add_le_add_left (cu8 _) _).trans (by simpa [FU] using hh)
private def QI (f :af 2) :ao[X][X] :=
 let A:=Mt f
 if 0<A.natDegree then
  Ka (A.resultant A.derivative A.natDegree (A.natDegree - 1))
 else Ka (A.coeff 0)
end
end dm7
end
section
namespace aeD
noncomputable section
open MvPolynomial rW MJ WI
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type} [nX k]
private theorem mem_colon {I:lI (cy σ k)} {g p:cy σ k} :
  p∈I.colon {g} ↔ p*g∈I :=
 Au
private theorem dNz {I:lI (cy σ k)}
  (hI:I.IsHomogeneous (Dz σ k)) {g:cy σ k} {b:ℕ}
  (hg:g.IsHomogeneous b) :
  (I.colon {g}).IsHomogeneous (Dz σ k) := by
 intro i p hp
 rw [ayA]
 rw [mem_colon] at hp ⊢
 have h:=zfj hI hp (i+b)
 simpa only [Zy hg,ite_eq_left (by omega :b≤ i+b),
  show i+b - b=i by omega] using h
private theorem d4j [vl σ]
    (I:lI (cy σ k)) (hI:I.IsHomogeneous (Dz σ k))
    (hproper :I ≠ ⊤) :
    ∃ (g:cy σ k) (b:ℕ),g.IsHomogeneous b∧g∉I∧(I.colon {g}).IsPrime := by
  let good (g:cy σ k) :=(∃ b,g.IsHomogeneous b)∧g∉I
  have he : ∃ g,good g:=⟨1,⟨0,isHomogeneous_one σ k⟩,I.ne_top_iff_one.mp hproper⟩
  obtain ⟨g,hmax⟩:=exists_maximalFor_of_wellFoundedGT good (fun g=>I.colon {g}) he
  obtain ⟨⟨b,hgb⟩,hg⟩:=hmax.prop
  refine ⟨g,b,hgb,hg,(dNz hI hgb).isPrime_of_homogeneous_mem_or_mem ?_ ?_⟩
  · intro ht
    apply hg
    have h: (1 :cy σ k)∈I.colon {g} := by rw [ht]; exact Submodule.mem_top
    simpa only [mem_colon,uh] using h
  · intro x y _ hy hxy
    by_cases h:y∈I.colon {g}
    · exact Or.inr h
    · left
      rw [mem_colon] at h
      obtain ⟨d,hyd⟩:=hy
      have hygood:good (y*g) :=⟨⟨d+b,(show y.IsHomogeneous d from hyd).mul hgb⟩,h⟩
      have hle :I.colon {g} ≤ I.colon {y*g} := by
        intro p hp
        rw [mem_colon,show p*(y*g)=y*(p*g) by ac_rfl]
        exact I.mul_mem_left _ (mem_colon.mp hp)
      apply hmax.2 hygood hle
      exact mem_colon.mpr (by simpa only [v9] using mem_colon.mp hxy)
private def Be (J P:lI (cy σ k)) (hp:P.IsPrime) :ℕ∞ :=
 letI:=hp
 let L:=zf P
 Fz L (L ⧸ J.map (aU (cy σ k) L))
private theorem bYd {R S:Type*} [ox R] [ox S] [nI R S]
  (T:Pk R) [C4 T S] (I:lI R) (g:R) :
  (I.colon {g}).map (aU R S)=(I.map (aU R S)).colon {aU R S g} := by
 ext z
 obtain ⟨a,s,rfl⟩:=zcf T z
 rw [Au,qG,
  pz _ (aU R S g),IsLocalization.mul_mk'_eq_mk'_of_mul,
  zNj,zNj]
 simp only [Au,qG,v9,pz g]
private theorem b7x (I P:lI (cy σ k)) (hp:P.IsPrime)
   (g:cy σ k) :
   Be I P hp =
     Be (I.colon {g}) P hp+Be (I ⊔ oz {g}) P hp:= by
 let _:P.IsPrime :=hp
 let L:=zf P
 let r :=aU (cy σ k) L
 let J:=I.map r
 let a :=r g
 have h:=Module.length_eq_add_of_exact (Vp J a)
   (Submodule.factor (Df :J≤J ⊔ oz {a}))
   (aPy J a) (Submodule.factor_surjective Df)
   (a7c J a)
 change Fz L (L ⧸ I.map r) =
   Fz L (L ⧸ (I.colon {g}).map r) +
     Fz L (L ⧸ (I ⊔ oz {g}).map r)
 rw [bYd P.primeCompl,Oc,Qx ,R9]
 exact h
private theorem aIs {I P:lI (cy σ k)} (hp:P.IsPrime)
   (h : ¬ I≤P) :Be I P hp=0:= by
 let _:P.IsPrime :=hp
 let L:=zf P
 have htop:I.map (aU (cy σ k) L) = ⊤ := by
   by_contra ht
   exact h (Set.disjoint_compl_left_iff_subset.mp
     ((IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl L I).mp ht))
 change Fz L (L ⧸ I.map (aU (cy σ k) L))=0
 simp [htop,Module.length_eq_zero]
private theorem brM (P:lI (cy σ k)) (hp:P.IsPrime) :
  Be P P hp=1 := by
 let _:P.IsPrime :=hp
 let L:=zf P
 change Fz L (L ⧸ P.map (aU (cy σ k) L))=1
 rw [Localization.AtPrime.map_eq_maximalIdeal]
 have h:IsSimpleModule L (L ⧸ IsLocalRing.maximalIdeal L) :=
  isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal L).1
 exact Module.length_eq_one _ _
private theorem dXc [vl σ] {P Q:lI (cy σ k)}
  (hP:P.IsPrime) (hlt:P<Q) (hd:xI P=2) :xI Q<2 := by
 obtain ⟨g,hgQ,hgP⟩:=SetLike.exists_of_lt hlt
 have hcut:P ⊔ oz {g} ≤ Q :=
  Gj hlt.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgQ))
 have hb:=(Lf hcut).trans
  (MK
    hP hgP (le_refl g.totalDegree)).1
 change xI Q≤xI P - 1 at hb
 omega
theorem dMY [vl σ] (J:lI (cy σ k))
    (hJ:J.IsHomogeneous (Dz σ k)) (hd:xI J≤2)
    (hmin : ∀ P,J.IsMinimalPrime P→xI P=2) :
    (n5 J).coeff 2 =
      ∑ P∈J.minimalPrimesFinset,
        (ado J P:ℚ)*(n5 P).coeff 2 := by
  classical
  let T:=J.minimalPrimesFinset
  suffices aux : ∀ I:lI (cy σ k),J≤I →
      I.IsHomogeneous (Dz σ k) →
      (∀ P (hp:J.IsMinimalPrime P),Be I P hp.isPrime ≠ ⊤) ∧
      (n5 I).coeff 2 =
        ∑ P∈T,(ado I P:ℚ)*(n5 P).coeff 2 from
    (aux J zk hJ).2
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α:=lI (cy σ k))) with
  | h I ih =>
    intro hJI hIhom
    by_cases hI:I = ⊤
    · subst I
      have hz (P:lI (cy σ k)) (hp:P.IsPrime) :Be ⊤ P hp=0 :=
        aIs hp (by simpa using hp.ne_top)
      refine ⟨fun P hp=> by simp [hz P hp.isPrime],?_⟩
      simp only [affineHilbertPolynomial_top,z9]
      symm
      apply Finset.sum_eq_zero
      intro P hP
      have hp:=(Ideal.mem_minimalPrimesFinset.mp hP).isPrime
      have he : (ado ⊤ P:ℕ)=(Be ⊤ P hp).toNat := by
        simp only [ado,dite_eq_left hp,Be]
      simp [he,hz P hp]
    obtain ⟨g,b,hgb,hg,hprime⟩:=d4j I hIhom hI
    let A:lI (cy σ k) :=I.colon {g}
    let B:lI (cy σ k) :=I ⊔ oz {g}
    have hIA:I≤A:=Ideal.le_colon
    have hIB:I<B:=lt_of_le_not_ge Df
      (fun h=>hg (h (G2 (Mj g))))
    have hspan: (oz {g}).IsHomogeneous (Dz σ k) := by
      apply Ideal.homogeneous_span
      intro f hf
      obtain rfl :=Set.mem_singleton_iff.mp hf
      exact ⟨b,hgb⟩
    obtain ⟨hfin,hbudget⟩:=ih B hIB (hJI.trans hIB.le) (hIhom.sup hspan)
    have hstep (P:lI (cy σ k)) (hp:J.IsMinimalPrime P) :
        Be I P hp.isPrime =
          Be A P hp.isPrime+Be B P hp.isPrime :=
      b7x I P hp.isPrime g
    have hterm (P:lI (cy σ k)) (hp:J.IsMinimalPrime P) :
        Be A P hp.isPrime=if P=A then 1 else 0:= by
      split_ifs with h
      · subst P
        exact brM A hp.isPrime
      · exact aIs hp.isPrime
          (fun hAP=>h (zd (hp.2 ⟨hprime,hJI.trans hIA⟩ hAP) hAP))
    have hfinite (P:lI (cy σ k)) (hp:J.IsMinimalPrime P) :
        Be A P hp.isPrime ≠ ⊤ := by rw [hterm P hp]; split_ifs <;> simp
    have hweight (P:lI (cy σ k)) (hP:P∈T) :
        (ado I P:ℚ)=(ado B P:ℚ)+(if P=A then 1 else 0) := by
      have hp:=Ideal.mem_minimalPrimesFinset.mp hP
      have hw (L:lI (cy σ k)) :ado L P=(Be L P hp.isPrime).toNat := by
        simp only [ado,dite_eq_left hp.isPrime,Be]
      rw [hw,hw,hstep P hp,ENat.toNat_add (hfinite P hp) (hfin P hp),hterm P hp,Mk]
      split_ifs <;> simp [FU]
    have hdim:=(Lf hJI).trans hd
    refine ⟨fun P hp=> by
      rw [hstep P hp]
      exact WithTop.add_ne_top.mpr ⟨hfinite P hp,hfin P hp⟩,?_⟩
    have hA: (n5 A).coeff 2 =
        if A∈T then (n5 A).coeff 2 else 0:= by
      split_ifs with hAT
      · rfl
      · let _:A.IsPrime :=hprime
        obtain ⟨P,hp,hPA⟩:=zXL (hJI.trans hIA:J≤A)
        have hne :P≠A:= fun he=>hAT (Ideal.mem_minimalPrimesFinset.mpr (he ▸ hp))
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (dXc hp.isPrime (Xp hPA hne) (hmin P hp))
    calc
      _=(n5 B).coeff 2+(n5 A).coeff 2 :=
        (dMj hIhom hgb hdim).symm
      _=(∑ P∈T,(ado B P:ℚ)*(n5 P).coeff 2) +
          (if A∈T then (n5 A).coeff 2 else 0) :=congrArg₂ (· + ·) hbudget hA
      _ = _:= by
        rw [← X4 T A (fun P=>(n5 P).coeff 2),
          ← PA]
        refine sI rfl fun P hP => ?_
        rw [hweight P hP,add_mul,ite_mul,uh,vh]
theorem dsp [vl σ] (J:lI (cy σ k))
   (hJ:J.IsHomogeneous (Dz σ k)) (hd:xI J=2)
   (hmin : ∀ P,J.IsMinimalPrime P→xI P=2) :
   p9 J =
     ∑ P∈J.minimalPrimesFinset,(ado J P:ℚ)*p9 P:= by
 classical
 have hdegree (P:lI (cy σ k)) (hP:xI P=2) :
     p9 P=2*(n5 P).coeff 2 := by
   change (n5 P).natDegree=2 at hP
   simp only [p9,SM,hP]
   norm_num
 rw [hdegree J hd,dMY J hJ hd.le hmin,zxw]
 apply sI rfl
 intro P hP
 rw [hdegree P (hmin P (Ideal.mem_minimalPrimesFinset.mp hP))]
 ac_rfl
end
end aeD
end
section
namespace aeD
noncomputable section
open MvPolynomial rW MJ
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 :Prop :=
  ∀ (k σ:Type) [nX k] [vl σ] (A:lI (cy σ k)),
    FV 1 (n5 (JA A)) =
      n5 A
def c2 :Prop :=
  ∀ (k σ:Type) [nX k] [vl σ] (A:lI (cy σ k)),
    (lW A).comap (Zq (k :=k) (σ:=σ)) =
      JA A ⊔ oz {lz none}
theorem of_children (h1 :c1) (h2 :c2) :MJ.c1 := by
 classical
 intro k σ _ _ A hA hdim
 change (n5 A).natDegree=2 at hdim
 let C:=JA A
 let B:=lW A
 let φ:cy (oD σ) k →ₐ[k] cy σ k :=Zq
 let w:cy (oD σ) k :=lz none
 let _:C.IsPrime :=dLT A hA
 have hw:w∉C:=eFx A hA
 have hcut:B.comap φ=C ⊔ oz {w} := h2 k σ A
 have hdiff :FV 1 (n5 C) =
     affineHilbertPolynomial A:=h1 k σ A
 have hle :=Polynomial.natDegree_backwardDifference_le (1 :ℚ) (n5 C)
 rw [hdiff,hdim] at hle
 have hback :=Te
   (P:=n5 C) (JK : (1 :ℚ)≠0) (by omega)
 have hCdim: (n5 C).natDegree=3:= by
   have h:=hback.1
   rw [hdiff,hdim] at h
   omega
 have hcol:C.colon {w} = C:= by
   refine zd ?_ Ideal.le_colon
   intro p hp
   exact (‹C.IsPrime›.mem_or_mem (Submodule.mem_colon_singleton.mp hp)).resolve_right hw
 have hBpoly :n5 B=n5 A:= by
   have hx :=b5W (cFL A) (isHomogeneous_X k none)
   change n5 (C ⊔ oz {w}) +
     u9 (-(1 :ℚ)) (n5 (C.colon {w})) =
     n5 C at hx
   rw [hcol,← hcut,cUJ] at hx
   rw [← hdiff,FV]
   exact eq_sub_of_add_eq hx
 have hBhom:=dzO A
 have hmin (P) (hP:B.IsMinimalPrime P) :xI P=2 := by
   have hp:=Ideal.minimalPrimes_comap_of_surjective
     (f :=φ.toRingHom) (show vZ φ from cBq) hP
   change P.comap φ∈(B.comap φ).minimalPrimes at hp
   rw [hcut] at hp
   have hx :=Pf hw hp
   have hPpoly :n5 (P.comap φ)=n5 P :=
     cUJ P
   rw [hPpoly,hCdim] at hx
   change (n5 P).natDegree=2
   omega
 refine ⟨fun P hp=>⟨hmin P hp,eAp hBhom hp⟩,?_⟩
 have hBdim:xI B=2 := by
   change (n5 B).natDegree=2
   rwa [hBpoly]
 have hdeg:p9 A=p9 B:= by simp [p9,hBpoly]
 exact hdeg.trans (dsp B hBhom hBdim hmin)
end
end aeD
end
section
namespace bRs
noncomputable section
open MvPolynomial MJ aeD
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type*} [nX k]
private def atOne :cy (oD σ) k →ₐ[k] cy σ k :=
 p7 fun i=>i.elim 1 lz
private theorem duG (p:cy (oD σ) k) :
  atOne p=(p5 k σ p).eval 1 := by
 let e :IT (cy σ k) →ₐ[k] cy σ k :=
  (z8 1).restrictScalars k
 have h: (atOne (k :=k) (σ:=σ))=e.comp (p5 k σ).toAlgHom:= by
  ext i
  cases i <;> simp [e,atOne,WY ,zQa]
 exact Kv h p
private theorem cBw (d:oD σ →₀ ℕ) (r :k) :
  atOne (xu d r)=xu d.some r := by
 rw [duG,optionEquivLeft_monomial,zsC,one_pow,Ee]
private theorem dux (d:oD σ →₀ ℕ) (r :k) :
  Zq (xu d r)=if d none=0 then xu d.some r else 0:= by
 rw [bUp,optionEquivLeft_monomial,Polynomial.coeff_monomial]
private theorem cJ4 (d:oD σ →₀ ℕ) :
  d.degree=d none+d.some.degree := by
 simp only [Finsupp.degree_apply]
 exact Finsupp.sum_option_index d (fun _ e=>e) (fun _=>rfl) (fun _ _ _=>rfl)
private theorem de8 {p:cy (oD σ) k} {n:ℕ}
   (hp:p.IsHomogeneous n) :
   (atOne p).totalDegree≤n∧Zq p=Av n (atOne p) := by
 classical
 have hdeg (d:oD σ →₀ ℕ) (hd:d∈p.support) :d none+d.some.degree=n:= by
   rw [← cJ4]
   exact (hp.degree_eq_sum_deg_support hd).symm
 have h₁:atOne p = ∑ d∈p.support,xu d.some (p.coeff d) := by
   conv_lhs=>rw [p.as_sum]
   simp only [pC,cBw]
 have h₀:Zq p =
     ∑ d∈p.support,if d none=0 then xu d.some (p.coeff d) else 0:= by
   conv_lhs=>rw [p.as_sum]
   simp only [pC,dux]
 constructor
 · rw [h₁]
   apply WK
   intro d hd
   exact (MS (p.coeff d) (n:=d.some.degree) rfl).totalDegree_le.trans
     (by have :=hdeg d hd; omega)
 · rw [h₀,h₁,pC]
   apply sI rfl
   intro d hd
   rw [UY (MS _ rfl)]
   have he :d none=0↔n=d.some.degree := by
     have :=hdeg d hd
     omega
   simp only [he]
private theorem cZ0 (A:lI (cy σ k))
   {p:cy (oD σ) k} {n:ℕ} (hp:p.IsHomogeneous n) :
   p∈JA A↔atOne p∈A:= by
 change anT A p=0↔_
 have hc (m:ℕ) : (anT A p).coeff m =
     lV A (atOne (if m=n then p else 0)) := by
   rw [bcy,UY hp]
   rfl
 constructor
 · intro h
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   simpa [h] using (hc n).symm
 · intro h
   ext m
   rw [hc,z9]
   by_cases hm:m=n
   · simpa [hm] using Ideal.Quotient.eq_zero_iff_mem.mpr h
   · simp [hm]
private theorem aUr (f :cy σ k) {n:ℕ} (hf :f.totalDegree≤n) :
   ∃ p:cy (oD σ) k,p.IsHomogeneous n∧atOne p=f := by
 classical
 let term (d:σ →₀ ℕ) :=xu (d.optionElim (n - d.degree)) (f.coeff d)
 refine ⟨∑ d∈f.support,term d,II _ _ _ ?_,?_⟩
 · intro d hd
   apply MS
   have hle :d.degree≤n:=(Kc hd).trans hf
   simp only [cJ4,z6S,zpo]
   exact G6 hle
 · simp only [pC,term,cBw,zpo]
   exact f.support_sum_monomial_coeff
private theorem map_closure (A:lI (cy σ k)) :
   (JA A).map (Zq (k :=k) (σ:=σ))=lW A:= by
 apply zd
 · apply Ideal.map_le_iff_le_comap.mpr
   intro p hp
   change Zq p∈lW A
   rw [← sum_homogeneousComponent p,pC]
   apply Ideal.sum_mem
   intro n _
   have hC:=zfj (cFL A) hp n
   have hhom:=z8k n p
   have ha :=(cZ0 A hhom).mp hC
   obtain ⟨hle,hs⟩:=de8 hhom
   rw [hs]
   rcases hle.eq_or_lt with he | hlt
   · exact G9 ⟨_,ha,by rw [he]⟩
   · rw [homogeneousComponent_eq_zero _ _ hlt]
     exact (lW A).zero_mem
 · apply Ideal.span_le.mpr
   rintro _ ⟨f,hf,rfl⟩
   obtain ⟨p,hh,h₁⟩:=aUr f (n:=f.totalDegree) zk
   have hp:=(cZ0 A hh).mpr (h₁.symm ▸ hf)
   have hmap :=Ideal.mem_map_of_mem (Zq (k :=k) (σ:=σ)) hp
   rwa [(de8 hh).2,h₁] at hmap
private theorem etH :
   vG (Zq (k :=k) (σ:=σ)).toRingHom =
     oz {lz none} := by
 ext p
 rw [Ideal.mem_span_singleton]
 change Zq p=0↔lz none∣p
 rw [bUp,← Polynomial.X_dvd_iff]
 simpa only [WY] using
   (map_dvd_iff (p5 k σ) (a :=lz none) (b:=p))
theorem proof :aeD.c2 := by
 intro k σ _ _ A
 rw [← map_closure A,Ideal.comap_map_of_surjective' _ cBq]
 exact ov (fun I=>JA A ⊔ I) etH
end
end bRs
end
section
namespace bRr
noncomputable section
open MvPolynomial aeD
variable {k σ:Type} [nX k]
private def specialize :cy (oD σ) k →ₐ[k] cy σ k :=
 p7 fun i=>i.elim 1 lz
private theorem gt2 (p:cy σ k) :
  specialize (t3 some p)=p:= by
 have h: (specialize (k :=k) (σ:=σ)).comp (t3 some)=AlgHom.id k _:= by
  ext i
  simp [specialize]
 exact Kv h p
private theorem gCp (p:cy (oD σ) k) :
   (specialize p).totalDegree≤p.totalDegree := by
 let e :=(z8 (R:=cy σ k) (1 :cy σ k)).restrictScalars k
 have he : (specialize (k :=k) (σ:=σ))=e.comp (p5 k σ).toAlgHom:= by
   ext i
   cases i <;> simp [e,specialize]
 rw [he]
 change (e (p5 k σ p)).totalDegree≤p.totalDegree
 conv_lhs=>rw [(p5 k σ p).as_sum_support]
 rw [pC,← mem_restrictTotalDegree]
 apply Y4
 intro i _
 rw [mem_restrictTotalDegree]
 have h:e (Kh i ((p5 k σ p).coeff i)) =
     (p5 k σ p).coeff i:= by
   change z8 (R:=cy σ k) (1 :cy σ k)
     (Kh i _)= _
   rw [z99,zsC,one_pow,Ee]
 rw [h]
 exact totalDegree_coeff_optionEquivLeft_le k σ p i
private theorem aUr {p:cy σ k} {n:ℕ}
    (hp:p.totalDegree≤n) :
    ∃ q:cy (oD σ) k,q.IsHomogeneous n∧specialize q=p:= by
  let h (d:σ →₀ ℕ) :cy (oD σ) k :=
    t3 some (xu d (p.coeff d))*lz none^(n - d.degree)
  refine ⟨∑ d∈p.support,h d,?_,?_⟩
  · apply II
    intro d hd
    have hd' : d.degree≤n:=(Kc hd).trans hp
    have hh: (h d).IsHomogeneous (d.degree+(n - d.degree)) :=
      ((MS (p.coeff d) rfl).rename_isHomogeneous (f :=some)).mul
        (isHomogeneous_X_pow none (n - d.degree))
    simpa only [Nat.add_sub_of_le hd'] using hh
  · have hw:specialize (lz none :cy (oD σ) k)=1 := by
      simp [specialize]
    rw [pC]
    calc
      _ = ∑ d∈p.support,xu d (p.coeff d) := by simp [h,gt2,hw]
      _=p:=p.as_sum.symm
private theorem ctP {τ:Type} {p:cy τ k} {n:ℕ}
  (hp:p.totalDegree≤n+1) :
  (p - Av (n+1) p).totalDegree≤n:= by
 classical
 apply Pv
 intro d hd
 change d.degree≤n
 rw [zuk,coeff_sub,coeff_homogeneousComponent] at hd
 have hne :d.degree≠n+1 := by
  intro he
  simp [he] at hd
 simp only [Nr hne,FQ] at hd
 have hle :d.degree≤n+1 :=
  (Kc (MvPolynomial.mem_support_iff.mpr hd)).trans hp
 exact Nat.le_of_lt_succ (Xp hle hne)
private def bDd (A:lI (cy σ k)) :
  (cy (oD σ) k ⧸ JA A) →ₐ[k] IT (cy σ k ⧸ A) :=
 zTA (JA A) (anT A)
  (fun _ hp=>RingHom.mem_ker.mp hp)
private theorem cHB (A:lI (cy σ k))
 (p:cy (oD σ) k) :
 bDd A (lV (JA A) p)=anT A p:=rfl
private def bxR (A:lI (cy σ k)) (n:ℕ) :
   p6 (JA A) n →ₗ[k] p6 A n :=
 let f :=((Polynomial.lcoeff (cy σ k ⧸ A) n).restrictScalars k).comp
   (bDd A).toLinearMap
 (f.domRestrict _).codRestrict _ fun x=> by
   obtain ⟨p,_,hpx⟩:=mem_quotientDegreeLE.mp x.property
   change (bDd A x.val).coeff n∈p6 A n
   rw [← hpx,cHB,bcy]
   exact GR (p:=specialize (Av n p))
     ((gCp _).trans (z8k n p).totalDegree_le)
private theorem ctK (A:lI (cy σ k)) (n:ℕ)
  (x :p6 (JA A) n) (p:cy (oD σ) k)
  (hp:lV (JA A) p=x.val) :
  (bxR A n x).val=lV A (specialize (Av n p)) := by
 change (bDd A x.val).coeff n= _
 rw [← hp,cHB,bcy]
 rfl
private theorem gB5 (A:lI (cy σ k)) (n:ℕ) :
  vZ (bxR A n) := by
 intro y
 obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
 obtain ⟨q,hq,hqp⟩:=aUr hp
 refine ⟨⟨lV _ q,GR hq.totalDegree_le⟩,zg ?_⟩
 rw [ctK A n _ q rfl,homogeneousComponent_eq_self hq,hqp,hpy]
private theorem etL (A:lI (cy σ k)) (n:ℕ) :
    wA (bxR A (n+1)) =
      (p6 (JA A) n).comap
        (p6 (JA A) (n+1)).subtype := by
  ext x
  rw [ XJ]
  change bxR A (n+1) x=0↔x.val∈p6 (JA A) n
  constructor
  · intro hz
    obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp x.property
    have hzero :lV A (specialize (Av (n+1) p))=0 :=
      (ctK A (n+1) x p hpx).symm.trans (ov zza hz)
    have hm:Av (n+1) p∈JA A:= by
      change anT A (Av (n+1) p)=0
      ext i
      rw [z9,bcy,
        UY (homogeneousComponent_mem (n+1) p)]
      by_cases hi:i=n+1
      · rw [zYo hi]
        exact hzero
      · simp [hi]
    refine mem_quotientDegreeLE.mpr ⟨p - Av (n+1) p,
      ctP hp,?_⟩
    rw [yU,Ideal.Quotient.eq_zero_iff_mem.mpr hm,FQ,hpx]
  · intro hx
    obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp hx
    apply zg
    rw [ctK A (n+1) x p hpx,
      homogeneousComponent_eq_zero _ _ (TZ hp)]
    simp
private theorem em2 [vl σ] (A:lI (cy σ k)) (n:ℕ) :
   G4 A (n+1)+affineHilbertFunction (JA A) n =
     G4 (JA A) (n+1) := by
 have h:=(bxR A (n+1)).finrank_range_add_finrank_ker
 rw [LinearMap.range_eq_top.mpr (gB5 A (n+1)),Yi ,
   etL,
   (Submodule.comapSubtypeEquivOfLe (zhv (JA A)
     (Nat.le_succ n))).finrank_eq] at h
 exact h
theorem proof :aeD.c1 := by
 intro k σ _ _ A
 obtain ⟨N,hN⟩:=NY (JA A)
 apply zpB (N₀:=N+1)
 intro m hm
 have h₁:1≤ m:= by omega
 have h₂:m - 1+1=m:= by omega
 rw [zjN,← G7,← Nat.cast_sub h₁,
  hN m (by omega),hN (m - 1) (by omega)]
 have h:=em2 A (m - 1)
 rw [h₂] at h
 exact sub_eq_iff_eq_add.mpr (by exact_mod_cast h.symm)
end
end bRr
end
section
namespace axb
noncomputable section
open yz MeasureTheory
open scoped BigOperators
def aRv {α:Type} (v :α→iz) (S:nq α)
    (f :iz →ₗ[ℝ] ℝ) :Prop :=
  ∀ a,a∈S ↔ ∀ b,f (v b)≤f (v a)
def agG {α:Type} (v :α→iz) (S:nq α) :Prop :=
 S.Nonempty ∧ ∃ f :iz →ₗ[ℝ] ℝ,aRv v S f
def flags {α:Type} [t7 α] (v :α→iz) :
    nq (Fin 5→nq α) := by
  classical
  exact Finset.univ.filter (fun F=>StrictMono F ∧ ∀ j,agG v (F j))
theorem bsB {α:Type} [t7 α] (v :α→iz)
  (F:Fin 5→nq α) :
  F∈flags v↔StrictMono F ∧ ∀ j,agG v (F j) := by
 classical
 simp [flags]
def JG {α:Type} (v :α→iz) (S:nq α) :iz :=
 (S.card:ℝ)⁻¹ • ∑ a∈S,v a
def aoa {α:Type} (v :α→iz) (F:Fin 5→nq α) :
    Set iz :=
  v8 ℝ (oK (fun j=>JG v (F j)))
end
end axb
end
section
namespace axb
noncomputable section
open aR oR yz Qp MeasureTheory Filter
open scoped BigOperators Pointwise Topology
private def bYL:Fin 5→iz :=
 Fin.cons 0 (fun j=>xW j 1)
def cus :Set iz :=v8 ℝ (oK bYL)
def aHC (x :Fin 5→iz) :Matrix (Fin 4) (Fin 4) ℝ :=
 fun i j=>x j.succ i - x 0 i
private theorem gq9 (x :Fin 5→iz) :
    v8 ℝ (oK x) =
      (fun y :iz=>x 0+y) ''
        ((aHC x).toLin' '' cus) := by
  let f :iz →ᵃ[ℝ] iz :=
    (AffineEquiv.constVAdd ℝ iz (x 0)).toAffineMap.comp
      (aHC x).toLin'.toAffineMap
  have hf (j:Fin 5) :f (bYL j)=x j:= by
    refine Fin.cases ?_ (fun j => ?_) j
    · change x 0+(aHC x).toLin' 0=x 0
      rw [qy ,zE]
    · change x 0+(aHC x).toLin' (xW j 1)=x j.succ
      rw [Matrix.toLin'_apply,Matrix.mulVec_single_one]
      ext i
      change x 0 i+(x j.succ i - x 0 i)=x j.succ i
      ring
  have hr :f '' oK bYL=oK x := by
    rw [← Set.range_comp]
    exact ov oK (funext hf)
  rw [← hr,← AffineMap.image_convexHull,Set.image_image]
  rfl
theorem gra (x :Fin 5→iz) :
   (qM (v8 ℝ (oK x))).toReal =
     |(aHC x).det| * (volume cus).toReal:= by
 have hshift (s :Set iz) :qM ((fun y=>x 0+y) '' s)=qM s := by
   let e :=MeasurableEquiv.addLeft (x 0)
   change qM (e '' s)=qM s
   rw [e.image_eq_preimage_symm]
   exact measure_preimage_add qM (-(x 0)) s
 rw [gq9,hshift,Measure.addHaar_image_linearMap,LinearMap.det_toLin',
   ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)]
private def a3a (b:Fin 4→Bool) :iz :=
 fun i=>if b i then 1 else 0
private theorem dRI (f :iz→iz)
    (haff : ∀ (a :iz) (i:Fin 4) (t:ℝ),
      f (zc a i t) =
        (1 - t)•f (zc a i 0)+t•f (zc a i 1))
    (a :iz) (ha : ∀ i,a i∈Gk (0:ℝ) 1) :
    f a∈v8 ℝ (oK (f ∘ a3a)) := by
  classical
  have aux : ∀ (S:nq (Fin 4)) (a :iz),
      (∀ i,a i∈Gk (0:ℝ) 1) →
      (∀ i∉S,a i=0∨a i=1) →
      f a∈v8 ℝ (oK (f ∘ a3a)) := by
    intro S
    induction S using zcw with
    | empty =>
      intro a _ ha'
      let b:Fin 4→Bool:= fun i=>decide (a i=1)
      have hb:a3a b=a := by
        funext i
        rcases ha' i (by simp) with h | h <;> simp [a3a,b,h]
      exact subset_convexHull ℝ _ ⟨b,ov f hb⟩
    | @insert i S hi ih =>
      intro a ha ha'
      have hup (t:ℝ) (ht:t=0∨t=1) (ht' : t∈Gk (0:ℝ) 1) :
          f (zc a i t)∈v8 ℝ (oK (f ∘ a3a)) := by
        apply ih
        · intro j
          by_cases hj:j=i
          · subst j
            simpa only [RD] using ht'
          · simpa only [UP hj] using ha j
        · intro j hj
          by_cases hji:j=i
          · subst j
            simpa only [RD] using ht
          · rw [UP hji]
            exact ha' j (by simp [hji,hj])
      have he :=haff a i (a i)
      rw [Function.update_eq_self] at he
      rw [he]
      exact (convex_convexHull ℝ _) (hup 0 (Or.inl rfl) (by simp))
        (hup 1 (Or.inr rfl) (by simp)) (sub_nonneg.mpr (ha i).2) (ha i).1 (by ring)
  exact aux Finset.univ a ha (by simp)
private def aTs (s :uJ) (h:ℕ) (a :iz) :iz :=
 let z :=a 2*(s.t:ℝ)
 let y :=a 1*((s.j:ℝ) - 2*z)
 ![a 0*((s.b:ℝ) - y - z),y,z,a 3*(h:ℝ)]
private theorem dEK (s :uJ) (h:ℕ) (a :iz)
    (i:Fin 4) (t:ℝ) :
    aTs s h (zc a i t) =
      (1 - t)•aTs s h (zc a i 0) +
        t•aTs s h (zc a i 1) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [aTs,zc,Pi.add_apply,MO,qG] <;> ring
private theorem dEL (s :uJ) (h:ℕ) (hc:bF s)
   (a :iz) (ha : ∀ i,a i∈Gk (0:ℝ) 1) :
   aTs s h a∈nD s h:= by
 have hct : (2 :ℝ)*(s.t:ℝ)≤ s.j:= by exact_mod_cast hc.2
 have hcj: (s.j:ℝ)≤ s.b:= by exact_mod_cast hc.1
 let z :=a 2*(s.t:ℝ)
 have hz :0≤z :=LP (ha 2).1 (Rm _)
 have hzt:z≤ s.t:= by
   simpa only [uh] using Mz (ha 2).2 (Rm s.t: (0:ℝ)≤ s.t)
 let y :=a 1*((s.j:ℝ) - 2*z)
 have hj:0≤(s.j:ℝ) - 2*z := by linarith
 have hy :0≤y :=LP (ha 1).1 hj
 have hyj:y≤(s.j:ℝ) - 2*z := by
   simpa only [uh] using Mz (ha 1).2 hj
 have hb:0≤(s.b:ℝ) - y - z := by linarith
 have hxb:a 0*((s.b:ℝ) - y - z)≤(s.b:ℝ) - y - z := by
   simpa only [uh] using Mz (ha 0).2 hb
 refine ⟨?_,?_,?_,hzt,?_⟩
 · intro j
   fin_cases j
   · exact LP (ha 0).1 hb
   · exact hy
   · exact hz
   · exact LP (ha 3).1 (Rm _)
 · change a 0*((s.b:ℝ) - y - z)+y+z≤ s.b
   linarith
 · change y+2*z≤ s.j
   linarith
 · change a 3*(h:ℝ)≤h
   simpa only [uh] using Mz (ha 3).2 (Rm h: (0:ℝ)≤h)
private theorem bNi {u b:ℝ} (hu:0≤u) (hb:u≤b) :
   ∃ t∈Gk (0:ℝ) 1,t*b=u:= by
 rcases (hu.trans hb).eq_or_lt with he | hp
 · exact ⟨0,by simp,by linarith⟩
 · exact ⟨u/b,⟨div_nonneg hu hp.le,(div_le_one hp).mpr hb⟩,div_mul_cancel₀ _ hp.ne'⟩
theorem bWo (s :uJ) (h:ℕ) (hc:bF s) :
   ∃ v :nq iz,nD s h=v8 ℝ (v :Set iz) := by
 classical
 let f :=aTs s h ∘ a3a
 refine ⟨Finset.univ.image f,?_⟩
 have hr : ((Finset.univ.image f :nq iz) :Set iz)=oK f := by
   simp
 rw [hr]
 refine Set.Subset.antisymm ?_ (convexHull_min ?_ (cDT s h))
 · intro x hx
   obtain ⟨hx,hb,hj,ht,hh⟩:=hx
   obtain ⟨a0,h0,ha0⟩:=bNi (hx 0)
     (show x 0≤(s.b:ℝ) - x 1 - x 2 by linarith)
   obtain ⟨a1,h1,ha1⟩:=bNi (hx 1)
     (show x 1≤(s.j:ℝ) - 2*x 2 by linarith)
   obtain ⟨a2,h2,ha2⟩:=bNi (hx 2) ht
   obtain ⟨a3,h3,ha3⟩:=bNi (hx 3) hh
   let a :iz := ![a0,a1,a2,a3]
   have ha : ∀ i,a i∈Gk (0:ℝ) 1 := by
     intro i
     fin_cases i <;> assumption
   have he :aTs s h a=x := by
     ext i
     fin_cases i <;> simp [aTs,a,ha0,ha1,ha2,ha3]
   rw [← he]
   exact dRI _ (dEK s h) _ ha
 · rintro _ ⟨b,rfl⟩
   apply dEL s h hc
   intro i
   cases hb:b i <;> simp [a3a,hb]
theorem bXo (B:Fin 4→Set iz)
   (hconv : ∀ i,Convex ℝ (B i)) (hzero : ∀ i,0∈B i)
   (hcompact : ∀ w:Fin 4→ℝ,PD (∑ i,w i•B i))
   (p:cy (Fin 4) ℝ)
   (hp : ∀ w:Fin 4→ℝ,(∀ i,0<w i) →
     p.eval w=(qM (∑ i,w i•B i)).toReal)
   (w:Fin 4→ℝ) (hw : ∀ i,0≤w i) :
   p.eval w=(qM (∑ i,w i•B i)).toReal:= by
 let K:Set iz := ∑ i,w i•B i
 let L:Set iz := ∑ i,B i
 change p.eval w=(qM K).toReal
 have hK:PD K:=hcompact w
 have hL:PD L:= by simpa [L] using hcompact (fun _=>1)
 have hzL:0∈L:=z2V _ _ |>.mpr
   ⟨fun _=>0,hzero,by simp⟩
 obtain ⟨R,hR⟩:=hL.isBounded.exists_norm_le
 let w' (t:ℝ) :Fin 4→ℝ:= fun i=>w i+t
 have hadd (t:ℝ) (ht:0≤t) : (∑ i,w' t i•B i)=K+t•L:= by
   rw [show K+t•L=(∑ i,w i•B i)+t•(∑ i,B i) from rfl,
     PM,← PA]
   exact sI rfl (fun i _=>(hconv i).add_smul (hw i) ht)
 have hpos : ∀ᶠ t:ℝ in 𝓝[Set.Ioi 0] 0,0<t:=self_mem_nhdsWithin
 have hp' (t:ℝ) (ht:0<t) :
     p.eval (w' t)=(qM (K+t•L)).toReal:= by
   rw [hp _ (fun i=>add_pos_of_nonneg_of_pos (hw i) ht),hadd t ht.le]
 have hw' : Tendsto w' (𝓝[Set.Ioi 0] 0) (𝓝 w) := by
   have hc:Continuous w' := by unfold w'; fun_prop
   have h0:w' 0=w:= by simp [w']
   rw [← h0]
   exact (hc.tendsto 0).mono_left zBa
 have hpLim:=(p.continuous_eval.tendsto w).comp hw'
 have hr :Tendsto (fun t:ℝ=>t*R) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
   simpa using ((continuous_id.mul_const R).tendsto 0).mono_left
     (zBa :𝓝[Set.Ioi (0:ℝ)] 0≤𝓝 0)
 have htLim:=(ENNReal.tendsto_toReal hK.measure_lt_top.ne).comp
   ((tendsto_measure_cthickening_of_isCompact (μ:=qM) hK).comp hr)
 apply zd
 · refine zyf hpLim htLim (hpos.mono fun t ht => ?_)
   change p.eval (w' t)≤(qM (Metric.cthickening (t*R) K)).toReal
   rw [hp' t ht]
   apply measureReal_mono _ (hK.isBounded.cthickening.measure_lt_top.ne)
   rintro _ ⟨x,hx,_,⟨y,hy,rfl⟩,rfl⟩
   refine Metric.mem_cthickening_of_dist_le _ x _ _ hx ?_
   simpa [dist_eq_norm,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.le] using
     Wl (hR y hy) ht.le
 · refine zyf tendsto_const_nhds hpLim (hpos.mono fun t ht => ?_)
   change (qM K).toReal≤p.eval (w' t)
   rw [hp' t ht]
   apply measureReal_mono _ (by rw [← hadd t ht.le]; exact (hcompact _).measure_lt_top.ne)
   intro x hx
   exact Set.mem_add.mpr ⟨x,hx,0,⟨0,hzL,zR t⟩,zE x⟩
end
end axb
end
section
namespace axb
noncomputable section
open aR oR yz Qp aeB
open MeasureTheory MvPolynomial
open scoped BigOperators Pointwise
def c1 :Prop :=
  ∀ {α:Type} [t7 α] (v :α→iz),
    v8 ℝ (oK v) =ᵐ[qM] ⋃ F∈flags v,aoa v F
def c2 :Prop :=
  ∀ {α:Type} [t7 α] (v :α→iz),
    Set.Pairwise (↑(flags v) :Set (Fin 5→nq α))
      (fun F G=>AEDisjoint qM (aoa v F) (aoa v G))
private theorem d5s {α:Type} {v :α→iz} {S:nq α}
  {f :iz →ₗ[ℝ] ℝ} (hf :aRv v S f)
  {a b:α} (ha :a∈S) (hb:b∈S) :f (v b)=f (v a) :=
 zd ((hf a).1 ha b) ((hf b).1 hb a)
private theorem d5t {α:Type} {v :α→iz} {S:nq α}
  {f :iz →ₗ[ℝ] ℝ} (hf :aRv v S f)
  {a b:α} (ha :a∈S) (hb:b∉S) :f (v b)<f (v a) := by
 refine Xp ((hf a).1 ha b) (fun he=>hb ((hf b).2 (fun c => ?_)))
 rw [he]
 exact (hf a).1 ha c
theorem bFN {α:Type} {v :α→iz} {S T:nq α}
  {f :iz →ₗ[ℝ] ℝ} (hf :aRv v S f)
  {a :α} (ha :a∈S) (hT:T.Nonempty) (hsub:T⊆S) :
  f (JG v T)=f (v a) := by
 have hc: (T.card:ℝ)≠0:= by exact_mod_cast hT.card_pos.ne'
 simp only [JG,FK,qG,pC]
 rw [sI rfl (fun b hb=>d5s hf ha (hsub hb)),
  Finset.sum_const,J4 ,← v9,NI hc,uh]
theorem bFO {α:Type} {v :α→iz} {S T:nq α}
  {f :iz →ₗ[ℝ] ℝ} (hf :aRv v S f)
  {a :α} (ha :a∈S) (hsub : ¬ T⊆S) :f (JG v T)<f (v a) := by
 obtain ⟨b,hb,hbs⟩:=Finset.not_subset.mp hsub
 have hc: (0:ℝ)<T.card:= by exact_mod_cast (Finset.card_pos.mpr ⟨b,hb⟩)
 have hlt : ∑ c∈T,f (v c) < ∑ _c∈T,f (v a) :=
  zfK (fun c _=>(hf a).1 ha c) ⟨b,hb,d5t hf ha hbs⟩
 have he :=zu3 hlt (inv_pos.mpr hc)
 simpa only [JG,FK,qG,pC,Finset.sum_const,J4 ,
  ← v9,NI hc.ne',uh] using he
theorem cSC {α:Type} [t7 α] (v :α→iz)
   (F:Fin 5→nq α) (hF:F∈flags v) :
   zP0 ℝ (fun j=>JG v (F j)) := by
 classical
 obtain ⟨hmono,hface⟩:=(bsB v F).1 hF
 rw [affineIndependent_iff_of_fintype]
 intro w hw hz i
 by_contra hi
 let T:=Finset.univ.filter (fun k :Fin 5=>w k≠0)
 have TA:i∈T:= by simp [T,hi]
 let j:=T.max' ⟨i,TA⟩
 have hjT:j∈T:=T.max'_mem _
 have hj:w j≠0:=(Finset.mem_filter.mp hjT).2
 have hzero (k :Fin 5) (hk :j<k) :w k=0:= by
   by_contra h
   exact (GF hk) (T.le_max' k (by simp [T,h]))
 have hjne :j≠0:= by
   intro he
   have hsum: (∑ k,w k)=w j:= by
     refine Qw j (fun k _ hk=>hzero k ?_) (by simp)
     rw [he] at hk ⊢
     exact Fin.pos_iff_ne_zero.mpr hk
   exact hj (hsum ▸ hw)
 obtain ⟨p,hp⟩:=Fin.exists_succ_eq_of_ne_zero hjne
 have hpj:p.castSucc<j:=hp ▸ p.castSucc_lt_succ
 obtain ⟨a,ha⟩:=(hface p.castSucc).1
 obtain ⟨f,hf⟩:=(hface p.castSucc).2
 have hl (k :Fin 5) (hk :k<j) :f (JG v (F k))=f (v a) := by
   apply bFN hf ha (hface k).1
   apply hmono.monotone
   rw [← hp] at hk
   exact Fin.le_castSucc_iff.mpr hk
 have hjlt:f (JG v (F j))<f (v a) :=
   bFO hf ha (GF (hmono hpj))
 rw [Finset.weightedVSub_eq_linear_combination _ hw] at hz
 have hv :=ov f hz
 simp only [qy ,pC,FK,qG] at hv
 have hsum : ∑ k,w k*(f (JG v (F k)) - f (v a))=0:= by
   simp only [mul_sub,zQq,← Ye,hv,hw,vh,FQ]
 have he : (∑ k,w k*(f (JG v (F k)) - f (v a))) =
     w j*(f (JG v (F j)) - f (v a)) := by
   refine Qw j (fun k _ hk => ?_) (by simp)
   rcases lt_or_gt_of_ne hk with hk | hk
   · rw [hl k hk,sub_self,G0]
   · rw [hzero k hk,vh]
 rw [he] at hsum
 exact (mul_ne_zero hj (ne_of_lt (sub_neg.mpr hjlt))) hsum
private abbrev aZr (v :Fin 4→nq iz) :=(i:Fin 4) → ↥(v i)
private def avj (v :Fin 4→nq iz) (w:Fin 4→ℝ)
   (a :aZr v) :iz :=
 ∑ i,w i•(a i:iz)
private theorem b7c (B:Fin 4→Set iz)
   (v :Fin 4→nq iz) (hv : ∀ i,B i=v8 ℝ (v i:Set iz))
   (w:Fin 4→ℝ) :
   v8 ℝ (oK (avj v w)) = ∑ i,w i•B i:= by
 have hr :oK (avj v w) = ∑ i,w i•(v i:Set iz) := by
   ext x
   rw [z2V]
   constructor
   · rintro ⟨a,rfl⟩
     exact ⟨fun i=>w i•(a i:iz),fun i=>⟨_,(a i).2,rfl⟩,rfl⟩
   · rintro ⟨z,hz,rfl⟩
     choose a ha he using hz
     exact ⟨fun i=>⟨a i,ha i⟩,sI rfl (fun i _=>he i)⟩
 rw [hr,convexHull_sum]
 simp only [convexHull_smul,← hv]
private theorem cWJ (v :Fin 4→nq iz) (w:Fin 4→ℝ)
    (hw : ∀ i,0<w i) (f :iz →ₗ[ℝ] ℝ) (a :aZr v) :
    (∀ b,f (avj v w b)≤f (avj v w a)) ↔
      ∀ i (b : ↥(v i)),f (b:iz)≤f (a i:iz) := by
  simp only [avj,pC,FK,qG]
  constructor
  · intro h i b
    by_contra! hi
    apply (not_lt_of_ge (h (zc a i b)))
    apply zfK
    · intro j _
      by_cases hj:j=i
      · subst j
        rw [RD]
        exact Wl hi.le (hw i).le
      · rw [UP hj]
    · refine ⟨i,FR i,?_⟩
      rw [RD]
      exact zu3 hi (hw i)
  · intro h b
    exact Wm (fun i _=>Wl (h i (b i)) (hw i).le)
private theorem ec4 (v :Fin 4→nq iz) (u w:Fin 4→ℝ)
  (hu : ∀ i,0< u i) (hw : ∀ i,0<w i) :
  flags (avj v u)=flags (avj v w) := by
 classical
 ext F
 simp only [flags,Finset.mem_filter,FR,true_and,agG,aRv,
  cWJ v u hu,cWJ v w hw]
private def a2f (v :Fin 4→nq iz) (F:Fin 5→nq (aZr v))
  (j:Fin 5) (k :Fin 4) :iz :=
 JG (fun a=>(a k :iz)) (F j)
private theorem dGx (v :Fin 4→nq iz) (w:Fin 4→ℝ)
  (F:Fin 5→nq (aZr v)) (j:Fin 5) :
  JG (avj v w) (F j) = ∑ k,w k•a2f v F j k := by
 simp only [JG,avj,a2f]
 rw [Finset.sum_comm,PM]
 apply sI rfl
 intro k _
 rw [← PM,smul_comm]
private theorem d0J (x :Fin 5→iz) (hx :zP0 ℝ x) :
  (aHC x).det≠0:= by
 intro hd
 obtain ⟨a,hne,ha⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr hd
 apply hne
 let e :=finSuccAboveEquiv (0:Fin 5)
 have hli:=(affineIndependent_iff_linearIndependent_vsub ℝ x 0).mp hx
 have hli' : z14 ℝ (fun j:Fin 4=>x j.succ - x 0) := by
  exact hli.comp e e.injective
 apply (linearIndependent_iff_injective_fintypeLinearCombination.mp hli')
 change (∑ j,a j•(x j.succ - x 0)) = ∑ j,(0:iz) j•(x j.succ - x 0)
 ext i
 have hi:=congrFun ha i
 simpa [aHC,Matrix.mulVec,dotProduct,Ze,MO,
  qG,Pi.sub_apply,pz] using hi
private def bdh (c:Fin 5→Fin 4→iz) :
  Matrix (Fin 4) (Fin 4) (cy (Fin 4) ℝ) :=
 fun i j => ∑ k,C (c j.succ k i - c 0 k i)*lz k
private theorem d0H (c:Fin 5→Fin 4→iz) :
   (bdh c).det.IsHomogeneous 4 := by
 classical
 rw [Matrix.det_apply']
 apply II
 intro σ _
 have hp: (∏ i,bdh c (σ i) i).IsHomogeneous (∑ _i:Fin 4,1) :=
   IsHomogeneous.prod _ _ _ (fun i _ =>
     II _ _ _ (fun _ _=>isHomogeneous_C_mul_X _ _))
 have hp' : (∏ i,bdh c (σ i) i).IsHomogeneous 4 := by simpa using hp
 rw [← map_intCast (C:ℝ →+* cy (Fin 4) ℝ)]
 exact hp'.C_mul _
private theorem d0G (c:Fin 5→Fin 4→iz) (w:Fin 4→ℝ) :
  (bdh c).det.eval w=(aHC (fun j => ∑ k,w k•c j k)).det:= by
 rw [(eval w).map_det]
 congr 1
 ext i j
 simp only [RingHom.mapMatrix_apply,Matrix.map_apply,bdh,pC,lJ,yl,wY ,aHC,
  Ze,MO,qG,← zQq]
 apply sI rfl
 intro k _
 ring
private def orientation (q:cy (Fin 4) ℝ) :ℝ :=
 if 0≤q.eval (fun _=>1) then 1 else -1
private theorem eH3 (q:cy (Fin 4) ℝ)
   (hn : ∀ w:Fin 4→ℝ,(∀ i,0<w i)→q.eval w≠0)
   (w:Fin 4→ℝ) (hw : ∀ i,0<w i) :
   |q.eval w| = orientation q*q.eval w:= by
 let U:Set (Fin 4→ℝ) :=Set.univ.pi (fun _=>Set.Ioi (0:ℝ))
 have hU:Convex ℝ U:=convex_pi (fun _ _=>convex_Ioi _)
 have h:=hU.isPreconnected.image (fun a=>q.eval a) q.continuous_eval.continuousOn
 have hz :0∉(fun a=>q.eval a) '' U:= by
   rintro ⟨a,ha,hq⟩
   exact hn a (by simpa [U] using ha) hq
 have hw' : q.eval w∈(fun a=>q.eval a) '' U:=⟨w,by simpa [U] using hw,rfl⟩
 have he :q.eval (fun _=>1)∈(fun a=>q.eval a) '' U :=
   ⟨fun _=>1,by simp [U],rfl⟩
 unfold orientation
 split_ifs with hs
 · have hg:0≤q.eval w:= by
     by_contra! hc
     exact hz (h.Icc_subset hw' he ⟨hc.le,hs⟩)
   simp [abs_of_nonneg hg]
 · have hg:q.eval w≤0:= by
     by_contra! hc
     exact hz (h.Icc_subset he hw' ⟨(lt_of_not_ge hs).le,hc.le⟩)
   simp [abs_of_nonpos hg]
private theorem enx (h1 :c1) (h2 :c2) {α:Type} [t7 α] (v :α→iz) :
  (qM (v8 ℝ (oK v))).toReal =
    ∑ F∈flags v,(qM (aoa v F)).toReal:= by
 have hF (F:Fin 5→nq α) :PD (aoa v F) :=
  (Set.finite_range _).isCompact_convexHull ℝ
 calc
  _=(qM (⋃ F∈flags v,aoa v F)).toReal :=
    ov ENNReal.toReal (measure_congr (h1 v))
  _ = _:=measureReal_biUnion_finset₀ (h2 v)
    (fun F _=>(hF F).measurableSet.nullMeasurableSet)
    (fun F _=>(hF F).measure_lt_top.ne)
private theorem c4T (h1 :c1) (h2 :c2)
    (B:Fin 4→Set iz) (v :Fin 4→nq iz)
    (hv : ∀ i,B i=v8 ℝ (v i:Set iz)) :
    ∃ p:cy (Fin 4) ℝ,p.IsHomogeneous 4 ∧
      ∀ w:Fin 4→ℝ,(∀ i,0<w i) →
        p.eval w=(qM (∑ i,w i•B i)).toReal:= by
  classical
  let fs :=flags (avj v (fun _=>1))
  let q (F:Fin 5→nq (aZr v)) :=(bdh (a2f v F)).det
  let p := ∑ F∈fs,C ((qM cus).toReal*orientation (q F))*q F
  have heval (F:Fin 5→nq (aZr v)) (w:Fin 4→ℝ) :
      (q F).eval w=(aHC (fun j=>JG (avj v w) (F j))).det:= by
    dsimp only [q]
    rw [d0G]
    simp_rw [dGx v w F]
  have hflags (w:Fin 4→ℝ) (hw : ∀ i,0<w i) :
      flags (avj v w)=fs :=ec4 v w _ hw (fun _=>zero_lt_one)
  have hn (F:Fin 5→nq (aZr v)) (hF:F∈fs)
      (w:Fin 4→ℝ) (hw : ∀ i,0<w i) : (q F).eval w≠0:= by
    rw [heval]
    apply d0J
    exact cSC (avj v w) F (by rw [hflags w hw]; exact hF)
  refine ⟨p,II _ _ _ (fun F _=>(d0H _).C_mul _),?_⟩
  intro w hw
  rw [← b7c B v hv w,enx h1 h2,hflags w hw]
  simp only [p,MvPolynomial.eval_sum,lJ,yl]
  apply sI rfl
  intro F hF
  rw [aoa,gra,← heval,eH3 (q F) (hn F hF) w hw]
  ring
end
end axb
end
section
set_option backward.isDefEq.respectTransparency false
namespace aZc
noncomputable section

open aeF (FZ)
open XX (EO adp aoG)
open scoped BigOperators Polynomial
section Residues
variable {k F:Type} [nX k] [nX F] [nI k F]
variable [nI k[X] F] [sH k k[X] F]
variable [IsDedekindDomain (DR k F)] [vj (DR k F) F]
variable [nI k (DR k F)] [sH k k[X] (DR k F)]
private def eOa (x :F) (hx :x≠0) (hu:Kp k F=x⁻¹)
   (P:aBi k F) [P.val.IsPrime] :
   P.val.ResidueField ≃ₐ[k] EO (aEh x hx hu P).val := by
 let B:=DR k F
 let p:=(aEh x hx hu P).val
 let Q:=aI6 (hu.symm ▸ inv_ne_zero hx) P
 let T:= Q.valuationSubringAtPrime F
 have :C4 P.val.primeCompl T:= by
   change C4 Q.asIdeal.primeCompl (Q.valuationSubringAtPrime F)
   infer_instance
 let loc:zf P.val ≃ₐ[B] T :=
   z0R P.val.primeCompl _ _
 have hT:T.toSubring=p.value.valuationSubring.toSubring :=
   ov ValuationSubring.toSubring (Q.valuationSubringAtPrime_eq_valuationSubring (K:=F))
 let e :zf P.val ≃+* p.value.valuationSubring :=
   loc.toRingEquiv.trans (zh4 hT)
 refine { IsLocalRing.ResidueField.mapEquiv e with commutes' := fun a => ?_ }
 change IsLocalRing.ResidueField.mapEquiv e
     (zeo _ (aU k (zf P.val) a)) =
   zeo _ (aoG p a)
 rw [IsLocalRing.ResidueField.mapEquiv_apply,IsLocalRing.ResidueField.map_residue]
 congr 1
 apply zg
 rw [t8 k B (zf P.val)]
 change (zh4 hT (loc (aU B _ (aU k B a)))).val= _
 rw [RingEquiv.coe_subringCongr_apply,loc.commutes]
 change aU B F (aU k B a)=aU k F a
 rw [t8 k k[X] B,← t8 k[X] B F,
   ← t8 k k[X] F]
private theorem eN9 [qx k[X] (DR k F)]
   (x :F) (hx :x≠0) (hu:Kp k F=x⁻¹) (P:aBi k F) :
   NW k (EO (aEh x hx hu P).val) ∧
     ze (aEh x hx hu P).val=P.val.inertiaDeg k[X] := by
 let B:=DR k F
 let p:=origin k
 let Q:=P.val
 let R:=k[X] ⧸ p
 let S:=B ⧸ Q
 have :Q.IsPrime :=P.property.1
 have :Q.LiesOver p:=P.property.2
 have :Q.IsMaximal:=Ideal.IsMaximal.of_liesOver_isMaximal Q p
 let:nX R:=zxv p
 let:nX S:=zxv Q
 let e :S ≃ₐ[k] EO (aEh x hx hu P).val :=
   (AlgEquiv.ofBijective (Hw k S Q.ResidueField)
     Q.bijective_algebraMap_quotient_residueField).trans (eOa x hx hu P)
 have :qx k R:=Np
   (caN (k :=k)).symm.toLinearMap (caN (k :=k)).symm.surjective
 have :qx k[X] S:=Np
   (Hw k[X] B S).toLinearMap (zh (I:= Q))
 have :qx R S:=Module.Finite.of_restrictScalars_finite k[X] R S
 have :qx k S:=Module.Finite.trans R S
 refine ⟨Np e.toLinearMap e.surjective,?_⟩
 have hrank :pQ k R=1 :=
   (caN (k :=k)).toLinearEquiv.finrank_eq.trans (Module.finrank_self k)
 rw [ze,← e.toLinearEquiv.finrank_eq,Ideal.inertiaDeg_eq_of_isMaximal p Q,
   ← Module.finrank_mul_finrank k R S,hrank,uh]
end Residues
theorem proof :XX.c2 := by
  classical
  intro k F _ _ _ x hx hfield hnorm
  let:nI k[X] F:=adp (k :=k) x⁻¹
  have :sH k k[X] F:=RC fun a=> by
    change aU k F a=z8 x⁻¹ (oY a)
    rw [z8q]
  have hu:Kp k F=x⁻¹:=ZJ _
  have htr :Yo k (Kp k F) := by
    rw [hu]
    exact fun hi=>hx (IsAlgebraic.inv_iff.mp hi)
  have :NW (FO (k :=k) (Kp k F)) F:= by
    rw [hu,cE4]
    exact hfield
  let B:=DR k F
  have :qx k[X] B:=hnorm
  have :IsDedekindDomain B:=bJK htr
  have :vj B F:=eFk htr
  let:nI k B:=Algebra.compHom B (aU k k[X])
  have :sH k k[X] B:=RC fun _=>rfl
  have :Module.IsTorsionFree k[X] B:=c1K htr
  have :Module.Free k[X] B:=F9
  let e :=Equiv.ofBijective (aEh x hx.ne_zero hu) (eN7 x hx.ne_zero hu)
  have hres (P:aBi k F) :=
    eN9 x hx.ne_zero hu P
  have :t7 (bkT k F x) :=Fintype.ofEquiv (aBi k F) e
  let f := fun v :pG k F=>ze v*pL v.value x
  have hf :vl (N0 (fun v :pG k F=>pL v.value x)) := by
    change vl (bkT k F x)
    infer_instance
  refine ⟨Set.finite_coe_iff.mp hf,?_,?_⟩
  · intro v hv
    obtain ⟨P,hP⟩:=e.surjective ⟨v,hv⟩
    have hv' : (aEh x hx.ne_zero hu P).val=v :=ov zza hP
    rw [← hv']
    exact (hres P).1
  change finsum f=FZ k x
  calc
    finsum f = ∑ᶠ v :bkT k F x,f v.val := by
      rw [finsum_subtype_eq_finsum_cond,← finsum_mem_univ f]
      apply zJX
      intro v hv
      exact iff_of_true (Set.mem_univ _) (fun h=>hv (by simp [f,h]))
    _ = ∑ᶠ P:aBi k F,P.val.ramificationIdx k[X]*P.val.inertiaDeg k[X] := by
      symm
      apply finsum_eq_of_bijective e e.bijective
      intro P
      change _=ze (aEh x hx.ne_zero hu P).val *
        pL (aEh x hx.ne_zero hu P).val.value x
      rw [(hres P).2,eN8,pz]
    _=pQ k[X] B:= by
      rw [finsum_eq_sum_of_fintype,Ideal.sum_ramification_inertia_eq_finrank]
    _=FZ k x := by
      rw [eFm htr,hu,cE4,FZ,Nr hx]
end
end aZc
end
