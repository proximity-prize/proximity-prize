import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdAA
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.DdBG
import ProximityPrize.SubmissionLower.DdZ3EWiUc
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_CodingTheory_ReedSolomon_MutualCorrelatedAgreement_Johnson_Agreement
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_Finset_PairwiseIntersection
import ProximityPrize.SubmissionLower.LibraryArkLib_ToMathlib_LinearAlgebra_FiniteDimensional
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Coeff
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Basis
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Degree_IsMonicOfDegree
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_TrivSqZeroExt_Ideal
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_BoxIntegral_UnitPartition
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Measure
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Visible
import ProximityPrize.SubmissionLower.LibraryMathlib_Combinatorics_Pigeonhole
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Finsupp_Interval
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Set_Card_Arithmetic
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Sym_NatCard
import ProximityPrize.SubmissionLower.LibraryMathlib_GroupTheory_CosetCover
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_FreeModule_Norm
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_TensorProduct_Free
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_FunctionField
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_RatFunc_Ostrowski
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_DedekindDomain_Factorization
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Finiteness_Descent
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Flat_Equalizer
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_GradedAlgebra_Radical
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Ideal_IsPrincipalPowQuotient
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Localization_NormTrace
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_OrderOfVanishing_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_PowerSeries_Inverse
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RamificationInertia_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Regular_Flat
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Surjective
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Unramified
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Spectrum_Prime_Homeomorph
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_Discrete_RankOne
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_LocalSubring
import ProximityPrize.SubmissionLower.LibraryMathlib_Topology_Algebra_MvPolynomial
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_DdA2
set_option Elab.async false



























































set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming AlgHom.coe_toRingHom→zlv,AlgHom.toRingHom_eq_coe→ziQ,Algebra→yU,Algebra.algebraMap→cy,Algebra.algebraMap_self_apply→zEi,Algebra.smul_def→Oc,CharP.cast_eq_zero_iff→zX2,CommRing→qJ,DFunLike.congr_fun→Ze,DecidableEq→t7,Disjoint→Mj,Field→zc,Filter→Df,Filter.atTop→pG,Filter.eventually_ge_atTop→ZJ,Fin.castSucc→uz,Fin.last→pC,Fin.lastCases→G0,Fin.range_fin_succ→Aa,Fin.sum_univ_eq_sum_range→Ok,Fin.sum_univ_four→zmM,Finite→qy,Finset→nI,Finset.add_sum_erase→zT2,Finset.card_univ→S1,Finset.finite_toSet→WD,Finset.induction_on→Kl,Finset.le_sup→WX,Finset.mem_filter→zO0,Finset.mem_insert_of_mem→ IU,Finset.mem_insert_self→Kc,Finset.mem_univ→vk,Finset.mul_sum→ze,Finset.prod_congr→Dz,Finset.prod_insert→zqX,Finset.range→p7,Finset.single_le_sum→Pc,Finset.sum_add_distrib→zfW,Finset.sum_apply→Zh,Finset.sum_attach→zKD,Finset.sum_congr→qx,Finset.sum_const→Mw,Finset.sum_filter→Np,Finset.sum_insert→Mk,Finset.sum_le_sum→uW
open _root_ renaming Finset.sum_nonneg→zlo,Finset.sum_subset→Wl,Finset.sup_le→X4,Finset.univ→Kv,Finsupp.add_apply→Dv,Finsupp.degree_eq_sum→zFi,Finsupp.filter_apply→zfF,Finsupp.finsetSum_apply→Xu,Finsupp.induction_linear→FK,Finsupp.single→Pk,Finsupp.single_apply→EK,Finsupp.smul_single_one→zrt,Finsupp.tsub_apply→VH,Finsupp.weight→ oy,Finsupp.weight_apply→SW,Finsupp.weight_eq_sum→Fz,Finsupp.weight_single→qG,Finsupp.weight_sub_single_add→Zg,Fintype→ oK,Fintype.card_fin→Pj,Fintype.equivFin→G8,Fintype.ofFinite→Gk,FractionRing→t5,Function.Injective→p9,Function.Surjective→vh,Function.comp_apply→Sd,Function.update→Wm,Ideal→aU,Ideal.IsPrime.comap→zm,Ideal.Quotient.eq_zero_iff_mem→G7,Ideal.Quotient.factorₐ→z5F,Ideal.Quotient.liftₐ→zTA,Ideal.Quotient.mk→mD,Ideal.Quotient.mk_surjective→Et,Ideal.Quotient.mkₐ→Fa,Ideal.comap_comap→Pf,Ideal.comap_isPrime→zG1,Ideal.comap_map_of_bijective→zFA,Ideal.comap_map_of_surjective→zEk,Ideal.comap_mono→Vl,Ideal.coprime_of_no_prime_ge→zQx,Ideal.height_add_one_le_of_lt_of_isPrime→zSK,Ideal.isPrime_map_of_isLocalizationAtPrime→zlD,Ideal.map_isPrime_of_surjective→TI,Ideal.map_map→zf,Ideal.map_span→y5,Ideal.mem_homogeneousCore_of_homogeneous_of_mem→zFp,Ideal.mem_map_of_mem→zh
open _root_ renaming Ideal.mem_span_singleton_self→vH,Ideal.mk_ker→Pr,Ideal.mul_mem_right→zx6,Ideal.mul_top→FU,Ideal.ofList→zE,Ideal.ofList_cons→z2L,Ideal.ofList_singleton→N0,Ideal.primesOver→TZ,Ideal.ringKrullDim_quotient_succ_le_of_lt→X8,Ideal.smul_eq_mul→FV,Ideal.span→lJ,Ideal.span_insert→OJ,Ideal.span_singleton_le_iff_mem→G3,Ideal.span_singleton_prime→zw5,Ideal.subset_span→ Il,Ideal.toIdeal_homogeneousCore_le→zFP,Insert.insert→t8,Irreducible→Sv,IsCoprime→xI,IsDomain→G2,IsFractionRing.injective→xL,IsLeftCancelMulZero.mul_left_cancel_of_ne_zero→zUH,IsLocalRing→PM,IsLocalRing.maximalIdeal→ oD,IsLocalRing.maximalIdeal.isMaximal→zHl,IsLocalization.AtPrime.isUnit_to_map_iff→z7L,IsLocalization.AtPrime.map_eq_maximalIdeal→zNE,IsLocalization.AtPrime.to_map_mem_maximal_iff→zRt,IsLocalization.algebraMap_mem_map_algebraMap_iff→zZS,IsLocalization.exists_mk'_eq→zcf,IsLocalization.isPrime_of_isPrime_disjoint→PD,IsLocalization.lift→QL,IsLocalization.lift_eq→NZ,IsLocalization.map_units→z0j,IsLocalization.mk'→zzm,IsLocalization.mk'_spec→zOg,IsLocalization.orderEmbedding→zRW,IsLocalization.ringHom_ext→zuW,IsLocalization.under_map_of_isPrime_disjoint→ztT,IsNoetherianRing→MS,IsSMulRegular→wY,IsScalarTower.algebraMap_eq→zYY,IsScalarTower.of_algebraMap_eq→zsL,IsUnit→vl,LinearEquiv.ofBijective→zD9,LinearMap.ker→uJ,LinearMap.mem_ker→Kz
open _root_ renaming LinearMap.range→Dw,LinearMap.range_domRestrict→zyK,LinearOrder.lift'→zEZ,Localization.AtPrime→Au,Localization.localRingHom_to_map→zMs,Module.Finite→Hw,Module.finrank→G1,Module.finrank_eq_nat_card_basis→zUF,Module.finrank_eq_zero_of_subsingleton→z6g,Module.length→qm,Module.length_eq_add_of_exact→ziu,Module.length_eq_finrank→z1C,Module.length_le_of_injective→zdt,Module.length_le_of_surjective→VS,ModuleCat.of→Kh,MonomialOrder→FR,MonomialOrder.degLex→zwf,MvPolynomial→nX,MvPolynomial.C→nq,MvPolynomial.IsWeightedHomogeneous.mul→JK,MvPolynomial.X→lV,MvPolynomial.affineHilbertFunction→Qy,MvPolynomial.affineHilbertPolynomial→yl,MvPolynomial.algHom_ext→Zf,MvPolynomial.basisRestrictSupport→zzc,MvPolynomial.coeff_eq_zero_of_totalDegree_lt→Xp,MvPolynomial.eval→p5,MvPolynomial.eval_C→FQ,MvPolynomial.eval_X→Gr,MvPolynomial.eval₂→z8,MvPolynomial.eval₂Hom→yB,MvPolynomial.eval₂Hom_C→NW,MvPolynomial.eval₂Hom_X'→Lf,MvPolynomial.eval₂_eq→zMm,MvPolynomial.eventually_eval_affineHilbertPolynomial→zaM,MvPolynomial.hom_eval₂→zUe,MvPolynomial.homogeneousComponent→zyc,MvPolynomial.isWeightedHomogeneous_X→Zi,MvPolynomial.le_weightedTotalDegree→z6P,MvPolynomial.map→t3,MvPolynomial.map_C→KI,MvPolynomial.map_X→G9,MvPolynomial.map_injective→zNV,MvPolynomial.mem_iff_weightedHomogeneousComponent_mem→z1h,MvPolynomial.mem_support_iff→zuk,MvPolynomial.mem_weightedHomogeneousSubmodule→Mz,MvPolynomial.monomial→qz,MvPolynomial.monomial_mul_monomial→zDU
open _root_ renaming MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective→zGE,MvPolynomial.optionEquivLeft→xu,MvPolynomial.optionEquivLeft_coeff_coeff→z9x,MvPolynomial.optionEquivRight→G4,MvPolynomial.pderiv→yQ,MvPolynomial.rename→ IT,MvPolynomial.renameEquiv_apply→zyl,MvPolynomial.rename_X→SC,MvPolynomial.restrictSupport→yJ,MvPolynomial.restrictSupport_eq_span→NI,MvPolynomial.ringHom_ext→Ea,MvPolynomial.support_weightedHomogeneousComponent→z66,MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt→ztH,MvPolynomial.weightedHomogeneousComponent→Ar,MvPolynomial.weightedHomogeneousComponent_eq_self→XG,MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous→zmP,MvPolynomial.weightedHomogeneousComponent_mem→zbF,MvPolynomial.weightedHomogeneousComponent_mem_of_mem→MK,MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported→zSq,MvPolynomial.weightedTotalDegree_mul_le→Eg,MvPolynomial.weightedTotalDegree_pderiv_le_sub→zYB,MvPolynomial.weightedTotalDegree_zero→z4a,MvPolynomial.zeroLocus→VO,Nat.add_le_add→zk,Nat.add_le_add_left→R9,Nat.add_mul→UY,Nat.add_sub_cancel_left→z7K,Nat.add_sub_of_le→GR,Nat.card_coe_set_eq→JM,Nat.card_congr→Nj,Nat.card_eq_fintype_card→XB,Nat.cast_mul→RD,Nat.cast_sum→SU,Nat.le_add_left→Pv,Nat.le_add_right→zi,Nat.le_of_lt_succ→Ef,Nat.lt_succ_of_le→SM,Nat.mul_le_mul_left→qU,Nat.mul_left_comm→WK,Nat.mul_pos→WY,Nat.multichoose_eq→z4m,Nat.multichoose_zero_succ→zGT,Nat.ne_of_gt→SD,Nat.nsmul_eq_mul→UZ,Nat.pos_of_ne_zero→Nq,Nat.sub_add_cancel→zxt,Nat.sub_le_sub_right→zIu,Nat.zero_le→ In
open _root_ renaming Or.inl→Gi,Pi.add_apply→Vq,Pi.single_eq_of_ne→Ye,Polynomial→zR,Polynomial.Bivariate.swap→zd,Polynomial.C→lI,Polynomial.X→ oj,Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd→zff,Polynomial.algebraMap_eq→Zt,Polynomial.coe_eval₂RingHom→x7,Polynomial.coe_mapRingHom→yo,Polynomial.coeff_C_mul_X_pow→zds,Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le→zKB,Polynomial.coeff_map→zg,Polynomial.evalRingHom→qM,Polynomial.eval_C→Te,Polynomial.eval_X→MO,Polynomial.eval_add→zvF,Polynomial.eval₂RingHom→GY,Polynomial.eval₂_C→F9,Polynomial.eval₂_X→zC9,Polynomial.eval₂_map→zem,Polynomial.eval₂_monomial→zFK,Polynomial.exists_mul_add_mul_eq_C_resultant→zKy,Polynomial.finsetSum_coeff→zaW,Polynomial.hasseDeriv→pQ,Polynomial.hasseDeriv_map→zvb,Polynomial.hasseDeriv_monomial→zKa,Polynomial.hom_eval₂→Y4,Polynomial.induction_on'→zCU,Polynomial.isUnit_resultant_iff_isCoprime→zgx,Polynomial.mapRingHom→u8,Polynomial.map_C→sS,Polynomial.map_add→z7,Polynomial.map_dvd→RP,Polynomial.map_id→Xx,Polynomial.map_map→sI,Polynomial.map_monomial→SL,Polynomial.map_mul→v8,Polynomial.map_sum→NY,Polynomial.map_taylor→zla,Polynomial.monomial→t9,Polynomial.natDegree_map_eq_of_injective→Z0,Polynomial.natDegree_map_le→RC,Polynomial.natDegree_modByMonic_lt→Yo,Polynomial.natDegree_sum_le_of_forall_le→UP,Polynomial.preHilbertPoly→zcb,Polynomial.preHilbertPoly_eq_choose_add_sub→zg1
open _root_ renaming Polynomial.ringHom_ext→C5,Polynomial.taylor→wR,PrimeSpectrum→Rm,QuotSMulTop→yL,RingHom.comap_ker→S2,RingHom.comp_apply→pU,RingHom.congr_fun→t4,RingHom.ext→xW,RingHom.id→LQ,RingHom.ker→sH,RingHom.ker_eq_comap_bot→Vz,RingHom.ker_isPrime→zgL,RingHom.mem_ker→ZK,RingTheory.Sequence.IsWeaklyRegular→P7,Set.disjoint_left→Up,Set.image_image→Vs,Set.image_insert_eq→z6c,Set.image_singleton→Cy,Set.mem_fintype_sum→RJ,Set.mem_insert_iff→zP8,Set.mem_ofPred_eq→Qx,Set.mem_zero→KH,Set.nsmul_mem_nsmul→zfk,Set.pair_comm→Yi,Set.range→Re,Set.range_eq_empty→zwy,Set.singleton_def→zrN,SetLike.exists_of_lt→zxV,Submodule→u9,Submodule.Quotient.mk_eq_zero→ziM,Submodule.add_mem→Ob,Submodule.factor_surjective→zSx,Submodule.ideal_span_singleton_smul→zQT,Submodule.inclusion→zwh,Submodule.inclusion_injective→zaX,Submodule.map_comp→z1U,Submodule.mem_colon_singleton→ztS,Submodule.mem_smul_pointwise_iff_exists→zeT,Submodule.mem_top→z8t,Submodule.quotEquivOfEq→Gn,Submodule.span_le→zKY,Submodule.sum_mem→zo3,Subsingleton→zS,Subtype.ext→pL,Subtype.val→C4,Transcendental→GF,UniqueFactorizationMonoid→LP
open _root_ renaming add_comm→NX,add_le_add→WW,add_right_comm→Kp,add_zero→G6,charP_of_injective_ringHom→XJ,congrArg→lz,finsum_eq_sum_of_fintype→zNX,inferInstance→z9,injective_iff_map_eq_zero→Un,inv_mul_cancel₀→Du,isSMulRegular_quotient_iff_mem_of_smul_mem→TH,ite_eq_right→C9,le_add_of_nonneg_right→zA2,le_antisymm→wA,le_min_iff→Xg,le_rfl→th,le_sup_left→Nr,lt_of_le_of_ne→GB,map_add→ oY,map_mul→ oz,map_natCast→Ts,map_ne_zero_iff→Bf,map_pow→vw,map_prod→JW,map_sub→Av,map_sum→u5,map_zero→p6,mem_of_isSMulRegular_quotient_of_smul_mem→Ww,min_le_left→Xo,mul_assoc→uh,mul_comm→ Iw,mul_one→Qw,nonZeroDivisors→Yc,nonZeroDivisors.ne_zero→G5
open _root_ renaming one_mul→xm,one_nsmul→Ml,one_pow→KA,one_smul→ II,ringKrullDim→EP,smul_eq_mul→LO,zero_add→Gj
set_option autoImplicit true
section
set_option maxRecDepth 12000
namespace bzr
noncomputable section
open Polynomial DdK1 aR gR ProximityPrize.Benchmark
open scoped BigOperators
private theorem bhI (Q:zR (Polynomial ao)) (i j:ℕ) :
   ((zd Q).coeff i).coeff j=(Q.coeff j).coeff i:= by
 induction Q using zCU with
 | add P Q hp hq=>simp [hp,hq]
 | monomial n P =>
   induction P using zCU with
   | add P Q hp hq=>simp only [map_add,Polynomial.coeff_add,hp,hq]
   | monomial m c =>
     rw [Bivariate.swap_monomial_monomial]
     by_cases hi:m=i <;> by_cases hj:n=j <;> simp [Polynomial.coeff_monomial,Finsupp.single_apply,hi,hj]
private theorem d2V (Q:zR (Polynomial ao)) (c:ao) :
  (zd Q).map (qM c)= Q.eval (lI c) := by
 simpa [Polynomial.aeval_def]
  using (Bivariate.aveal_eq_map_swap c Q).symm
private theorem bnl (Q:zR (Polynomial ao)) (x :ao) (r :ℕ)
   (h : ∀ c:ao,(oj - C x)^r∣Q.eval (C c)) (j:ℕ) :
   (oj - C x)^r∣Q.coeff j:= by
 let f :(Polynomial ao) →+* (Polynomial ao) :=(taylorAlgHom x).toRingHom
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
theorem cX8 (Q:zR (Polynomial ao)) (A:nI I)
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
open Polynomial DdK1 aR gR
open scoped BigOperators
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
open DdK1 cu Polynomial
end
end aqb
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace baz
noncomputable section
open cu aqb
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
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
open cu aqb Polynomial
end
end cy1
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace baz
noncomputable section
open DdK1 cu aqb
open MvPolynomial
open scoped Polynomial
end
end baz
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace baz
noncomputable section
open cu aqb
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end baz
end
section
namespace as7
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end
end as7
end
section
namespace as7
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end
end as7
end
section
namespace as7
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {A:Fin 4→Set ov} {B:Set ov}
end
end as7
end
section
namespace as7
noncomputable section
open MvPolynomial Filter
open scoped BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end
end as7
end
section
namespace bRB
noncomputable section
open as7 MvPolynomial
open scoped BigOperators Pointwise
variable {A:Fin 4→Set ov} {B:Set ov}
end
end bRB
end
section
namespace cys
open aR
open scoped BigOperators Pointwise
end cys
end
section
namespace cyt
open aR Finset
open scoped BigOperators
noncomputable section
end
end cyt
end
section
namespace cyM
noncomputable section
open aR MvPolynomial
open scoped Polynomial
end
end cyM
end
section
namespace cxQ
noncomputable section
open aR Polynomial
open scoped Polynomial
end
end cxQ
end
section
set_option maxHeartbeats 1000000
namespace cxX
noncomputable section
open aR oR we aeC MvPolynomial
open scoped BigOperators Polynomial
end
end cxX
end
section
namespace cxV
noncomputable section
open we zP aaq MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {A:Fin 4→nI vZ}
end
end cxV
end
section
namespace aKr
noncomputable section
open scoped BigOperators Function
variable {ι σ:Type} [t7 ι]
end
end aKr
end
section
namespace aKr
noncomputable section
open scoped BigOperators
variable {ι σ:Type} [t7 ι] [oK σ] {T:σ→ℕ}
end
end aKr
end
section
namespace aKr
noncomputable section
open Filter
open scoped BigOperators
variable {ι:Type} [oK ι] [t7 ι]
end
end aKr
end
section
namespace Jq
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end
end Jq
end
section
namespace cyD
noncomputable section
open Jq as7
open MvPolynomial Filter
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end
end cyD
end
section
namespace bzL
open Ideal IsLocalRing MvPolynomial RingTheory.Sequence
open CategoryTheory Abelian
open scoped Pointwise
universe u
end bzL
end
section
namespace bzL
open Ideal IsLocalRing
open scoped Pointwise
section LocalRing
variable {R:Type*} [qJ R] [MS R] [PM R]
end LocalRing
end bzL
end
section
namespace bRu
open IsDedekindDomain WithZero
open scoped WithZero
noncomputable section
variable {k L:Type} [zc k] [zc L] [yU k L] {x :L}
end
end bRu
end
section
namespace aw8
open Finset
open scoped BigOperators
set_option maxHeartbeats 1500000
end aw8
end
section
namespace bjB
noncomputable section
variable {S ι:Type} [qJ S] (P:ι→ aU S) [∀ i,(P i).IsPrime]
end
end bjB
end
section
namespace bjB
noncomputable section
end
end bjB
end
section
namespace axa
noncomputable section
open Polynomial DdK1 aR
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
end
end axa
end
section
namespace vq
noncomputable section
open DdK1 cu MN MvPolynomial
open scoped Polynomial BigOperators
end
end vq
end
section
namespace dnc
noncomputable section
open aR oR we Polynomial
open RingTheory.Sequence
open scoped Pointwise
end
end dnc
end
section
set_option maxRecDepth 1500
namespace bRq
noncomputable section
open Polynomial aR
open scoped BigOperators
end
end bRq
end
section
namespace bav
open aR
open scoped BigOperators Pointwise
end bav
end
section
namespace bav
noncomputable section
open aR MvPolynomial Filter
open scoped BigOperators
variable {ι:Type} [oK ι]
end
end bav
end
section
namespace bRd
noncomputable section
open Polynomial aR
end
end bRd
end
section
namespace as5
open Jq MvPolynomial
open scoped BigOperators
end as5
end
section
namespace bjx
noncomputable section
open aR Polynomial
open scoped Polynomial
set_option maxRecDepth 4000
end
end bjx
end
section
namespace bjx
noncomputable section
open aR Polynomial
open scoped Polynomial BigOperators Pointwise
set_option maxRecDepth 4000
end
end bjx
end
section
namespace as5
open Jq
open scoped BigOperators
end as5
end
section
namespace as5
open Jq MvPolynomial
open scoped BigOperators
section
variable {σ:Type} [oK σ] {b:σ →₀ ℕ}
end
end as5
end
section
namespace bRA
noncomputable section
open scoped Pointwise
end
end bRA
end
section
set_option backward.isDefEq.respectTransparency false
namespace cy2
noncomputable section
open cu
open scoped BigOperators
end
end cy2
end
section
namespace cyo
noncomputable section
open aR MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end
end cyo
end
section
namespace dnf
noncomputable section
open Polynomial MvPolynomial aR
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
end
end dnf
end

end Merged6967_DdA2

section Merged6967_DdA3
set_option Elab.async false



























































set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
open _root_ renaming Algebra→t6,Algebra.IsAlgebraic→G1,Algebra.IsIntegral→XB,Algebra.algebraMap→cy,Algebra.algebraMapSubmonoid→Xp,Algebra.trdeg→pL,CharP.cast_eq_zero_iff→Ok,CommRing→ ox,CommSemiring→vZ,DFunLike.congr_fun→G4,DecidableEq→Nq,Disjoint→Ea,Field→sH,Fin.addCases_left→PD,Fin.addCases_right→JQ,Fin.castLE→Nj,Fin.ext→yU,Fin.last→qx,Fin.sum_univ_three→LO,Finset→ oz,Finset.card_image_of_injective→Yo,Finset.exists_mem_eq_sup→Wl,Finset.mem_coe→qy,Finset.mem_filter→zm,Finset.mem_product→FV,Finset.mem_univ→zS,Finset.mul_sum→Dz,Finset.sum_add_distrib→wR,Finset.sum_comm→N0,Finset.sum_congr→t4,Finset.sum_eq_single→Qw,Finset.sum_eq_zero→Pf,Finset.sum_erase_add→zvm,Finset.sum_le_sum→yo,Finset.sum_le_sum_of_subset_of_nonneg→Z0,Finset.sum_mul→Qx,Finset.sum_nonneg→ZK,Finset.sup_le→yL,Finsupp.add_apply→NI,Finsupp.degree_eq_sum→Up,Finsupp.single_eq_same→Mw,Finsupp.sumFinsuppAddEquivProdFinsupp→Kv,Finsupp.weight→Du,Finsupp.weight_apply→LQ,Finsupp.weight_eq_sum→ IU,Fintype.card_fin→PA
open _root_ renaming Function.Injective→qm,Function.Surjective→zpX,Function.comp_apply→SU,Ideal→lI,Ideal.Quotient.commRing→ IT,Ideal.Quotient.eq_zero_iff_mem→SL,Ideal.Quotient.factor→Ww,Ideal.Quotient.mk→n5,Ideal.Quotient.mk_algebraMap→Wm,Ideal.Quotient.mk_surjective→uW,Ideal.Quotient.mkₐ→Sd,Ideal.Quotient.mkₐ_eq_mk→Vs,Ideal.annihilator_quotient→Df,Ideal.comap_map_mk→Kl,Ideal.height_add_one_le_of_lt_of_isPrime→Nr,Ideal.isPrime_map_quotientMk_of_isPrime→ztf,Ideal.map_span→yQ,Ideal.mem_map_of_mem→Et,Ideal.mem_span_singleton→G9,Ideal.mem_span_singleton_self→xL,Ideal.mem_span_singleton_sup→Zt,Ideal.mem_sup_left→Vq,Ideal.mem_sup_right→C9,Ideal.mk_ker→Qy,Ideal.mul_mem_left→KA,Ideal.pow_mem_pow→SM,Ideal.quotientMap→JK,Ideal.quotientMap_injective→zmq,Ideal.quotientMapₐ→zwL,Ideal.quotient_map_mkₐ→Zi,Ideal.span→c9,Ideal.span_insert→Zg,Ideal.subset_span→t9,IntermediateField.adjoin→G7,Irreducible→JW,IsAlgebraic→Hw,IsDomain→vH,IsFractionRing.injective→ze,IsLocalRing.ResidueField→Zh,IsLocalRing.maximalIdeal→RP,IsLocalRing.residue→Ze,IsLocalization→MS,IsLocalization.AtPrime.map_eq_maximalIdeal→VH,IsLocalization.algebraMap_mem_map_algebraMap_iff→XJ,IsLocalization.injective→Ml,IsLocalization.isAlgebraic→Sv,IsLocalization.isPrime_of_isPrime_disjoint→QL
open _root_ renaming IsLocalization.lift→zvq,IsLocalization.lift_eq→XG,IsLocalization.map_units→ II,IsLocalization.minimalPrimes_map→VC,IsLocalization.mk'_mem_map_algebraMap_iff→VS,IsLocalization.mul_mk'_eq_mk'_of_mul→WY,IsLocalization.surj→Zf,IsLocalization.under_map_of_isPrime_disjoint→G6,IsSMulRegular→vi,IsScalarTower.algebraMap_apply→zi,LinearMap.ker→EK,LinearMap.mem_ker→Y4,Localization.AtPrime→p9,LocalizedModule.map→UP,LocalizedModule.map_injective→ZJ,LocalizedModule.map_surjective→S2,LocalizedModule.mkLinearMap→Yi,Module.Finite→v8,Module.annihilator→FU,Module.coe_length→Ts,Module.finrank→R9,Module.length_eq_of_surjective→TZ,MulEquiv.irreducible_iff→UY,MvPolynomial→nX,MvPolynomial.C→mD,MvPolynomial.C_dvd_iff_dvd_coeff→Gi,MvPolynomial.C_injective→X8,MvPolynomial.C_mul→S1,MvPolynomial.IsWeightedHomogeneous→Ar,MvPolynomial.X→lz,MvPolynomial.aeval→pz,MvPolynomial.algebraMap_def→zu8,MvPolynomial.algebraMap_eq→zk,MvPolynomial.coeff_C_mul→ In,MvPolynomial.coeff_map→F9,MvPolynomial.coeff_monomial→ Iw,MvPolynomial.coeff_mul→GF,MvPolynomial.coeff_pderiv→Ye,MvPolynomial.coeff_sum→RC,MvPolynomial.coeff_weightedHomogeneousComponent→Vl,MvPolynomial.degreeOf_X_pow_of_ne→PM,MvPolynomial.degreeOf_add_le→G2,MvPolynomial.degreeOf_eq_sup→Gk,MvPolynomial.degreeOf_mul_le→GB,MvPolynomial.degreeOf_rename_of_injective→Xo
open _root_ renaming MvPolynomial.eval→Pc,MvPolynomial.eval₂Hom→vl,MvPolynomial.eval₂Hom_C→z7,MvPolynomial.eval₂Hom_X'→y5,MvPolynomial.ext→LP,MvPolynomial.finSuccEquiv→Fa,MvPolynomial.finSuccEquiv_apply→zyf,MvPolynomial.induction_on→JM,MvPolynomial.induction_on'→VO,MvPolynomial.le_degreeOf_of_mem_support→NZ,MvPolynomial.le_weightedTotalDegree→zh,MvPolynomial.map→p7,MvPolynomial.map_C→C5,MvPolynomial.map_rename→zoD,MvPolynomial.mem_support_iff→Dv,MvPolynomial.monomial→xu,MvPolynomial.pderiv→ oD,MvPolynomial.pderiv_mul→LR,MvPolynomial.rename→ oy,MvPolynomial.renameEquiv→Mj,MvPolynomial.rename_C→zt1,MvPolynomial.ringHom_ext→pU,MvPolynomial.trdeg_of_isDomain→Xx,MvPolynomial.weightedHomogeneousComponent→yJ,MvPolynomial.weightedHomogeneousSubmodule→Kc,MvPolynomial.weightedTotalDegree→Gj,Nat.add_zero→OJ,Nat.cast_add→zg,Nat.cast_succ→G0,Nat.eq_zero_of_le_zero→uz,Nat.le_of_dvd→NY,Nat.lt_succ_of_le→Kz,Nat.lt_succ_of_lt→Lf,Nat.lt_succ_self→NX,Nat.mul_add→Dw,Nat.mul_le_mul_left→KH,Nat.pos_of_ne_zero→WD,Nat.sub_add_cancel→HZ,Nat.zero_add→Pj,Nontrivial→xI,Or.inl→v9,Polynomial→lJ,Polynomial.Bivariate.swap→zd,Polynomial.C→lV,Polynomial.X→nq,Polynomial.coe_eval₂RingHom→SW,Polynomial.coe_mapRingHom→xW,Polynomial.coeff_C_mul→Av
open _root_ renaming Polynomial.coeff_C_mul_X→TH,Polynomial.coeff_X_mul→Xu,Polynomial.coeff_add→Kp,Polynomial.coeff_derivative→MK,Polynomial.coeff_map→vj,Polynomial.coeff_monomial→Np,Polynomial.coeff_mul_X→zwB,Polynomial.coeff_sub→zsl,Polynomial.coeff_zero→wA,Polynomial.constantCoeff→Cy,Polynomial.evalRingHom→vh,Polynomial.eval₂RingHom→zqf,Polynomial.eval₂_C→UZ,Polynomial.finsetSum_coeff→Gr,Polynomial.hasseDeriv→qM,Polynomial.hasseDeriv_map→G8,Polynomial.hom_eval₂→Bf,Polynomial.induction_on'→FK,Polynomial.mapEquiv→MO,Polynomial.mapRingHom→t7,Polynomial.map_C→RJ,Polynomial.map_eq_zero_iff→X4,Polynomial.map_map→Rm,Polynomial.ringHom_ext→EP,Polynomial.smul_eq_C_mul→WX,Polynomial.sum→P7,Polynomial.sylvester→Pk,Polynomial.taylor→u8,Polynomial.taylorEquiv→G3,PrimeSpectrum→ oj,RingHom.comp_apply→pC,RingHom.congr_fun→ oZ,RingHom.ext→SD,RingHom.id→ Il,RingHom.ker→GY,RingHom.ker_eq_comap_bot→WK,RingHom.mem_ker→xm,Set.image_insert_eq→Kh,Set.image_singleton→zf,Set.insert_subset_iff→J4,Set.singleton_subset_iff→NW,Submodule.mem_bot→Vz,Submodule.mem_colon_singleton→ztS,Subtype.ext→wY,Sum.inl→zR,Sum.inr→C4
open _root_ renaming add_comm→vw,add_le_add→Gn,add_zero→u5,charP_of_injective_ringHom→z9,congrArg→ ov,faithfulSMul_iff_algebraMap_injective→Xg,finSuccEquivLast→x7,finSuccEquivLast_last→Eg,inferInstance→Oc,injective_iff_map_eq_zero→Mz,ite_eq_left→wB,ite_eq_right→vk,le_antisymm→Ob,le_min_iff→Pr,le_rfl→sI,le_sup_left→yl,le_sup_right→G5,left_ne_zero_of_mul→Te,map_add→ oK,map_dvd_iff→FR,map_mul→nI,map_natCast→Mk,map_ofNat→GR,map_pow→p6,map_sub→qG,map_sum→vG,map_zero→qz,mul_assoc→sS,mul_comm→t3,mul_le_mul_of_nonneg_left→WW,mul_left_cancel₀→SC,mul_left_comm→Pv,mul_ne_zero→Fz,mul_nonneg→Ee,nonZeroDivisors→u9,not_le_of_gt→Aa,one_mul→Au,pow_succ→yB,smul_eq_mul→zc,sup_le→uJ
open _root_ renaming trdeg_add_eq→Ef,trdeg_eq_zero→KI,zero_add→zE
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace aez
noncomputable section
open MvPolynomial wT
variable {F:Type*} [sH F]
end
end aez
end
section
set_option backward.isDefEq.respectTransparency false
namespace aez
noncomputable section
open DdK1 BN wT MvPolynomial
end
end aez
end
section
set_option backward.isDefEq.respectTransparency false
namespace cxH
noncomputable section
open DdK1 BN aez wT MvPolynomial
end
end cxH
end
section
namespace cxI
noncomputable section
open DdK1 BN aez MvPolynomial
end
end cxI
end
section
namespace aKv
noncomputable section
open scoped BigOperators
end
end aKv
end
section
namespace bzQ
noncomputable section
open MvPolynomial
end
end bzQ
end
section
namespace aRX
noncomputable section
open aKv
open scoped Classical
end
end aRX
end
section
namespace bzQ
noncomputable section
open aKv
end
end bzQ
end
section
namespace aRX
noncomputable section
open aKv
open scoped BigOperators
end
end aRX
end
section
namespace aBb
end aBb
end
section
set_option backward.isDefEq.respectTransparency false
namespace czq
noncomputable section
open cu
open scoped Polynomial
end
end czq
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace bzX
noncomputable section
open cu
end
end bzX
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace bzX
noncomputable section
open cu
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end bzX
end
section
namespace Sy
open aR
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
noncomputable section
end
end Sy
end
section
namespace cxR
noncomputable section
open aR Polynomial
open scoped Polynomial BigOperators
end
end cxR
end
section
namespace cxO
noncomputable section
open aR Finset MvPolynomial
open scoped BigOperators
end
end cxO
end
section
namespace bjA
noncomputable section
open aR MvPolynomial
end
end bjA
end
section
set_option maxSynthPendingDepth 8
namespace bjF
noncomputable section
open cu Polynomial
end
end bjF
end
section
set_option maxSynthPendingDepth 8
namespace bjF
noncomputable section
open DdK1 cu Polynomial
end
end bjF
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace cxU
noncomputable section
open zP MvPolynomial Algebra
open scoped nonZeroDivisors
variable {A:Fin 4→ oz uh}
end
end cxU
end
section
namespace aeA
noncomputable section
open aR oR MvPolynomial
open scoped Polynomial BigOperators
def view {r :ℕ} : af (r+1) ≃ₐ[(Polynomial ao)] lJ (af r) :=
 (Mj (Polynomial ao) x7).trans (optionEquivLeft (Polynomial ao) (Fin r))
theorem biB {r :ℕ} (w:Fin (r+1)→ℕ)
    (f :af (r+1)) (k :ℕ)
    (hk :k≤(view f).natDegree) :
    ((view f).coeff k).weightedTotalDegree (fun i=>w i.castSucc) +
      w (qx r)*k≤f.weightedTotalDegree w:= by
  classical
  let w' : Option (Fin r)→ℕ:= fun i=>i.elim (w (qx r)) (fun j=>w j.castSucc)
  have hw : ∀ i:Fin (r+1),w' (x7 i)=w i:= by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [w',Eg]
  have hrename : (oy x7 f).weightedTotalDegree w' =
      f.weightedTotalDegree w:= by
    rw [Gj,Gj,support_rename_of_injective
      finSuccEquivLast.injective,Finset.sup_image]
    congr 1
    funext u
    simp only [SU,LQ,zc]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
    simp only [hw]
  have hterm (k :ℕ) (m:Fin r →₀ ℕ) (hm:m∈((view f).coeff k).support) :
      m.weight (fun i=>w i.castSucc)+w (qx r)*k≤f.weightedTotalDegree w:= by
    have hs :=(mem_support_coeff_optionEquivLeft _).mp hm
    have hle :=zh w' hs
    change _≤(oy x7 f).weightedTotalDegree w' at hle
    rw [hrename,Finsupp.weight_optionElim] at hle
    simpa only [w',Nat.add_comm,Nat.mul_comm] using hle
  have hcoeff (j:ℕ) (hj: (view f).coeff j≠0) :
      ((view f).coeff j).weightedTotalDegree (fun i=>w i.castSucc) +
        w (qx r)*j≤f.weightedTotalDegree w:= by
    obtain ⟨m,hm,hmax⟩:=Wl
      _ (support_nonempty.mpr hj) (fun m=>m.weight (fun i:Fin r=>w i.castSucc))
    rw [Gj,hmax]
    exact hterm j m hm
  by_cases hzero : (view f).coeff k=0
  · rw [hzero,weightedTotalDegree_zero,bot_eq_zero,zE]
    by_cases hf :view f=0
    · simp_all
    have h:=hcoeff _ (Polynomial.leadingCoeff_ne_zero.mpr hf)
    exact (KH _ hk).trans ((Nat.le_add_left _ _).trans h)
  · exact hcoeff k hzero
def elimination {r :ℕ} (f :af (r+1)) :af r :=
 let F:=view f
 let c:=F.natDegree
 if c=0 then F.coeff 0 else F.resultant F.derivative c (c - 1)
end
end aeA
end
section
namespace aeA
noncomputable section
open aR MvPolynomial
open scoped Polynomial BigOperators
private theorem fXo {r :ℕ} (w:Fin r→ℕ) (a :ℕ)
    (P Q:lJ (af r)) (m n B D:ℕ)
    (hP : ∀ i≤ m,(P.coeff i).weightedTotalDegree w+a*i≤B)
    (hQ : ∀ i≤n,(Q.coeff i).weightedTotalDegree w+a*i≤D) :
    (P.resultant Q m n).weightedTotalDegree w+a*(m*n)≤n*B+m*D:= by
  classical
  let M:=Pk P Q m n
  let W:Fin (m+n)→ℕ :=
    Fin.addCases (fun j:Fin m=>D + a*j.val) (fun j:Fin n=>B+a*j.val)
  have hentry (σ:Equiv.Perm (Fin (m+n))) (i:Fin (m+n))
      (hne :M (σ i) i≠0) :
      (M (σ i) i).weightedTotalDegree w+a*(σ i).val≤W i:= by
    cases i using Fin.addCases with
    | left j =>
      simp only [M,Pk,Matrix.of_apply,PD] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hj:j.val≤(σ (j.castAdd n)).val :=h.1
        have hh:=hQ ((σ (j.castAdd n)).val - j.val) (by have :=h.2; omega)
        simp only [W,PD]
        have hid :a*((σ (j.castAdd n)).val - j.val)+a*j.val =
            a*(σ (j.castAdd n)).val := by rw [← Dw ,HZ hj]
        omega
      · exact absurd rfl hne
    | right j =>
      simp only [M,Pk,Matrix.of_apply,JQ] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hj:j.val≤(σ (j.natAdd m)).val :=h.1
        have hh:=hP ((σ (j.natAdd m)).val - j.val) (by have :=h.2; omega)
        simp only [W,JQ]
        have hid :a*((σ (j.natAdd m)).val - j.val)+a*j.val =
            a*(σ (j.natAdd m)).val := by rw [← Dw ,HZ hj]
        omega
      · exact absurd rfl hne
  let S:=(∑ j:Fin m,a*j.val) + ∑ j:Fin n,a*j.val
  have hW : ∑ i,W i=m*D + n*B+S:= by
    simp only [W,S,Fin.sum_univ_add,PD,JQ,
      wR,Finset.sum_const,Finset.card_univ,PA,zc]
    ring
  have hsum : ∑ i:Fin (m+n),a*i.val=a*(m*n)+S:= by
    simp only [S,Fin.sum_univ_add,Fin.val_castAdd,Fin.val_natAdd,Dw ,
      wR,Finset.sum_const,Finset.card_univ,PA,zc]
    ring
  have hbase :a*(m*n)≤n*B:= by
    rw [show a*(m*n)=n*(a*m) by ring]
    exact KH n ((Nat.le_add_left _ _).trans (hP m sI))
  have hterm (σ:Equiv.Perm (Fin (m+n))) :
      (∏ i,M (σ i) i).weightedTotalDegree w≤n*B+m*D - a*(m*n) := by
    by_cases hz : ∃ i,M (σ i) i=0
    · obtain ⟨i,hi⟩:=hz
      have hp: (∏ j,M (σ j) j)=0:=Finset.prod_eq_zero (zS i) hi
      rw [hp,weightedTotalDegree_zero]
      exact Nat.zero_le _
    · simp only [not_exists] at hz
      rw [weightedTotalDegree_prod _ _ _ (fun i _=>hz i)]
      have h:=yo (s :=Finset.univ) (fun i _=>hentry σ i (hz i))
      rw [wR,Equiv.sum_comp σ (fun i=>a*i.val),hW,hsum] at h
      omega
  have hdet:M.det.weightedTotalDegree w≤n*B+m*D - a*(m*n) := by
    rw [Matrix.det_apply]
    refine AddMonoidAlgebra.supDegree_sum_le.trans (yL fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs,one_smul]
      exact hterm σ
    · have hsign:Equiv.Perm.sign σ•(∏ i,M (σ i) i) = -(∏ i,M (σ i) i) := by
        simp [hs]
      rw [hsign,AddMonoidAlgebra.supDegree_neg]
      exact hterm σ
  change M.det.weightedTotalDegree w+a*(m*n)≤_
  omega
private theorem dMl {r :ℕ} (w:Fin r→ℕ) (P:lJ (af r))
  (i:ℕ) :
  (P.derivative.coeff i).weightedTotalDegree w≤(P.coeff (i+1)).weightedTotalDegree w:= by
 rw [MK,← G0 ,← Mk (mD:(Polynomial ao) →+* af r)]
 exact (weightedTotalDegree_mul_le _ _ _).trans (by rw [weightedTotalDegree_C,OJ])
theorem cLz {r :ℕ} (w:Fin (r+1)→ℕ)
   (f :af (r+1)) (hc:0<(view f).natDegree) :
   let c:=(view f).natDegree
   (elimination f).weightedTotalDegree (fun i=>w i.castSucc) +
     w (qx r)*c^2≤(2*c - 1)*f.weightedTotalDegree w:= by
 let A:=view f
 let a :=w (qx r)
 let v :Fin r→ℕ:= fun i=>w i.castSucc
 let B:=f.weightedTotalDegree w
 change 0<A.natDegree at hc
 obtain ⟨k,hk⟩ : ∃ k,A.natDegree=k+1 :=
   ⟨A.natDegree - 1,by omega⟩
 have hA : ∀ i≤k+1,(A.coeff i).weightedTotalDegree v+a*i≤B :=
   fun i hi=>biB w f i (by rwa [hk])
 have hab:a≤B:= by
   have htop:=hA (k+1) sI
   rw [Dw ,Nat.mul_one] at htop
   omega
 obtain ⟨d,hd⟩:=Nat.exists_eq_add_of_le hab
 have hD : ∀ i≤k,(A.derivative.coeff i).weightedTotalDegree v+a*i≤d:= by
   intro i hi
   have h:=hA (i+1) (by omega)
   rw [Dw ,Nat.mul_one,hd] at h
   have h' := dMl v A i
   omega
 have h:=fXo v a A A.derivative (k+1) k B d hA hD
 have hEq:elimination f=A.resultant A.derivative (k+1) k := by
   change (if A.natDegree=0 then A.coeff 0
     else A.resultant A.derivative A.natDegree (A.natDegree - 1))= _
   simp [hk]
 have hR: (2*(k+1) - 1)*B=k*B+(k+1)*d+(k+1)*a := by
   rw [show 2*(k+1) - 1=2*k+1 by omega,hd]
   ring
 have hL:a*(k+1)^2=a*((k+1)*k)+(k+1)*a := by ring
 change (elimination f).weightedTotalDegree v+a*A.natDegree^2≤(2*A.natDegree - 1)*B
 rw [hk,hEq,hL,hR]
 omega
theorem cLA {r :ℕ} (w:Fin (r+1)→ℕ)
  (f :af (r+1)) (hc: (view f).natDegree=0) :
  (elimination f).weightedTotalDegree (fun i=>w i.castSucc)≤f.weightedTotalDegree w:= by
 simpa [elimination,hc] using biB w f 0 (Nat.zero_le _)
end
end aeA
end
section
namespace aeA
noncomputable section
open scoped BigOperators
end
end aeA
end
section
namespace dm8
noncomputable section
open aR oR we aA1
open MvPolynomial
open scoped Polynomial
end
end dm8
end
section
namespace dm6
noncomputable section
open DdK1 aR
open scoped Polynomial BigOperators
end
end dm6
end
section
namespace dnb
noncomputable section
open aR oR we yz aA2 MvPolynomial
end
end dnb
end
section
namespace cyA
open aR Polynomial
open scoped Polynomial WithZero
end cyA
end
section
set_option backward.isDefEq.respectTransparency false
namespace bju
noncomputable section
open MvPolynomial
variable {F:Type*} [sH F]
end
end bju
end
section
namespace baD
open Polynomial
end baD
end

end Merged6967_DdA3

section Merged6967_Pack_K1_14_3_2_7Proof
set_option Elab.async false



set_option Elab.async false

-- merged module Numeric6Defs
section Merged_Numeric6Defs
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6
open scoped BigOperators
open CJ0 (Jet blockRows blockCols blockMatrix)
open CJ1 (total total_eq_sum)
private theorem row_bounds (q u c d h : ℕ)
    (hr : (⟨c,d,h⟩ : Jet) ∈ blockRows 52 q ((u : ℤ)-20)) :
    h < q+1 ∧ rowLo q u h ≤ d ∧ d < rowHi q u h ∧ q-(h+d) = c := by
  simp only [blockRows, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
    Finset.mem_singleton, Jet.v, Jet.b, Jet.c, Jet.a, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hr
  unfold rowLo rowHi
  omega
private theorem col_bounds (q u c b a : ℕ)
    (hs : (⟨c,b,a⟩ : Jet) ∈ blockCols source q ((u : ℤ)-20)) :
    b < min q 20 + 1 ∧ colLo u b ≤ c ∧ c < colHi q b ∧ q-(b+c) = a := by
  change (⟨c,b,a⟩ : Jet) ∈ (CJ0.fullBox 71 20 9).filter _ at hs
  rw [Finset.mem_filter, CJ0.mem_fullBox (by decide) (by decide)] at hs
  simp only [Jet.q, Jet.v, Jet.a, Jet.b, Jet.c, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hs
  unfold colLo colHi
  omega
private def rowIndex (q u : ℕ) :
    ↥(blockRows 52 q ((u : ℤ)-20)) → Row q u
  | ⟨⟨c,d,h⟩, hr⟩ =>
    let H := row_bounds q u c d h hr
    ⟨⟨h,H.1⟩, ⟨d-rowLo q u h, by
      change d - rowLo q u h < rowHi q u h - rowLo q u h
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private def colIndex (q u : ℕ) :
    ↥(blockCols source q ((u : ℤ)-20)) → Col q u
  | ⟨⟨c,b,a⟩, hs⟩ =>
    let H := col_bounds q u c b a hs
    ⟨⟨b,H.1⟩, ⟨c-colLo u b, by
      change c - colLo u b < colHi q b - colLo u b
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private theorem rowJet_index (q u : ℕ) (r : ↥(blockRows 52 q ((u : ℤ)-20))) :
    rowJet q u (rowIndex q u r) = r.val := by
  rcases r with ⟨⟨c,d,h⟩,hr⟩
  obtain ⟨_, hlo, _, hc⟩ := row_bounds q u c d h hr
  change (⟨q-(h+(rowLo q u h+(d-rowLo q u h))),rowLo q u h+(d-rowLo q u h),h⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, hc]
private theorem colJet_index (q u : ℕ) (s : ↥(blockCols source q ((u : ℤ)-20))) :
    colJet q u (colIndex q u s) = s.val := by
  rcases s with ⟨⟨c,b,a⟩,hs⟩
  obtain ⟨_, hlo, _, ha⟩ := col_bounds q u c b a hs
  change (⟨colLo u b+(c-colLo u b),b,q-(b+(colLo u b+(c-colLo u b)))⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, ha]
theorem block_rank_le (q u : ℕ) :
    (blockMatrix source q ((u : ℤ)-20)).rank ≤ (packet q u).rank := by
  have he : blockMatrix source q ((u : ℤ)-20) =
      (packet q u).submatrix (rowIndex q u) (colIndex q u) := by
    ext r s
    change CJ0.blockEntry r.val s.val =
      CJ0.blockEntry (rowJet q u (rowIndex q u r)) (colJet q u (colIndex q u s))
    exact congrArg₂ CJ0.blockEntry (rowJet_index q u r).symm (colJet_index q u s).symm
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _
theorem card_row (q u : ℕ) : Fintype.card (Row q u) = rows q u := by
  simp only [Row, Fintype.card_sigma, Fintype.card_fin, rows, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
theorem card_col (q u : ℕ) : Fintype.card (Col q u) = cols q u := by
  simp only [Col, Fintype.card_sigma, Fintype.card_fin, cols, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
end CJ6
end
section
namespace CJ6.Packed
open Polynomial
open scoped Polynomial
theorem digit_eval (F : (Polynomial ℕ)) (B n : ℕ) (h : F.eval 1 < B) :
    F.eval B / B^n % B = F.coeff n := by
  have decomp (P : (Polynomial ℕ)) (x : ℕ) : P.eval x = P.coeff 0 + x * P.divX.eval x := by
    simpa [add_comm] using (congrArg (eval x) (X_mul_divX_add P)).symm
  induction n generalizing F with
  | zero =>
    have hh := decomp F 1
    simp only [one_mul] at hh
    have hh' : F.coeff 0 < B := by omega
    simp [decomp F B, Nat.mod_eq_of_lt hh']
  | succ n ih =>
    have hh := decomp F 1
    simp only [one_mul] at hh
    have h₀ : F.coeff 0 < B := by omega
    have hd : F.divX.eval 1 < B := by omega
    have hb : 0 < B := by omega
    rw [pow_succ', ← Nat.div_div_eq_div_mul, decomp F B, Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt h₀, zero_add, ih _ hd, coeff_divX]
def signWeight (c w : ℕ) : ℕ :=
  if c % 2 = 0 then w else (CJ0.p - 1) * w
private theorem signWeight_cast (c w : ℕ) :
    (signWeight c w : ZMod CJ0.p) = (-1)^c * (w : ZMod CJ0.p) := by
  have hp : ((CJ0.p-1 : ℕ) : ZMod CJ0.p) = -1 := by
    rw [Nat.cast_sub (by decide : 1 ≤ CJ0.p), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have parity : (-1 : ZMod CJ0.p)^c = (-1)^(c%2) := by
    conv_lhs => rw [← Nat.mod_add_div c 2, pow_add, pow_mul]
    simp
  rw [parity]
  by_cases h : c % 2 = 0
  · simp [signWeight, h]
  · have h' : c % 2 = 1 := by omega
    rw [signWeight, if_neg h, Nat.cast_mul, hp, h', pow_one]
def shift (left : Bool) (q b : ℕ) : ℕ := if left then q-b else b
def slice (left : Bool) (outA inA : ℕ) : ℕ × ℕ :=
  if left then (outA,inA) else (inA,outA)
noncomputable def piece (left : Bool) (outA inA pos w : ℕ) : (Polynomial ℕ) :=
  let (a,h) := slice left outA inA
  C (CJ1.fastChoose a h * w) * (1+(Polynomial.X : Polynomial ℕ))^(a-h) * (Polynomial.X : Polynomial ℕ)^pos
def factor (left : Bool) (x outA inA : ℕ) : ℕ :=
  let (a,h) := slice left outA inA
  CJ1.fastChoose a h * (1+x)^(a-h)
theorem eval_piece (left : Bool) (outA inA pos w x : ℕ) :
    (piece left outA inA pos w).eval x = factor left x outA inA * (w * x^pos) := by
  cases left <;> simp [piece, slice, factor] <;> ring
private theorem fastChoose_eq (n k : ℕ) : CJ1.fastChoose n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm
theorem coeff_entry (left : Bool) (q : ℕ) (o v : CJ0.Jet) (w : ℕ)
    (ho : o.q = q) (hv : v.q = q) :
    (((piece left o.a v.a (shift left q v.b) (signWeight v.c w)).coeff
        (shift left q o.b) : ℕ) : ZMod CJ0.p) =
      (-1)^(o.c) * (((if left then CJ1.entryZ v o else CJ1.entryZ o v : ℤ) : ZMod CJ0.p)) * w := by
  have aux (r c : CJ0.Jet) (hr : r.q = q) (hc : c.q = q) :
      (if c.b ≤ r.b then c.a.choose r.a * (c.a-r.a).choose (r.b-c.b) else 0) =
      (if c.b ≤ r.b ∧ c.c ≤ r.c ∧ r.a + (r.b-c.b) + (r.c-c.c) = c.a then
        c.a.choose r.a * (c.a-r.a).choose (r.b-c.b) else 0) := by
    unfold CJ0.Jet.q at hr hc
    split_ifs with hb hcond
    · rfl
    · by_cases ha : c.a < r.a
      · simp [Nat.choose_eq_zero_of_lt ha]
      · have hbad : c.a-r.a < r.b-c.b := by omega
        simp [Nat.choose_eq_zero_of_lt hbad]
    · omega
    · rfl
  have sign (r c : ℕ) (hc : c ≤ r) :
      (-1 : ZMod CJ0.p)^r * (-1)^(r-c) = (-1)^c := by
    conv_lhs => lhs; rw [← Nat.sub_add_cancel hc, pow_add]
    have h : (-1 : ZMod CJ0.p)^(r-c) * (-1)^(r-c) = 1 := by
      rw [← mul_pow]; simp
    calc
      _ = ((-1 : ZMod CJ0.p)^(r-c) * (-1)^(r-c)) * (-1)^c := by ring
      _ = _ := by rw [h, one_mul]
  have sign' (r c : ℕ) (hc : c ≤ r) :
      (-1 : ZMod CJ0.p)^c * (-1)^(r-c) = (-1)^r := by
    rw [← pow_add, Nat.add_sub_of_le hc]
  have scalar (r c : CJ0.Jet) (hr : r.q = q) (hc : c.q = q) (s t : ℕ)
      (hs : c.c ≤ r.c → (-1 : ZMod CJ0.p)^s * (-1)^(r.c-c.c) = (-1)^t) :
      ((if c.b ≤ r.b then c.a.choose r.a * signWeight t w * (c.a-r.a).choose (r.b-c.b)
          else 0 : ℕ) : ZMod CJ0.p) = (-1)^s * (CJ1.entryZ r c : ZMod CJ0.p) * w := by
    have pull : (if c.b ≤ r.b then c.a.choose r.a * signWeight t w * (c.a-r.a).choose (r.b-c.b)
          else 0) = (if c.b ≤ r.b then c.a.choose r.a * (c.a-r.a).choose (r.b-c.b)
          else 0) * signWeight t w := by split <;> ring
    rw [pull, aux r c hr hc, CJ1.entryZ]
    split_ifs with hg
    · simp only [Nat.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
          Int.cast_natCast, signWeight_cast, fastChoose_eq, ← hs hg.2.1]
      ring
    · simp
  have hob : o.b ≤ q := by unfold CJ0.Jet.q at ho; omega
  have hvb : v.b ≤ q := by unfold CJ0.Jet.q at hv; omega
  cases left <;> simp only [piece, slice, shift, Bool.false_eq_true,
    ite_false, ite_true, coeff_mul_X_pow', coeff_C_mul, coeff_one_add_X_pow, Nat.cast_id, fastChoose_eq]
  · exact scalar o v ho hv o.c v.c (sign o.c v.c)
  · simp only [show (q-v.b ≤ q-o.b) ↔ o.b ≤ v.b by omega,
      show q-o.b-(q-v.b) = v.b-o.b by omega]
    exact scalar v o hv ho o.c v.c (sign' v.c o.c)
end CJ6.Packed
end
section
namespace CJ6.Packed
open Polynomial
abbrev Input := CJ0.Jet × ℕ
abbrev Bucket := ℕ × ℕ × ℕ
abbrev Band := ℕ × List ℕ
def radix : ℕ := 2^192
def insert (a s v : ℕ) : List Bucket → List Bucket
  | [] => [(a,s,v)]
  | (k,t,w)::bs => if a = k then (k,s+t,v+w)::bs else (k,t,w)::insert a s v bs
def pack (left : Bool) (q : ℕ) : List Input → List Bucket
  | [] => []
  | (j,w)::xs =>
    let v := signWeight j.c w
    insert j.a v (v * radix^(shift left q j.b)) (pack left q xs)
def value (big : Bool) (f : ℕ → ℕ) : List Bucket → ℕ
  | [] => 0
  | (a,s,v)::bs => f a * (if big then v else s) + value big f bs
private theorem value_insert (big : Bool) (f : ℕ → ℕ) (a s v : ℕ) (bs : List Bucket) :
    value big f (insert a s v bs) = f a * (if big then v else s) + value big f bs := by
  induction bs with
  | nil => simp [insert, value]
  | cons b bs ih =>
    obtain ⟨k,t,w⟩ := b
    by_cases h : a = k <;> cases big <;> simp [insert, value, h, ih, Nat.mul_add] <;> omega
noncomputable def poly (left : Bool) (q outA : ℕ) : List Input → Polynomial ℕ
  | [] => 0
  | (j,w)::xs => piece left outA j.a (shift left q j.b) (signWeight j.c w) + poly left q outA xs
theorem value_pack (big left : Bool) (q a : ℕ) (xs : List Input) :
    value big (factor left (if big then radix else 1) a) (pack left q xs) =
      (poly left q a xs).eval (if big then radix else 1) := by
  induction xs with
  | nil => simp [poly, pack, value]
  | cons v xs ih =>
    obtain ⟨j,w⟩ := v
    simp only [pack, poly, value_insert, eval_add, ih, eval_piece]
    cases big <;> simp
def checkBand (left : Bool) (bs : List Bucket) (band : Band) : Bool :=
  let a := band.1
  let s := value false (factor left 1 a) bs
  let v := value true (factor left radix a) bs
  decide (s < radix) && band.2.all (fun t => v / radix^t % radix % CJ0.p == 0)
theorem band_sound {left : Bool} {q : ℕ} {xs : List Input} {bands : List Band}
    (h : bands.all (checkBand left (pack left q xs)) = true)
    {a t : ℕ} (hm : ∃ b ∈ bands, b.1 = a ∧ t ∈ b.2) :
    (poly left q a xs).coeff t % CJ0.p = 0 := by
  obtain ⟨⟨a',ts⟩, hb, rfl, ht⟩ := hm
  have hb' := List.all_eq_true.mp h _ hb
  simp only [checkBand, Bool.and_eq_true, decide_eq_true_eq] at hb'
  have h₁ := value_pack false left q a' xs
  have h₂ := value_pack true left q a' xs
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
  obtain ⟨hsize, hd⟩ := hb'
  have ht' := List.all_eq_true.mp hd _ ht
  simp only [beq_iff_eq] at ht'
  rw [h₁] at hsize
  rwa [h₂, digit_eval _ _ _ hsize] at ht'
def covers (left : Bool) (q : ℕ) (bands : List Band) (j : CJ0.Jet) : Bool :=
  j.q == q && bands.any (fun b => b.1 == j.a && b.2.contains (shift left q j.b))
def axisList {α : Type} (n : ℕ) (len : ℕ → ℕ) (f : ℕ → ℕ → α) : List α :=
  (List.range n).flatMap (fun i => (List.range (len i)).map (f i))
theorem mem_axis {α : Type} {n : ℕ} {len : ℕ → ℕ} {f : ℕ → ℕ → α}
    {i k : ℕ} (hi : i < n) (hk : k < len i) : f i k ∈ axisList n len f := by
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩
theorem sum_axis {α M : Type} [AddCommMonoid M] (g : α → M)
    (n : ℕ) (len : ℕ → ℕ) (f : ℕ → ℕ → α) :
    ((axisList n len f).map g).sum =
      CJ1.total (fun i => CJ1.total (fun k => g (f i k)) (len i)) n := by
  have inner (i m : ℕ) : (((List.range m).map (f i)).map g).sum =
      CJ1.total (fun k => g (f i k)) m := by
    induction m with
    | zero => rfl
    | succ m ih => simpa only [List.range_succ, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, CJ1.total] using (congrArg (· + g (f i m)) ih)
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [axisList, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, List.sum_append, inner, CJ1.total]
    exact congrArg (· + _) ih
def intTerm (left : Bool) (o : CJ0.Jet) (vw : Input) : ℤ :=
  (if left then CJ1.entryZ vw.1 o else CJ1.entryZ o vw.1) * (vw.2 : ℤ)
theorem coeff_sum (left : Bool) (q : ℕ) (o : CJ0.Jet) (xs : List Input) (ho : o.q = q)
    (hx : ∀ v ∈ xs, v.1.q = q) :
    (((poly left q o.a xs).coeff (shift left q o.b) : ℕ) : ZMod CJ0.p) =
      (-1)^o.c * (((xs.map (intTerm left o)).sum : ℤ) : ZMod CJ0.p) := by
  induction xs with
  | nil => simp [poly]
  | cons v xs ih =>
    obtain ⟨j,w⟩ := v
    rw [poly, coeff_add, Nat.cast_add, coeff_entry left q o j w ho (hx (j,w) (by simp)),
      ih (fun v hv => hx v (by simp [hv]))]
    simp only [List.map_cons, List.sum_cons, Int.cast_add, intTerm, Int.cast_mul,
      Int.cast_natCast, mul_add, mul_assoc]
theorem int_sum_zero {left : Bool} {q : ℕ} {o : CJ0.Jet} {xs : List Input} {bands : List Band}
    (hi : xs.all (fun v => v.1.q == q) = true)
    (hc : covers left q bands o = true)
    (hb : bands.all (checkBand left (pack left q xs)) = true) :
    (xs.map (intTerm left o)).sum % (CJ0.p : ℤ) = 0 := by
  simp only [covers, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem] at hc
  have hz := band_sound hb hc.2
  have hcast : (((poly left q o.a xs).coeff (shift left q o.b) : ℕ) : ZMod CJ0.p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hz)
  rw [coeff_sum left q o xs hc.1 (fun v hv => beq_iff_eq.mp (List.all_eq_true.mp hi v hv))] at hcast
  have hu : IsUnit ((-1 : ZMod CJ0.p)^o.c) := (isUnit_one.neg).pow _
  have hzero := hu.mul_right_eq_zero.mp hcast
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero)
end CJ6.Packed
end
section
namespace CJ6
open CJ1 (Block total total_eq_sum fastChoose entryZ right_witness)
open scoped BigOperators
local instance : Fact (Nat.Prime CJ0.p) := ⟨KoalaBear.is_prime⟩
def Guard (q u : ℕ) (z : Block) : Prop :=
  total (fiber z.bank.onRows q u) (outer z.bank.onRows q) ≤ z.cap + z.free.length ∧
  (∀ j : Fin z.free.length,
    z.free[j].1 < outer z.bank.onRows q ∧
    z.free[j].2 < fiber z.bank.onRows q u z.free[j].1) ∧
  ∀ j k : Fin z.free.length, z.coeff k z.free[j].1 z.free[j].2 = if j = k then 1 else 0
instance (q u : ℕ) (z : Block) : Decidable (Guard q u z) := by
  unfold Guard
  infer_instance
private theorem entryZ_cast (r c : CJ0.Jet) : (entryZ r c : ZMod CJ0.p) = CJ0.blockEntry r c := by
  unfold entryZ CJ0.blockEntry
  split <;> simp [fastChoose, ← Nat.choose_eq_descFactorial_div_factorial, *]
private def oriented (side : Bool) (q u : ℕ) :
    Matrix (Axis (!side) q u) (Axis side q u) (ZMod CJ0.p) :=
  fun r c => (orientedEntry side q u r.1 r.2 c.1 c.2 : ZMod CJ0.p)
private theorem oriented_rank (side : Bool) (q u : ℕ) :
    (oriented side q u).rank = (packet q u).rank := by
  cases side
  · have he : oriented false q u = packet q u := by
      ext r c
      exact entryZ_cast _ _
    rw [he]
    rfl
  · have he : oriented true q u = (packet q u).transpose := by
      ext r c
      exact entryZ_cast _ _
    rw [he]
    exact Matrix.rank_transpose _
private def vectors (q u : ℕ) (z : Block) :
    Matrix (Axis z.bank.onRows q u) (Fin z.free.length) (ZMod CJ0.p) :=
  fun c j => (z.coeff j c.1 c.2 : ZMod CJ0.p)
private theorem sum_axis {α : Type*} [AddCommMonoid α] (side : Bool) (q u : ℕ) (f : ℕ → ℕ → α) :
    (∑ x : Axis side q u, f x.1 x.2) =
      total (fun i => total (f i) (fiber side q u i)) (outer side q) := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma, total_eq_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [total_eq_sum, ← Fin.sum_univ_eq_sum_range]
private theorem mul_eq_dot (q u : ℕ) (z : Block) (r : Axis (!z.bank.onRows) q u)
    (j : Fin z.free.length) :
    (oriented z.bank.onRows q u * vectors q u z) r j = (dot q u z j r.1 r.2 : ZMod CJ0.p) := by
  rw [Matrix.mul_apply, dot, ← sum_axis, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro c _
  change (orientedEntry z.bank.onRows q u r.1 r.2 c.1 c.2 : ZMod CJ0.p) * (z.coeff j c.1 c.2 : ZMod CJ0.p) = _
  by_cases hh : z.coeff j c.1 c.2 = 0 <;> simp [hh]
theorem rank_of_dots {q u : ℕ} {z : Block} (hg : Guard q u z) (hd : Dots q u z) :
    (packet q u).rank ≤ z.cap := by
  obtain ⟨hsize, hfree, hid⟩ := hg
  let f (j : Fin z.free.length) : Axis z.bank.onRows q u :=
    ⟨⟨z.free[j].1,(hfree j).1⟩, ⟨z.free[j].2,(hfree j).2⟩⟩
  have hm : oriented z.bank.onRows q u * vectors q u z = 0 := by
    ext r j
    rw [mul_eq_dot, Matrix.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_of_emod_eq_zero (hd j j.isLt r.1 r.1.isLt r.2 r.2.isLt)
  have hi : (vectors q u z).submatrix f id = 1 := by
    ext j k
    change (z.coeff k z.free[j].1 z.free[j].2 : ZMod CJ0.p) = _
    rw [hid]
    by_cases h : j = k <;> simp [Matrix.one_apply, h]
  have hr := right_witness (oriented z.bank.onRows q u) (vectors q u z) f hm hi
  have hc (side : Bool) :
      Fintype.card (Axis side q u) = total (fiber side q u) (outer side q) := by
    cases side
    · exact card_col q u
    · exact card_row q u
  rw [hc, oriented_rank] at hr
  exact Nat.le_of_add_le_add_right (hr.trans hsize)
end CJ6
end
section
namespace CJ6.Fast
open CJ6 (rowAt colAt outer fiber dot VectorDots orientedEntry)
open CJ1 (Block total)
open CJ6.Packed
def point (row : Bool) (q u i k : ℕ) : CJ0.Jet := if row then rowAt q u i k else colAt q u i k
def inputs (q u : ℕ) (z : Block) (j : ℕ) : List Input :=
  axisList (outer z.bank.onRows q) (fiber z.bank.onRows q u)
    (fun i k => (point z.bank.onRows q u i k, z.coeff j i k))
def outputs (q u : ℕ) (z : Block) : List CJ0.Jet :=
  axisList (outer (!z.bank.onRows) q) (fiber (!z.bank.onRows) q u) (point (!z.bank.onRows) q u)
private theorem dot_eq (q u : ℕ) (z : Block) (j i k : ℕ) :
    dot q u z j i k = ((inputs q u z j).map (intTerm z.bank.onRows (point (!z.bank.onRows) q u i k))).sum := by
  rw [inputs, CJ6.Packed.sum_axis, dot]
  congr 1
  funext b
  congr 1
  funext t
  by_cases h : z.coeff j b t = 0
  · simp [h, intTerm]
  · cases hs : z.bank.onRows <;> simp [h, intTerm, point, orientedEntry]
theorem vector {q u : ℕ} {z : Block} {j : ℕ} (bands : List Band) (bs : List Bucket)
    (hi : (inputs q u z j).all (fun v => v.1.q == q) = true)
    (hc : (outputs q u z).all (covers z.bank.onRows q bands) = true)
    (hp : pack z.bank.onRows q (inputs q u z j) = bs)
    (hb : bands.all (checkBand z.bank.onRows bs) = true) : VectorDots q u z j := by
  intro i hᵢ k hₖ
  rw [dot_eq]
  subst bs
  apply int_sum_zero hi _ hb
  apply List.all_eq_true.mp hc
  exact mem_axis hᵢ hₖ
end CJ6.Fast
end
section
namespace CJ6.Fast
structure Lane where
  a : ℕ
  pos : ℕ
  n : ℕ
  width : ℕ
  digits : ℕ
private def expand (w : ℕ) : ℕ → Bool → ℕ → ℕ × ℕ
  | 0, _, _ => (0,0)
  | n+1, odd, x =>
    let v := x % 2^w
    let v := if odd then (CJ0.p-1)*v else v
    let t := expand w n (!odd) (x >>> w)
    (v+t.1, v+(t.2 <<< 192))
def bucket (left : Bool) (q : ℕ) (l : Lane) : CJ6.Packed.Bucket :=
  let c := if left then l.pos-l.a else q-l.a-l.pos
  let t := expand l.width l.n (c%2 == 1) l.digits
  (l.a, t.1, t.2 <<< (192*l.pos))
def buckets (left : Bool) (q : ℕ) (ls : List Lane) := ls.map (bucket left q)
def good (left : Bool) (q : ℕ) (ls : List Lane) (bs : List CJ6.Packed.Band) : Prop :=
  bs.all (CJ6.Packed.checkBand left (buckets left q ls)) = true
end CJ6.Fast
end
section
namespace CJ6
theorem belowZero {P : ℕ → Prop} : ∀ i < 0, P i := by omega
theorem belowSucc {P : ℕ → Prop} {n : ℕ} (h : ∀ i < n, P i) (hlast : P n) :
    ∀ i < n+1, P i := by
  intro i hi
  by_cases he : i = n
  · simpa only [he] using hlast
  · exact h i (by omega)
end CJ6
end
section
namespace CJ6
open CJ1 (total)
private def triangle (n : ℕ) := n*(n-1)/2
private theorem triangle_succ (n : ℕ) : triangle (n+1) = n + triangle n := by
  simp only [triangle, ← Nat.choose_two_right, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
private def ramp (s a b n : ℕ) :=
  let t := (b-a+s-1)/s
  let d := n-t
  d*(a+s*t-b) + s*triangle d
private theorem ramp_eq (s a b n : ℕ) (hs : s=1 ∨ s=2) :
    total (fun i => a+s*i-b) n = ramp s a b n := by
  let t := (b-a+s-1)/s
  have ht₀ : b ≤ a+s*t := by dsimp [t]; rcases hs with rfl|rfl <;> omega
  have ht₁ (i : ℕ) (hi : i < t) : a+s*i ≤ b := by
    dsimp [t] at hi
    rcases hs with rfl|rfl <;> omega
  change _ = (n-t)*(a+s*t-b) + s*triangle (n-t)
  induction n with
  | zero => simp [total, triangle]
  | succ n ih =>
    rw [total, ih]
    by_cases hn : n < t
    · have h₀ : n-t = 0 := by omega
      have h₁ : n+1-t = 0 := by omega
      simp [h₀, h₁, Nat.sub_eq_zero_of_le (ht₁ n hn)]
    · have hd : n+1-t = (n-t)+1 := by omega
      have hv : a+s*n-b = (a+s*t-b) + s*(n-t) := by
        rcases hs with rfl|rfl <;> omega
      rw [hd, triangle_succ, Nat.add_mul, one_mul, Nat.mul_add, hv]
      omega
private def quickRows (q u : ℕ) :=
  let a := u+2*q+1
  let n := q+1
  ramp 1 a 20 n + ramp 2 a (72+n) n - (ramp 2 a (20+n) n + ramp 1 a 72 n)
private theorem quickRows_eq (q u : ℕ) : rows q u = quickRows q u := by
  let a := u+2*q+1
  let n := q+1
  have summation (j : ℕ) (hj : j ≤ n) :
      total (rowLen q u) j + total (fun h => a+2*h-(20+n)) j +
        total (fun h => a+1*h-72) j =
      total (fun h => a+1*h-20) j + total (fun h => a+2*h-(72+n)) j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hi := ih (by omega)
      have cell : rowLen q u j + (a+2*j-(20+n)) + (a+1*j-72) =
          (a+1*j-20) + (a+2*j-(72+n)) := by
        dsimp [rowLen, rowHi, rowLo, a, n] at *
        omega
      simp only [total] at ⊢
      omega
  have eq := summation n (Nat.le_refl _)
  rw [ramp_eq 2 _ _ _ (Or.inr rfl), ramp_eq 1 _ _ _ (Or.inl rfl),
      ramp_eq 1 _ _ _ (Or.inl rfl), ramp_eq 2 _ _ _ (Or.inr rfl)] at eq
  change total (rowLen q u) n = ramp 1 a 20 n + ramp 2 a (72+n) n - (ramp 2 a (20+n) n + ramp 1 a 72 n)
  omega
private theorem cols_large (q u : ℕ) (hq : 20 ≤ q) : cols q u = cols 20 (min u 20) := by
  unfold cols
  rw [min_eq_right hq]
  congr 1
  funext b
  unfold colLen colHi colLo
  omega
private def colTable (u : ℕ) : ℕ := (0x78777674726f6c68645f5a544e47403830271e140a >>> (8*u)) % 256
private theorem colTable_eq : ∀ u < 21, cols 20 u = colTable u :=
  (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowZero (P := fun u => cols 20 u = colTable u)) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl)
private def quickCols (q u : ℕ) := if q < 20 then cols q u else colTable (min u 20)
private theorem quickCols_eq (q u : ℕ) : cols q u = quickCols q u := by
  unfold quickCols
  split
  · rfl
  · exact (cols_large _ _ (by omega)).trans (colTable_eq _ (by omega))
private def quickGrade (q : ℕ) := total (fun u =>
  boundIn q u (min (quickRows q u) (quickCols q u)) (cells q)) (72-q)
private theorem grade_eq_quick (q : ℕ) : grade q = quickGrade q := by
  unfold grade quickGrade allowance nominal
  simp only [quickRows_eq, quickCols_eq]
private theorem step {n s x y : ℕ} (hs : total grade n = s)
    (hx : quickGrade n = x) (hy : s + x = y) : total grade (n+1) = y := by
  rw [total, hs, grade_eq_quick, hx, hy]
local notation "row!" p "," v => step p (x := v) rfl rfl
end CJ6
end
section
namespace CJ6
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
end CJ6
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3
open scoped BigOperators
end K1_13_2_3_6
end

end Merged_Numeric6Defs

-- merged module Numeric6AuxCert
section Merged_Numeric6AuxCert
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_1
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
end CJ6_1
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3
open scoped BigOperators
def sumFrom (f : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumFrom f j n + f (j + n)
end K1_13_2_3_6
end

end Merged_Numeric6AuxCert

-- merged module Pack_K1_14_2_1Arithmetic
section Merged_Pack_K1_14_2_1Arithmetic
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_14_2_1
open K1 K1_14 K1_14_2 Finset
theorem twice_sum_linear (a b : ℤ) (n : ℕ) :
    2 * (∑ j ∈ range n, (a + b * (j : ℤ))) =
      n * (2 * a + b * ((n : ℤ) - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring
private def nodeRow (k d : ℕ) : ℕ :=
  let n := min k ((d + 1) / 2)
  n * (d + 1 - n)
private def nodeCost (s : Shape) : ℕ :=
  triangle s.U * 262144 *
    ∑ q ∈ range (s.B + 1), nodeRow (min q s.J + 1) (s.m + min q s.J - q)
private def poleSlope (s : Shape) : ℕ :=
  2 * (s.U + 1) * ∑ q ∈ range (s.B + 1), (min q s.J + 1) * ((s.B + s.J - q) * (s.B - q))
private def widthBase (s : Shape) : ℤ :=
  ∑ q ∈ range (s.B + 1), (((min q s.J : ℕ) : ℤ) + 1) *
    (2 * ((s.m : ℤ) * 180265 - (q : ℤ) * 131071) + min q s.J)
private def widthSlope (s : Shape) (r mode : ℕ) : ℤ :=
  ∑ q ∈ range (s.B + 1), (((min q s.J : ℕ) : ℤ) + 1) *
    (2 * ((q : ℤ) - 2 * r) - 2 * mode * min q s.J)
private theorem width_cast (h r : ℕ) (s : Shape) (q j : ℕ)
    (hh : h ≤ 131071) (hq : q ≤ s.B)
    (hw : s.B * (131071 - h) < cutoffCount h r s) :
    (rawWidth h r s q j : ℤ) =
      (s.m : ℤ) * 180265 - 2 * (h : ℤ) * r + j - (q : ℤ) * (131071 - h) := by
  have hq' := (Nat.mul_le_mul_right (131071 - h) hq).trans hw.le
  have hbuf : 2 * h * r ≤ s.m * 180265 := by unfold cutoffCount at hw; omega
  unfold rawWidth cutoffCount at *
  rw [Nat.cast_sub (by omega : q * (131071 - h) ≤ s.m * 180265 - 2 * h * r + j)]
  push_cast [Nat.cast_sub hh, Nat.cast_sub hbuf]
  rfl
theorem volume_eq (h r mode : ℕ) (s : Shape) (hh : h ≤ 131071)
    (hw : s.B * (131071 - h) < cutoffCount h r s) :
    2 * ((rawVolume h r s : ℤ) - mode * (movingCeiling h s : ℤ)) =
      (triangle s.U : ℤ) * (widthBase s + h * widthSlope s r mode) := by
  calc
    _ = (triangle s.U : ℤ) * ∑ q ∈ range (s.B + 1),2 *
          ∑ j ∈ range (min q s.J + 1), ((rawWidth h r s q j : ℤ) - mode * (2 * h * j)) := by
      unfold rawVolume movingCeiling shapeSum
      push_cast [Nat.cast_sum]
      simp only [sum_sub_distrib, ← mul_sum, mul_sub]
      ring
    _ = (triangle s.U : ℤ) * (widthBase s + h * widthSlope s r mode) := by
      unfold widthBase widthSlope
      congr 1
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro q hqr
      have hq : q ≤ s.B := Nat.le_of_lt_succ (mem_range.mp hqr)
      simp_rw [width_cast h r s q _ hh hq hw]
      let a : ℤ := (s.m : ℤ) * 180265 - 2 * (h : ℤ) * r - (q : ℤ) * (131071 - h)
      let b : ℤ := 1 - 2 * (h : ℤ) * mode
      have hrow : ∀ j : ℕ,
          (s.m : ℤ) * 180265 - 2 * (h : ℤ) * r + j - (q : ℤ) * (131071 - h) -
            mode * (2 * (h : ℤ) * j) = a + b * j := by
        intro j
        dsimp [a, b]
        ring
      simp_rw [hrow]
      rw [twice_sum_linear]
      push_cast
      dsimp [a, b]
      ring
def worstBase (s : Shape) : ℤ := (s.m : ℤ) * 180265 - (s.B : ℤ) * 131071
def worstSlope (s : Shape) (r : ℕ) : ℤ := (s.B : ℤ) - 2 * r
def surplusBase (s : Shape) : ℤ := (triangle s.U : ℤ) * widthBase s - 2 * nodeCost s
def surplusSlope (s : Shape) (r mode : ℕ) : ℤ :=
  (triangle s.U : ℤ) * widthSlope s r mode - 2 * poleSlope s
private def Certificate (s : Shape) (r mode : ℕ) : Prop :=
  0 < worstBase s + 2601 * worstSlope s r ∧
  0 < worstBase s + 3554 * worstSlope s r ∧
  0 < surplusBase s + 2601 * surplusSlope s r mode ∧
  0 < surplusBase s + 3554 * surplusSlope s r mode
private def GoodStage (s : Stage) : Prop :=
  Certificate s.cheap s.reserve 0 ∧ Certificate s.layered s.reserve 1 ∧ s.cheap.U < p
private instance (s : Stage) : Decidable (GoodStage s) := by
  unfold GoodStage Certificate
  infer_instance
section
set_option maxHeartbeats 0
set_option maxRecDepth 16000
end
end K1_14_2_1
end

end Merged_Pack_K1_14_2_1Arithmetic

-- merged module Pack_K1_14_2_1Split
section Merged_Pack_K1_14_2_1Split
set_option Elab.async false
set_option autoImplicit true
section
set_option maxSynthPendingDepth 8
namespace K1_14_2_1
noncomputable section
open K1 K1_14 K1_14_2 Polynomial Finset
def c1 : Prop :=
  ∀ (G P R : Jet) (U e : ℕ),
    Irreducible G → 0 < G.natDegree → UsesSeed G →
    P ≠ 0 → G ∣ P → U < p →
    (∀ j i, ((P.coeff j).coeff i).totalDegree ≤ U) →
    (∀ (i : Fin 2) (r : ℕ), r < e → G ∣ seedHasse i r R) →
    G ^ e ∣ R
end
end K1_14_2_1
end

end Merged_Pack_K1_14_2_1Split

-- merged module Pack_K1_14_3_2_7Proof
section Merged_Pack_K1_14_3_2_7Proof
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 300000
namespace K1_14_3_2_7
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
end
end K1_14_3_2_7
end

end Merged_Pack_K1_14_3_2_7Proof

end Merged6967_Pack_K1_14_3_2_7Proof

section Merged6967_SoloK1_13_1_1ArithmeticLogic
set_option Elab.async false









set_option Elab.async false

-- merged module Fast040
section Merged_Fast040
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_1
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧
    u.some.weight (fun i => i.val) ≤ 48 ∧
    u (some 3) ≤ 10 ∧
    u (some 1) + u (some 2) + u (some 3) ≤ 48 - (u.some.degree - 113 + 1) / 2 ∧
    u.weight (differentialWeight 133671) ≤ 90 * 180265 - 1
end
end K1_13_1
end
section
namespace K1_13_1
noncomputable section
section Evaluation
open K1 K1_13 PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative
open scoped BigOperators
theorem coeff_flatten {n : ℕ} (P : Row n) (m : Fin n →₀ ℕ) (i : ℕ) :
    ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).coeff (m.optionElim i) =
      (P.coeff m).coeff i := by
  rw [← MvPolynomial.optionEquivRight_coeff_coeff, AlgEquiv.apply_symm_apply]
theorem atJet_unflatten (Q : DifferentialPolynomial Geom 3) (S : (Polynomial Geom)) :
    atJet (MvPolynomial.optionEquivRight Geom (Fin 4) Q) S =
      differentialSpecialization Q S := by
  let x : Option (Fin 4) → (Polynomial Geom) := fun
    | none => Polynomial.X
    | some i => jet S i
  have h := MvPolynomial.aeval_map_optionEquivRight (R := Geom) x Q
  have hx : x none = Polynomial.X := rfl
  have hj : (fun j => x (some j)) = jet S := rfl
  rw [hx, hj, Polynomial.aeval_X_left] at h
  rw [show (AlgHom.id Geom (Polynomial Geom)).toRingHom = RingHom.id ((Polynomial Geom)) from rfl,
    MvPolynomial.map_id] at h
  rw [MvPolynomial.aeval_eq_eval] at h
  unfold atJet differentialSpecialization
  refine h.trans (AlgHom.congr_fun ?_ Q)
  apply MvPolynomial.algHom_ext
  intro v
  rw [differentialSpecializationHom, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  cases v <;> rfl
end Evaluation
section LeadingCoefficient
open K1_13 MvPolynomial
open scoped Polynomial
def topView : Row 4 ≃ₐ[(Polynomial Geom)] Polynomial (Row 3) :=
  (renameEquiv (Polynomial Geom) finSuccEquivLast).trans (optionEquivLeft (Polynomial Geom) (Fin 3))
def anchorLead (P : Row 4) : Row 3 := (topView P).leadingCoeff
theorem topView_degree (P : Row 4) : (topView P).natDegree = (shape P).t := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast P)).natDegree = P.degreeOf 3
  rw [natDegree_optionEquivLeft]
  exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 3)
theorem anchorLead_ne {P : Row 4} (hP : P ≠ 0) : anchorLead P ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr (fun h => hP (topView.injective (h.trans (map_zero _).symm)))
theorem anchorLead_mul (P Q : Row 4) : anchorLead (P * Q) = anchorLead P * anchorLead Q := by
  rw [anchorLead, map_mul, Polynomial.leadingCoeff_mul]
  rfl
private def partialEval (S : (Polynomial Geom)) : Row 4 →+* (Polynomial (Polynomial Geom)) :=
  eval₂Hom Polynomial.C fun i : Fin 4 =>
    if i = 3 then Polynomial.X else Polynomial.C (jet S i)
private theorem partialEval_eq_map (P : Row 4) (S : (Polynomial Geom)) :
    partialEval S P = (topView P).map (eval (jet S)) := by
  have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
  have h : partialEval S = (Polynomial.mapRingHom (eval (jet S))).comp topView.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [partialEval, topView, optionEquivLeft_C]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [partialEval, topView, hlast, optionEquivLeft_X_none, show Fin.last 3 = (3 : Fin 4) by rfl]
      · have hj : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
        simp [partialEval, topView, optionEquivLeft_X_some, hj, jet]
  exact RingHom.congr_fun h P
theorem eval_anchorLead (P : Row 4) (S : (Polynomial Geom)) :
    atJet (anchorLead P) S = topLead P S := by
  change eval (jet S) (topView P).leadingCoeff =
    (partialEval S P).coeff (shape P).t
  rw [partialEval_eq_map, Polynomial.coeff_map, ← topView_degree, Polynomial.leadingCoeff]
theorem atJet_eq_anchorLead_of_top_zero (P : Row 4) (S : (Polynomial Geom)) (ht : (shape P).t = 0) :
    atJet P S = atJet (anchorLead P) S := by
  have he : atJet P S = (partialEval S P).eval (jet S (3 : Fin 4)) := by
    have h : eval (jet S) =
        (Polynomial.evalRingHom (jet S (3 : Fin 4))).comp (partialEval S) := by
      apply MvPolynomial.ringHom_ext
      · intro p
        simp [partialEval]
      · intro i
        by_cases hi : i = 3
        · subst i
          simp [partialEval]
        · simp [partialEval, hi]
    exact RingHom.congr_fun h P
  have hd : (partialEval S P).natDegree ≤ 0 := by
    rw [partialEval_eq_map]
    exact Polynomial.natDegree_map_le.trans (by rw [topView_degree, ht])
  rw [he, eval_anchorLead]
  change (partialEval S P).eval _ = (partialEval S P).coeff (shape P).t
  rw [ht, Polynomial.eq_C_of_natDegree_le_zero hd, Polynomial.eval_C, Polynomial.coeff_C_zero]
theorem indexDegree_eq {n : ℕ} (P : Row n) :
    indexDegree P = P.weightedTotalDegree (fun i => i.val) := by
  simp only [indexDegree, weightedTotalDegree, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]
theorem anchorLead_term (P : Row 4) (m : Fin 3 →₀ ℕ) (hm : m ∈ (anchorLead P).support) :
    ∃ u ∈ P.support, P.coeff u = (anchorLead P).coeff m ∧
      ∀ w : Fin 4 → ℕ, m.weight (fun i => w i.castSucc) ≤ u.weight w := by
  classical
  let k := (topView P).natDegree
  let c := rename finSuccEquivLast P
  have hc : c.coeff (m.optionElim k) = (anchorLead P).coeff m := by
    exact (optionEquivLeft_coeff_coeff _ _ _ _).symm
  have hs : m.optionElim k ∈ c.support :=
    mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
  rw [show c = rename finSuccEquivLast P from rfl,
    support_rename_of_injective finSuccEquivLast.injective] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hs
  refine ⟨u, hu, ?_, fun w => ?_⟩
  · rw [← hc, ← he, coeff_rename_mapDomain _ finSuccEquivLast.injective]
  · let w' : Option (Fin 3) → ℕ := fun v => v.elim (w 3) (fun i => w i.castSucc)
    have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
    have hw : ∀ i : Fin 4, w' (finSuccEquivLast i) = w i := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [w', hlast, show Fin.last 3 = (3 : Fin 4) by rfl]
      · simp [w']
    have hweight : (m.optionElim k).weight w' = u.weight w := by
      rw [← he]
      simp only [Finsupp.weight_apply, smul_eq_mul]
      rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
      simp only [hw]
    rw [Finsupp.weight_optionElim] at hweight
    exact hweight ▸ Nat.le_add_left _ _
end LeadingCoefficient
section FactorCover
open K1 K1_13 MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
theorem index_bounds (P : Row 4) :
    3 * (shape P).t ≤ (shape P).j ∧ (shape P).j ≤ 3 * (shape P).b := by
  classical
  change 3 * P.degreeOf 3 ≤ indexDegree P ∧ indexDegree P ≤ 3 * P.totalDegree
  rw [indexDegree_eq]
  constructor
  · rw [MvPolynomial.degreeOf_eq_sup]
    have h : P.support.sup (fun m => m (3 : Fin 4)) ≤
        P.weightedTotalDegree (fun i => i.val) / 3 := by
      apply Finset.sup_le
      intro m hm
      have hterm := Finsupp.apply_smul_le_weight (fun i : Fin 4 => i.val) m (3 : Fin 4)
      have hthree : (3 : Fin 4).val = 3 := rfl
      have hle := le_weightedTotalDegree (fun i : Fin 4 => i.val) hm
      have hmul : 3 * m (3 : Fin 4) ≤ P.weightedTotalDegree (fun i => i.val) :=
        (by simpa only [smul_eq_mul, Nat.mul_comm, hthree] using hterm :
          3 * m (3 : Fin 4) ≤ m.weight (fun i => i.val)).trans hle
      omega
    omega
  · rw [weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    have hle := Finsupp.weight_le_weight
      (w := fun i : Fin 4 => i.val) (w' := fun _ => 3) (fun i => Nat.le_of_lt_succ i.isLt) m
    have he : m.weight (fun _ => 3) = 3 * m.degree := by
      simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
        Finset.mul_sum, Nat.mul_comm]
    have hdeg : m.degree ≤ P.totalDegree := le_totalDegree hm
    exact hle.trans (he.trans_le (Nat.mul_le_mul_left 3 hdeg))
end FactorCover
section Composition
open K1_13
end Composition
end
end K1_13_1
end
section
namespace K1_13_1_1
open K1_13 K1_13_1 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def residualDegree (s : ℕ) : ℕ :=
  min s (48 - (s - 113 + 1) / 2)
def orderCutoff (s : ℕ) (g : ℤ) : ℤ := 90 - (s : ℤ) - g
def jetIndex : Fin 4 → ℕ := Fin.val
def targetOrder : Fin 4 → ℕ := ![3,0,1,2]
def BandExponent (d : ℕ) (lo hi : ℤ) (f : ℕ) (m : Fin 4 →₀ ℕ) : Prop :=
  m.degree = d ∧ lo ≤ (m.weight jetIndex : ℤ) ∧ (m.weight jetIndex : ℤ) ≤ hi ∧ m 3 ≤ f
def intervalSize (lo hi : ℤ) : ℕ := (hi + 1 - lo).toNat
def sumRange (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec 0 (fun i a => a + f i) n
theorem sumRange_eq_sum (n : ℕ) (f : ℕ → ℕ) :
    sumRange n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl
def bandCount (d : ℕ) (lo hi : ℤ) (top : ℕ) : ℕ :=
  sumRange (min d top + 1) fun f =>
    sumRange (min (d - f) ((hi - 3 * f) / 2).toNat + 1) fun c =>
      intervalSize (max 0 (lo - 2 * c - 3 * f))
        (min ((d : ℤ) - f - c) (hi - 2 * c - 3 * f))
def lineBound (d : ℕ) (lo order : ℤ) (b c : ℕ) : ℕ :=
  let fmin := max 0 ((lo - b - 2 * (min c 24 : ℕ) + 2) / 3)
  let rowMin := max fmin (3 * (d : ℤ) - 3 * b - 2 * c - order + 1)
  min (intervalSize fmin (min d 10)) (intervalSize rowMin ((d : ℤ) - b - c))
def pairBound (d : ℕ) (lo : ℤ) (b : ℕ) : ℕ :=
  sumRange (min d 10 + 1) fun f =>
    intervalSize (max 0 ((lo - b - 3 * f + 1) / 2))
      (min ((d : ℤ) - f) ((48 - 3 * f) / 2))
structure FactorPowers where
  value : ℕ
  jetTwo : ℕ
  quad : ℕ
  cubic : ℕ
noncomputable section
abbrev Form := MvPolynomial (Fin 4) Geom
def bandSpace (d : ℕ) (lo hi : ℤ) (f : ℕ) : Submodule Geom Form :=
  restrictSupport Geom {m | BandExponent d lo hi f m}
def valueForm : Form := MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 2 + MvPolynomial.X 3
def backShift : Form →ₐ[Geom] Form :=
  bind₁ fun j => if j = 0 then valueForm else MvPolynomial.X j
def blockMap (s : ℕ) (g : ℤ) : bandSpace (residualDegree s) (-g) 48 10 →ₗ[Geom] Form :=
  ((weightedTruncation targetOrder (orderCutoff s g).toNat).comp
    backShift.toLinearMap).domRestrict _
def projectJet (j : Fin 4) (k : ℕ) : Form →ₗ[Geom] Form :=
  filterSupport fun m => m j = k
def pascalRowScale (e : Fin 4 →₀ ℕ) : Geom :=
  (-1 : Geom) ^ (e 2) / ∏ j : Fin 4, ((e j).factorial : Geom)
def pascalColScale (m : Fin 4 →₀ ℕ) : Geom :=
  (-1 : Geom) ^ (m 2) * ∏ j : Fin 4, ((m j).factorial : Geom)
def PascalEntries : Prop :=
  ∀ (m e : Fin 4 →₀ ℕ), m.degree = e.degree → m.degree ≤ 48 →
    (backShift (monomial m 1)).coeff e =
      pascalRowScale e * pascalColScale m *
        ((e 1).choose (m 1) : Geom) * ((e 2).choose (m 2) : Geom) *
          ((e 3).choose (m 3) : Geom)
end
end K1_13_1_1
end
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
end K1_13_1_1
end

end Merged_Fast040

-- merged module SoloK1_13_1_1ArithmeticLogic
section Merged_SoloK1_13_1_1ArithmeticLogic
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_1_1
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
end K1_13_1_1
end

end Merged_SoloK1_13_1_1ArithmeticLogic

end Merged6967_SoloK1_13_1_1ArithmeticLogic
