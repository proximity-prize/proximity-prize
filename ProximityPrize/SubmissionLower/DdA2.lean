import ProximityPrize.SubmissionLower.DdBG
import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.ENat.BigOperators
import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.DdAA
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.DdZ3EWiUc
import ProximityPrize.SubmissionLower.DdZgdIx1d
import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.DdP6Defs
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming AlgHom.coe_toRingHom→zlv,AlgHom.toRingHom_eq_coe→ziQ,Algebra→yU,Algebra.algebraMap→cy,Algebra.algebraMap_self_apply→zEi,Algebra.smul_def→Oc,CharP.cast_eq_zero_iff→zX2,CommRing→qJ,DFunLike.congr_fun→Ze,DecidableEq→t7,Disjoint→Mj,Field→zc,Filter→Df,Filter.atTop→pG,Filter.eventually_ge_atTop→ZJ,Fin.castSucc→uz,Fin.last→pC,Fin.lastCases→G0,Fin.range_fin_succ→Aa,Fin.sum_univ_eq_sum_range→Ok,Fin.sum_univ_four→zmM,Finite→qy,Finset→nI,Finset.add_sum_erase→zT2,Finset.card_univ→S1,Finset.finite_toSet→WD,Finset.induction_on→Kl,Finset.le_sup→WX,Finset.mem_filter→zO0,Finset.mem_insert_of_mem→ IU,Finset.mem_insert_self→Kc,Finset.mem_univ→vk,Finset.mul_sum→ze,Finset.prod_congr→Dz,Finset.prod_insert→zqX,Finset.range→p7,Finset.single_le_sum→Pc,Finset.sum_add_distrib→zfW,Finset.sum_apply→Zh,Finset.sum_attach→zKD,Finset.sum_congr→qx,Finset.sum_const→Mw,Finset.sum_filter→Np,Finset.sum_insert→Mk,Finset.sum_le_sum→uW
open _root_ renaming Finset.sum_nonneg→zlo,Finset.sum_subset→Wl,Finset.sup_le→X4,Finset.univ→Kv,Finsupp.add_apply→Dv,Finsupp.degree_eq_sum→zFi,Finsupp.filter_apply→zfF,Finsupp.finsetSum_apply→Xu,Finsupp.induction_linear→FK,Finsupp.single→Pk,Finsupp.single_apply→EK,Finsupp.smul_single_one→zrt,Finsupp.tsub_apply→VH,Finsupp.weight→ oy,Finsupp.weight_apply→SW,Finsupp.weight_eq_sum→Fz,Finsupp.weight_single→qG,Finsupp.weight_sub_single_add→Zg,Fintype→ oK,Fintype.card_fin→Pj,Fintype.equivFin→G8,Fintype.ofFinite→Gk,FractionRing→t5,Function.Injective→p9,Function.Surjective→vh,Function.comp_apply→Sd,Function.update→Wm,Ideal→aU,Ideal.IsPrime.comap→zm,Ideal.Quotient.eq_zero_iff_mem→G7,Ideal.Quotient.factorₐ→z5F,Ideal.Quotient.liftₐ→zTA,Ideal.Quotient.mk→mD,Ideal.Quotient.mk_surjective→Et,Ideal.Quotient.mkₐ→Fa,Ideal.comap_comap→Pf,Ideal.comap_isPrime→zG1,Ideal.comap_map_of_bijective→zFA,Ideal.comap_map_of_surjective→zEk,Ideal.comap_mono→Vl,Ideal.coprime_of_no_prime_ge→zQx,Ideal.height_add_one_le_of_lt_of_isPrime→zSK,Ideal.isPrime_map_of_isLocalizationAtPrime→zlD,Ideal.map_isPrime_of_surjective→TI,Ideal.map_map→zf,Ideal.map_span→y5,Ideal.mem_homogeneousCore_of_homogeneous_of_mem→zFp,Ideal.mem_map_of_mem→zh
open _root_ renaming Ideal.mem_span_singleton_self→vH,Ideal.mk_ker→Pr,Ideal.mul_mem_right→zx6,Ideal.mul_top→FU,Ideal.ofList→zE,Ideal.ofList_cons→z2L,Ideal.ofList_singleton→N0,Ideal.primesOver→TZ,Ideal.ringKrullDim_quotient_succ_le_of_lt→X8,Ideal.smul_eq_mul→FV,Ideal.span→lJ,Ideal.span_insert→OJ,Ideal.span_singleton_le_iff_mem→G3,Ideal.span_singleton_prime→zw5,Ideal.subset_span→ Il,Ideal.toIdeal_homogeneousCore_le→zFP,Insert.insert→t8,Irreducible→Sv,IsCoprime→xI,IsDomain→G2,IsFractionRing.injective→xL,IsLeftCancelMulZero.mul_left_cancel_of_ne_zero→zUH,IsLocalRing→PM,IsLocalRing.maximalIdeal→ oD,IsLocalRing.maximalIdeal.isMaximal→zHl,IsLocalization.AtPrime.isUnit_to_map_iff→z7L,IsLocalization.AtPrime.map_eq_maximalIdeal→zNE,IsLocalization.AtPrime.to_map_mem_maximal_iff→zRt,IsLocalization.algebraMap_mem_map_algebraMap_iff→zZS,IsLocalization.exists_mk'_eq→zcf,IsLocalization.isPrime_of_isPrime_disjoint→PD,IsLocalization.lift→QL,IsLocalization.lift_eq→NZ,IsLocalization.map_units→z0j,IsLocalization.mk'→zzm,IsLocalization.mk'_spec→zOg,IsLocalization.orderEmbedding→zRW,IsLocalization.ringHom_ext→zuW,IsLocalization.under_map_of_isPrime_disjoint→ztT,IsNoetherianRing→MS,IsSMulRegular→wY,IsScalarTower.algebraMap_eq→zYY,IsScalarTower.of_algebraMap_eq→zsL,IsUnit→vl,LinearEquiv.ofBijective→zD9,LinearMap.ker→uJ,LinearMap.mem_ker→Kz
open _root_ renaming LinearMap.range→Dw,LinearMap.range_domRestrict→zyK,LinearOrder.lift'→zEZ,Localization.AtPrime→Au,Localization.localRingHom_to_map→zMs,Module.Finite→Hw,Module.finrank→G1,Module.finrank_eq_nat_card_basis→zUF,Module.finrank_eq_zero_of_subsingleton→z6g,Module.length→qm,Module.length_eq_add_of_exact→ziu,Module.length_eq_finrank→z1C,Module.length_le_of_injective→zdt,Module.length_le_of_surjective→VS,ModuleCat.of→Kh,MonomialOrder→FR,MonomialOrder.degLex→zwf,MvPolynomial→nX,MvPolynomial.C→nq,MvPolynomial.IsWeightedHomogeneous.mul→JK,MvPolynomial.X→lV,MvPolynomial.affineHilbertFunction→Qy,MvPolynomial.affineHilbertPolynomial→yl,MvPolynomial.algHom_ext→Zf,MvPolynomial.basisRestrictSupport→zzc,MvPolynomial.coeff_eq_zero_of_totalDegree_lt→Xp,MvPolynomial.eval→p5,MvPolynomial.eval_C→FQ,MvPolynomial.eval_X→Gr,MvPolynomial.eval₂→z8,MvPolynomial.eval₂Hom→yB,MvPolynomial.eval₂Hom_C→NW,MvPolynomial.eval₂Hom_X'→Lf,MvPolynomial.eval₂_eq→zMm,MvPolynomial.eventually_eval_affineHilbertPolynomial→zaM,MvPolynomial.hom_eval₂→zUe,MvPolynomial.homogeneousComponent→zyc,MvPolynomial.isWeightedHomogeneous_X→Zi,MvPolynomial.le_weightedTotalDegree→z6P,MvPolynomial.map→t3,MvPolynomial.map_C→KI,MvPolynomial.map_X→G9,MvPolynomial.map_injective→zNV,MvPolynomial.mem_iff_weightedHomogeneousComponent_mem→z1h,MvPolynomial.mem_support_iff→zuk,MvPolynomial.mem_weightedHomogeneousSubmodule→Mz,MvPolynomial.monomial→qz,MvPolynomial.monomial_mul_monomial→zDU
open _root_ renaming MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective→zGE,MvPolynomial.optionEquivLeft→xu,MvPolynomial.optionEquivLeft_coeff_coeff→z9x,MvPolynomial.optionEquivRight→G4,MvPolynomial.pderiv→yQ,MvPolynomial.rename→ IT,MvPolynomial.renameEquiv_apply→zyl,MvPolynomial.rename_X→SC,MvPolynomial.restrictSupport→yJ,MvPolynomial.restrictSupport_eq_span→NI,MvPolynomial.ringHom_ext→Ea,MvPolynomial.support_weightedHomogeneousComponent→z66,MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt→ztH,MvPolynomial.weightedHomogeneousComponent→Ar,MvPolynomial.weightedHomogeneousComponent_eq_self→XG,MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous→zmP,MvPolynomial.weightedHomogeneousComponent_mem→zbF,MvPolynomial.weightedHomogeneousComponent_mem_of_mem→MK,MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported→zSq,MvPolynomial.weightedTotalDegree_mul_le→Eg,MvPolynomial.weightedTotalDegree_pderiv_le_sub→zYB,MvPolynomial.weightedTotalDegree_zero→z4a,MvPolynomial.zeroLocus→VO,Nat.add_le_add→zk,Nat.add_le_add_left→R9,Nat.add_mul→UY,Nat.add_sub_cancel_left→z7K,Nat.add_sub_of_le→GR,Nat.card_coe_set_eq→JM,Nat.card_congr→Nj,Nat.card_eq_fintype_card→XB,Nat.cast_mul→RD,Nat.cast_sum→SU,Nat.le_add_left→Pv,Nat.le_add_right→zi,Nat.le_of_lt_succ→Ef,Nat.lt_succ_of_le→SM,Nat.mul_le_mul_left→qU,Nat.mul_left_comm→WK,Nat.mul_pos→WY,Nat.multichoose_eq→z4m,Nat.multichoose_zero_succ→zGT,Nat.ne_of_gt→SD,Nat.nsmul_eq_mul→UZ,Nat.pos_of_ne_zero→Nq,Nat.sub_add_cancel→zxt,Nat.sub_le_sub_right→zIu,Nat.zero_le→ In
open _root_ renaming Or.inl→Gi,Pi.add_apply→Vq,Pi.single_eq_of_ne→Ye,Polynomial→zR,Polynomial.Bivariate.swap→zd,Polynomial.C→lI,Polynomial.X→ oj,Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd→zff,Polynomial.algebraMap_eq→Zt,Polynomial.coe_eval₂RingHom→x7,Polynomial.coe_mapRingHom→yo,Polynomial.coeff_C_mul_X_pow→zds,Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le→zKB,Polynomial.coeff_map→zg,Polynomial.evalRingHom→qM,Polynomial.eval_C→Te,Polynomial.eval_X→MO,Polynomial.eval_add→zvF,Polynomial.eval₂RingHom→GY,Polynomial.eval₂_C→F9,Polynomial.eval₂_X→zC9,Polynomial.eval₂_map→zem,Polynomial.eval₂_monomial→zFK,Polynomial.exists_mul_add_mul_eq_C_resultant→zKy,Polynomial.finsetSum_coeff→zaW,Polynomial.hasseDeriv→pQ,Polynomial.hasseDeriv_map→zvb,Polynomial.hasseDeriv_monomial→zKa,Polynomial.hom_eval₂→Y4,Polynomial.induction_on'→zCU,Polynomial.isUnit_resultant_iff_isCoprime→zgx,Polynomial.mapRingHom→u8,Polynomial.map_C→sS,Polynomial.map_add→z7,Polynomial.map_dvd→RP,Polynomial.map_id→Xx,Polynomial.map_map→sI,Polynomial.map_monomial→SL,Polynomial.map_mul→v8,Polynomial.map_sum→NY,Polynomial.map_taylor→zla,Polynomial.monomial→t9,Polynomial.natDegree_map_eq_of_injective→Z0,Polynomial.natDegree_map_le→RC,Polynomial.natDegree_modByMonic_lt→Yo,Polynomial.natDegree_sum_le_of_forall_le→UP,Polynomial.preHilbertPoly→zcb,Polynomial.preHilbertPoly_eq_choose_add_sub→zg1
open _root_ renaming Polynomial.ringHom_ext→C5,Polynomial.taylor→wR,PrimeSpectrum→Rm,QuotSMulTop→yL,Ring.ord→LR,RingHom.comap_ker→S2,RingHom.comp_apply→pU,RingHom.congr_fun→t4,RingHom.ext→xW,RingHom.id→LQ,RingHom.ker→sH,RingHom.ker_eq_comap_bot→Vz,RingHom.ker_isPrime→zgL,RingHom.mem_ker→ZK,RingTheory.Sequence.IsWeaklyRegular→P7,Set.disjoint_left→Up,Set.image_image→Vs,Set.image_insert_eq→z6c,Set.image_singleton→Cy,Set.mem_fintype_sum→RJ,Set.mem_insert_iff→zP8,Set.mem_ofPred_eq→Qx,Set.mem_zero→KH,Set.nsmul_mem_nsmul→zfk,Set.pair_comm→Yi,Set.range→Re,Set.range_eq_empty→zwy,Set.singleton_def→zrN,SetLike.exists_of_lt→zxV,Submodule→u9,Submodule.Quotient.mk_eq_zero→ziM,Submodule.add_mem→Ob,Submodule.factor_surjective→zSx,Submodule.ideal_span_singleton_smul→zQT,Submodule.inclusion→zwh,Submodule.inclusion_injective→zaX,Submodule.map_comp→z1U,Submodule.mem_colon_singleton→ztS,Submodule.mem_smul_pointwise_iff_exists→zeT,Submodule.mem_top→z8t,Submodule.quotEquivOfEq→Gn,Submodule.span_le→zKY,Submodule.sum_mem→zo3,Subsingleton→zS,Subtype.ext→pL,Subtype.val→C4,Transcendental→GF,UniqueFactorizationMonoid→LP
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
