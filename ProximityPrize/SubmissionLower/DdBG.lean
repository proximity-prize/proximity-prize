import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdAA
import ProximityPrize.SubmissionLower.DdAE
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
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Flat_TorsionFree
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

section Merged6967_DdBG
set_option Elab.async false





















































set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 10000
set_option maxHeartbeats 2500000
open _root_ renaming AlgEquiv.apply_symm_apply→zIH,AlgHom.pi→Kz,AlgHom.toLinearMap_apply→FV,Algebra→ oD,Algebra.EssFiniteType→Df,Algebra.FormallyEtale→Vq,Algebra.IsAlgebraic→MS,Algebra.IsSeparable→N0,Algebra.algebraMap→cy,Algebra.algebraMap_self_apply→zEi,Algebra.smul_def→TI,Algebra.trdeg→u5,Cardinal.mk→JK,CharP→u9,CharP.cast_eq_zero_iff→S1,CommRing→nq,DFunLike.congr_fun→Nr,ENNReal.ofReal→Au,Equiv.refl→Xu,Equiv.sumCongr→P7,EquivLike.apply_eq_iff_eq→zNr,Field→lV,Fin.castSucc→pU,Fin.castSucc_injective→xI,Fin.castSucc_ne_last→zm4,Fin.last→ II,Fin.lastCases→WK,Fin.snoc→yB,Fin.snoc_castSucc→FQ,Fin.snoc_comp_castSucc→ZK,Fin.snoc_last→Dz,Fin.sum_univ_eq_sum_range→Up,Fin.sum_univ_four→zmL,Fin.sum_univ_three→Kh,Finite→vj,Finset→aU,Finset.card_insert_of_notMem→Xo,Finset.filter_subset→zT0,Finset.induction_on→Cy,Finset.le_sup→zk,Finset.mem_insert→Y4,Finset.mem_univ→vi,Finset.mul_sum→ Iw,Finset.prod_eq_zero→zue,Finset.range→Pc,Finset.smul_sum→UP,Finset.sum_add_distrib→zm,Finset.sum_attach→zKB
open _root_ renaming Finset.sum_congr→sH,Finset.sum_eq_single→G3,Finset.sum_erase_add→zvm,Finset.sum_insert→yo,Finset.sum_ite_eq'→G0,Finset.sum_le_sum→KI,Finset.sum_mul→Nq,Finset.sum_powerset_insert→EK,Finset.univ→th,Finsupp.degree_eq_sum→Qx,Finsupp.induction_linear→Zh,Finsupp.mapDomain→JQ,Finsupp.mapDomain_apply_of_injective→Vz,Finsupp.single→t3,Finsupp.sum_fintype→Z0,Finsupp.weight→t4,Finsupp.weight_single→LP,Fintype.card→G1,FractionRing→vh,Function.Injective→qG,Function.Surjective→t8,Function.iterate_one→zS5,Function.iterate_succ_apply'→Rm,Function.update→GR,Function.update_of_ne→zBg,Ideal→c9,Ideal.Quotient.eq_zero_iff_mem→Ye,Ideal.Quotient.lift→R9,Ideal.Quotient.mk→nI,Ideal.Quotient.mk_eq_mk_iff_sub_mem→Mz,Ideal.Quotient.mk_surjective→vH,Ideal.Quotient.mkₐ→Ee,Ideal.kerLiftAlg→TZ,Ideal.kerLiftAlg_injective→zvo,Ideal.kerLiftAlg_mk→Kv,Ideal.map→zE,Ideal.map_le_iff_le_comap→zo0,Ideal.map_map→Oc,Ideal.map_span→zc,Ideal.mem_map_of_mem→EP,Ideal.mem_span_singleton_self→Pf,Ideal.mem_sup_left→zKg,Ideal.quotientEquivAlg→zpY,Ideal.quotientKerAlgEquivOfSurjective→Qw,Ideal.quotientMap→Yo,Ideal.quotientMap_injective→zmq,Ideal.quotientMapₐ→zwL,Ideal.span→n5
open _root_ renaming Ideal.span_insert→zf9,Ideal.span_mono→Pr,Ideal.span_singleton_le_iff_mem→ In,Ideal.subset_span→sI,Insert.insert→sS,IntermediateField.adjoin→NY,Irreducible→ze,IsAlgClosed→G8,IsDomain→HZ,IsFractionRing.injective→z7,IsLocalRing.ResidueField→G2,IsLocalRing.maximalIdeal→zR,IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing→ztC,IsLocalization→RD,IsLocalization.AtPrime.under_maximalIdeal→znW,IsLocalization.Away.algebraMap_isUnit→Ze,IsLocalization.Away.invSelf→Un,IsLocalization.Away.lift→ztx,IsLocalization.Away.lift_eq→Ts,IsLocalization.algebraMap_mem_map_algebraMap_iff→Te,IsLocalization.exists_mk'_eq→zcf,IsLocalization.isPrime_of_isPrime_disjoint→VH,IsLocalization.minimalPrimes_map→zMt,IsLocalization.mk'→zzm,IsLocalization.mk'_spec→zOg,IsLocalization.ringHom_ext→zuW,IsScalarTower→yl,IsScalarTower.algebraMap_apply→zg,IsScalarTower.algebraMap_eq→S2,IsScalarTower.of_algebraMap_eq→zsL,IsScalarTower.toAlgHom→zE2,IsUnit→qU,LinearIndependent→X8,LinearMap.congr_fun→Zg,LinearMap.finrank_range_of_inj→XJ,LinearMap.mulLeft→XB,Localization.AtPrime→C9,Localization.AtPrime.map_eq_maximalIdeal→zRt,Localization.Away→LQ,MeasurableSet→yJ,Module.Finite→qm,Module.Flat→G6,Module.finrank→pz,Module.length→u8,Module.length_eq_finrank→Yc,MulZeroClass.mul_zero→p9,MvPolynomial→lz,MvPolynomial.C→pQ
open _root_ renaming MvPolynomial.IsPrime.vanishingIdeal_zeroLocus→QL,MvPolynomial.X→lI,MvPolynomial.X_pow_eq_monomial→zp9,MvPolynomial.aeval→ oy,MvPolynomial.aeval_X→wY,MvPolynomial.aeval_eq_eval→x7,MvPolynomial.affineDegree→uJ,MvPolynomial.affineHilbertPolynomial→p7,MvPolynomial.algHom_ext→Dv,MvPolynomial.algebraMap_def→WX,MvPolynomial.algebraMap_eq→F9,MvPolynomial.algebraMvPolynomial→Zf,MvPolynomial.algebraTensorAlgEquiv→Wm,MvPolynomial.basisMonomials→FU,MvPolynomial.coeff_C→zG0,MvPolynomial.coeff_monomial→ IT,MvPolynomial.coeff_mul_X'→X4,MvPolynomial.coeff_sum→NX,MvPolynomial.degreeOf_def→Zi,MvPolynomial.eval→nX,MvPolynomial.eval_C→Fa,MvPolynomial.eval_X→xm,MvPolynomial.eval_map→NI,MvPolynomial.eval₂→SD,MvPolynomial.eventually_eval_affineHilbertPolynomial→zaL,MvPolynomial.ext→Kl,MvPolynomial.hom_eval₂→zUe,MvPolynomial.induction_on→JM,MvPolynomial.isLocalization→zEY,MvPolynomial.isWeightedHomogeneous_monomial→UZ,MvPolynomial.map→ ox,MvPolynomial.map_eval→WW,MvPolynomial.map_injective→RC,MvPolynomial.mem_vanishingIdeal_iff→Ok,MvPolynomial.mem_vanishingIdeal_singleton_iff→v9,MvPolynomial.monomial→ ov,MvPolynomial.monomial_mul_monomial→Kp,MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective→zGE,MvPolynomial.optionEquivLeft→G7,MvPolynomial.pderiv→ oZ,MvPolynomial.pderiv_mul→Qy,MvPolynomial.quotientDegreeLE→zf,MvPolynomial.rename→p6,MvPolynomial.renameEquiv_apply→Ob,MvPolynomial.ringHom_ext→Mw,MvPolynomial.totalDegree_C→UY,MvPolynomial.totalDegree_X→RJ,MvPolynomial.totalDegree_finsetSum_le→SM
open _root_ renaming MvPolynomial.totalDegree_mul→yU,MvPolynomial.totalDegree_sub_C_le→ZJ,MvPolynomial.trdeg_of_isDomain→zUx,MvPolynomial.vanishingIdeal→uh,MvPolynomial.weightedHomogeneousComponent→yQ,MvPolynomial.weightedHomogeneousComponent_eq_self→zfp,MvPolynomial.weightedHomogeneousComponent_mem→zbF,MvPolynomial.weightedHomogeneousComponent_of_mem→Zt,MvPolynomial.zeroLocus→qM,Nat.add_le_add→Aa,Nat.cast_add→Pk,Nat.cast_mul→ IU,Nat.cast_nonneg→NW,Nat.cast_sub→Vl,Nat.choose_one_right→zk4,Nat.le_add_right→JW,Nat.lt_succ_of_le→PD,Nat.mul_le_mul_left→Kc,Nat.mul_le_mul_right→Hw,Nat.sub_add_cancel→z8,Nat.zero_le→v8,Option→zi,Pi.add_apply→Av,Pi.single→vZ,Pi.single_apply→RP,Pi.single_eq_of_ne→C5,Pi.smul_apply→PM,Polynomial→ oz,Polynomial.C→ oY,Polynomial.C_eq_natCast→Np,Polynomial.C_injective→VC,Polynomial.X→pL,Polynomial.X_dvd_iff→zIa,Polynomial.as_sum_range'→Vs,Polynomial.coeff_map→Eg,Polynomial.coeff_zero→KH,Polynomial.coeff_zero_eq_eval_zero→zTt,Polynomial.derivative→mD,Polynomial.derivative_mul→Fz,Polynomial.evalRingHom→y5,Polynomial.eval_C→FR,Polynomial.eval_map→zhI,Polynomial.eval₂RingHom→WD,Polynomial.hasseDeriv→p5,Polynomial.hasseDeriv_map→NZ,Polynomial.mapRingHom→MO,Polynomial.map_monomial→zA0,Polynomial.map_sum→zWf
open _root_ renaming Polynomial.monomial→vl,Polynomial.natDegree_taylor→SC,Polynomial.ringHom_ext→Pv,Polynomial.taylor→xL,Polynomial.taylor_coeff→SW,Polynomial.taylor_taylor→Yi,Polynomial.taylor_zero→z9k,RingHom.comp_apply→Gn,RingHom.congr_fun→Gi,RingHom.ext→Ef,RingHom.injective→Xx,RingHom.ker→ oK,RingHom.ker_isPrime→zgL,RingHom.mem_ker→zS,Set.Subset.antisymm→G5,Set.add_subset_add→zgS,Set.eq_univ_of_forall→zps,Set.image_image→Sv,Set.mem_insert_iff→Sd,Set.mem_preimage→SU,Set.mem_range_self→zWL,Set.mem_singleton_iff→Ww,Set.range→qJ,Set.range_comp'→Xp,Set.univ→z9,Submodule→zd,Submodule.map_mono→zzl,Submodule.mem_top→PA,Submodule.span→Re,Submodule.sum_mem→Wl,Submonoid.powers→LO,Subtype.ext→vG,Subtype.val→XG,Transcendental→VO,TrivSqZeroExt.ext→Gk,add_comm→LR,add_neg_cancel→OJ,add_nonneg→SL,charP_of_injective_ringHom→vw,congrArg→ oj,congrFun→wR,convexHull→xW,convexHull_min→Mk,convexHull_mono→Ml,convex_convexHull→WY,div_mul_cancel₀→TH
open _root_ renaming faithfulSMul_iff_algebraMap_injective→zSO,finSuccEquivLast→wA,inferInstance→xu,le_antisymm→yL,le_rfl→t9,map_add→pG,map_mul→lJ,map_natCast→zh,map_ne_zero_iff→Xg,map_neg→ Il,map_ofNat→uW,map_one→vk,map_pow→t7,map_prod→Lf,map_smul→KA,map_sub→qx,map_sum→t5,map_zero→ oq,measurableSet_Icc→MK,measurableSet_le→C4,measurable_const→Gj,measurable_pi_apply→Nj,mul_add→GF,mul_assoc→qy,mul_comm→uz,mul_le_mul_of_nonneg_left→qz,mul_ne_zero→FK,mul_nonneg→Et,mul_one→Dw,nonZeroDivisors→GY,not_le_of_gt→G4,nsmul_eq_mul→Mj,one_mul→t6,pow_ne_zero→Du,pow_succ→GB,smul_eq_mul→G9,sub_eq_zero→Ar,sub_self→Ea,sub_zero→Gr,subset_convexHull→VS,subsingleton_iff_forall_eq→zAZ,succ_nsmul→J4,trdeg_add_eq→Pj,zero_add→wB
set_option autoImplicit true
section
namespace oR
noncomputable section
open DdK1 aR Polynomial
open scoped BigOperators
end
end oR
end
section
namespace we
noncomputable section
open DdK1 aR oR Polynomial
open scoped BigOperators
end
end we
end
section
namespace we
noncomputable section
open DdK1 aR oR Polynomial
open scoped BigOperators
end
end we
end
section
namespace yz
noncomputable section
open aR oR we MvPolynomial
open scoped BigOperators Pointwise
end
end yz
end
section
namespace yz
noncomputable section
open aR oR we MvPolynomial
open scoped BigOperators
end
end yz
end
section
namespace zP
noncomputable section
open aR oR we yz MvPolynomial
open scoped Pointwise
end
end zP
end
section
namespace zP
noncomputable section
open aR we yz MvPolynomial
end
end zP
end
section
namespace yz
noncomputable section
open aR oR we MvPolynomial
open scoped BigOperators Pointwise
private theorem dsq {k σ:Type} [lV k] [vj σ] (x :σ→k) :
  uJ (uh k {x})=1 := by
 have hker :uh k {x} = oK (oy x :lz σ k →ₐ[k] k) := by
  ext p
  rw [zS ,v9]
 rw [hker]
 have hs :t8 (oy x :lz σ k →ₐ[k] k) :=
  fun b=>⟨C b,by simp⟩
 let e := Qw hs
 let:=Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
 rw [affineDegree_eq_finrank,e.toLinearEquiv.finrank_eq,Module.finrank_self,Nat.cast_one]
theorem bK6 {k σ τ:Type} [lV k] [vj σ] [vj τ]
    (A:Set (σ→k)) (I:c9 (lz σ k)) (hI:I=uh k A)
    (hprime :I.IsPrime) (hdim: (p7 I).natDegree=1)
    (hone :1≤uJ I) (D:lz σ k) (N :τ→lz σ k)
    (hD:D.totalDegree≤1) (hN : ∀ i,(N i).totalDegree≤1)
    (hnonzero : ∀ x∈A,eval x D ≠0) :
    ∃ Q:c9 (lz τ k),Q.IsPrime∧(p7 Q).natDegree≤1 ∧
      uJ Q≤uJ I ∧
      ∀ x∈A,(fun i=>eval x (N i)/eval x D)∈qM k Q:= by
  have hA:A.Nonempty := by
    by_contra! h
    exact hprime.ne_top (by rw [hI,h,vanishingIdeal_empty])
  obtain ⟨x₀,hx₀⟩:=hA
  let e :lz σ k →ₐ[k] (A→k) :=Kz fun x=>oy x.val
  have he :I=oK e := by
    ext p
    rw [hI,Ok,zS ,_root_.funext_iff]
    exact ⟨fun h x=>h x.val x.property,fun h x hx=>h ⟨x,hx⟩⟩
  clear hI
  subst I
  let I:=oK e
  let:I.IsPrime :=hprime
  change (p7 I).natDegree=1 at hdim
  change 1≤uJ I at hone
  let R:=lz σ k ⧸ I
  let j:R →ₐ[k] (A→k) :=TZ e
  have hj:qG j:=zvo e
  let dr :R:=nI I D
  let d:A→k :=e D
  have hjd:j dr=d:=rfl
  have hd:qU d:=Pi.isUnit_iff.mpr fun x=>isUnit_iff_ne_zero.mpr (hnonzero _ x.property)
  let y (i:τ) (x :A) :k :=eval x.val (N i)/eval x.val D
  let φ:lz τ k →ₐ[k] (A→k) :=oy y
  let Q:=oK φ
  have hφ (p:lz τ k) (x :A) :
      φ p x=oy (fun i=>y i x) p:= by
    let π:=Pi.evalAlgHom k (fun _:A=>k) x
    have h:π.comp φ=oy (fun i=>y i x) := by
      apply Dv
      intro i
      simp [φ,π]
    exact Nr h p
  have hy (i:τ) :d*y i=e (N i) := by
    ext x
    change eval x.val D *(eval x.val (N i)/eval x.val D)=eval x.val (N i)
    rw [uz ,TH _ (hnonzero _ x.property)]
  let V (m:ℕ) :zd k (A→k) :=(zf I m).map j.toLinearMap
  let W (m:ℕ) :zd k (A→k) :=(V m).comap (XB k (d^m))
  have hW (m:ℕ) (z :A→k) :
      z∈W m ↔ ∃ r∈zf I m,j r=d^m*z := by
    simp only [W,V,Submodule.mem_comap,Submodule.mem_map,LinearMap.mulLeft_apply,
      FV]
    rfl
  have hdr_pow (n:ℕ) :dr^n∈zf I n:= by
    dsimp only [dr]
    rw [← t7]
    exact mk_mem_quotientDegreeLE ((totalDegree_pow _ _).trans (by simpa using Kc n hD))
  have hmono:Monotone W:= by
    intro m n hmn z hz
    obtain ⟨r,hr,heq⟩:=(hW _ _).mp hz
    refine (hW _ _).mpr ⟨dr^(n - m)*r,?_,?_⟩
    · simpa only [z8 hmn] using
        mul_mem_quotientDegreeLE (hdr_pow (n - m)) hr
    · rw [lJ,t7,hjd,heq,← qy ,← pow_add,z8 hmn]
  have hmul (i:τ) (m:ℕ) (z :A→k) (hz :z∈W m) :
      y i*z∈W (m+1) := by
    obtain ⟨r,hr,heq⟩:=(hW _ _).mp hz
    refine (hW _ _).mpr ⟨r* nI I (N i),
      mul_mem_quotientDegreeLE hr (mk_mem_quotientDegreeLE (hN i)),?_⟩
    rw [lJ,heq,Kv,GB,← hy]
    ring
  have hclear (p:lz τ k) (m:ℕ) (hp:p.totalDegree≤ m) :
      ∃ r∈zf I m,j r=d^m*φ p:= by
    have hz : (1 :A→k)∈W 0 :=
      (hW _ _).mpr ⟨1,one_mem_quotientDegreeLE I _,by simp⟩
    have h:=aeval_mem_of_forall_mul_mem y hmono hz hmul hp
    rw [t6] at h
    exact (hW _ _).mp h
  have hQ:Q.IsPrime := by
    apply Ideal.isPrime_iff.mpr
    constructor
    · intro htop
      have hz :φ 1=0:=RingHom.mem_ker.mp (show 1∈Q from htop ▸ PA)
      rw [vk] at hz
      exact one_ne_zero (wR hz ⟨x₀,hx₀⟩)
    · intro p q hpq
      have hz :=RingHom.mem_ker.mp hpq
      change φ (p*q)=0 at hz
      rw [lJ] at hz
      obtain ⟨r,_,hr⟩:=hclear p _ t9
      obtain ⟨s,_,hs⟩:=hclear q _ t9
      have hrs :r*s=0:=hj (by
        rw [lJ,hr,hs,oq]
        calc
          _=(d^p.totalDegree*d^q.totalDegree)*(φ p*φ q) := by ring
          _=0:= by rw [hz,p9])
      rcases mul_eq_zero.mp hrs with hr₀ | hs₀
      · left
        apply RingHom.mem_ker.mpr
        exact (hd.pow _).mul_left_cancel (by rw [← hr,hr₀,oq,p9])
      · right
        apply RingHom.mem_ker.mpr
        exact (hd.pow _).mul_left_cancel (by rw [← hs,hs₀,oq,p9])
  have hgrowth (m:ℕ) :affineHilbertFunction Q m≤affineHilbertFunction I m:= by
    let ι:=TZ φ
    have hm (a :zf Q m) :d^m*ι a.1∈V m:= by
      obtain ⟨p,hp,hp'⟩:=mem_quotientDegreeLE.mp a.2
      obtain ⟨r,hr,heq⟩:=hclear p m hp
      refine Submodule.mem_map.mpr ⟨r,hr,?_⟩
      rw [FV,← hp',Kv,heq]
    let l:zf Q m →ₗ[k] V m :=
      (((XB k (d^m)).comp ι.toLinearMap).domRestrict
        (zf Q m)).codRestrict (V m) hm
    have hl:qG l:= by
      intro a b hab
      have h:d^m*ι a.1=d^m*ι b.1 :=oj XG hab
      exact vG (zvo φ ((hd.pow _).mul_left_cancel h))
    exact (LinearMap.finrank_le_finrank_of_injective hl).trans (Submodule.finrank_map_le _ _)
  have hle : ∀ᶠ m:ℕ in Filter.atTop,
      (p7 Q).eval (m:ℚ)≤(p7 I).eval (m:ℚ) := by
    filter_upwards [zaL Q,
      zaL I] with m hq hi
    rw [hq,hi]
    exact_mod_cast hgrowth m
  obtain ⟨hdegree,hcoeff⟩:=Polynomial.natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg Q) hle
  have hcover (x :A) : (fun i=>y i x)∈qM k Q:= by
    intro p hp
    rw [← hφ p x,RingHom.mem_ker.mp hp]
    rfl
  refine ⟨Q,hQ,hdegree.trans_eq hdim,?_,fun x hx=>hcover ⟨x,hx⟩⟩
  by_cases heq : (p7 Q).natDegree=(p7 I).natDegree
  · rw [uJ,uJ,heq]
    exact qz (hcoeff heq) (NW _)
  · have hzero : (affineHilbertPolynomial Q).natDegree=0:= by omega
    let:=hQ
    let:=natDegree_affineHilbertPolynomial_eq_zero_iff.mp hzero
    have hmax :=Ideal.Quotient.maximal_of_isField Q (IsField.of_isDomain_of_finite k _)
    have hpoint :Q≤uh  k {(fun i=>y i ⟨x₀,hx₀⟩)} := by
      intro p hp
      exact (v9  _ _).mpr (hcover ⟨x₀,hx₀⟩ p hp)
    have hprime' : (uh  k {(fun i=>y i ⟨x₀,hx₀⟩)}).IsPrime :=xu
    rw [hmax.eq_of_le hprime'.ne_top hpoint,dsq]
    exact hone
end
end yz
end
section
namespace yz
noncomputable section
open aR oR we MvPolynomial
open scoped BigOperators
end
end yz
end
section
namespace zP
noncomputable section
open aR oR we yz MvPolynomial Filter MeasureTheory
open scoped BigOperators Pointwise Topology
end
end zP
end
section
namespace aaq
noncomputable section
open zP MvPolynomial
open scoped Pointwise
end
end aaq
end
section
namespace aaq
noncomputable section
open zP MvPolynomial
open scoped Pointwise
variable {A:Fin 4→aU Exponent}
end
end aaq
end
section
namespace aaq
noncomputable section
end
end aaq
end
section
namespace aeC
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
end
end aeC
end
section
namespace aeC
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
end
end aeC
end
section
namespace aaq
noncomputable section
open zP
variable {A:Fin 4→aU Exponent}
end
end aaq
end
section
namespace aA2
noncomputable section
open aR oR we
end
end aA2
end
section
namespace aeC
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
end
end aeC
end
section
namespace aA2
noncomputable section
open aR oR we yz MvPolynomial
end
end aA2
end
section
namespace as3
noncomputable section
open zP aaq MvPolynomial
open scoped Pointwise
variable {A:Fin 4→aU Exponent}
end
end as3
end
section
namespace dm9
noncomputable section
open aR oR we yz MvPolynomial
open RingTheory.Sequence
open scoped Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end dm9
end
section
namespace Qp
open aR yz
end Qp
end
section
namespace Qp
noncomputable section
open aR yz MeasureTheory Set
end
end Qp
end
section
namespace as3
noncomputable section
open zP aaq MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {A:Fin 4→aU Exponent}
end
end as3
end
section
namespace abG
noncomputable section
open we yz zP MvPolynomial
end
end abG
end
section
namespace aA1
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
end
end aA1
end
section
namespace aeC
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
end
end aeC
end
section
namespace Qp
noncomputable section
open aR oR we yz MvPolynomial
open scoped BigOperators Pointwise
end
end Qp
end
section
namespace Qp
noncomputable section
open aR oR yz MeasureTheory
open scoped BigOperators Pointwise
end
end Qp
end
section
namespace aA1
noncomputable section
open aR oR Polynomial MvPolynomial
end
end aA1
end
section
namespace abG
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
section Branch
variable {L:Type} [lV L]
end Branch
section Rank
variable {L:Type} [lV L]
end Rank
section IsolatedPoints
open scoped Function
variable {L:Type} [lV L]
end IsolatedPoints
end
end abG
end
section
namespace bjy
noncomputable section
open aR oR we aeC Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end bjy
end
section
namespace aY0
noncomputable section
open aaq as3 MvPolynomial
end
end aY0
end
section
namespace ac0
noncomputable section
open MvPolynomial
open scoped BigOperators
variable {k σ:Type} [lV k] [vj σ]
end
end ac0
end
section
namespace abG
noncomputable section
open we zP MvPolynomial
open scoped TensorProduct
end
end abG
end
section
namespace aA1
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
end
end aA1
end
section
namespace ac0
noncomputable section
open MvPolynomial
open scoped BigOperators Function
variable {k σ:Type} [lV k] [vj σ]
end
end ac0
end
section
namespace ana
noncomputable section
open DdK1 aR oR Polynomial PolynomialDifferential
open scoped BigOperators nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end ana
end
section
namespace aA2
noncomputable section
open aR oR we yz MvPolynomial
end
end aA2
end
section
namespace aeB
noncomputable section
open aR oR yz MeasureTheory
open scoped BigOperators Pointwise
end
end aeB
end
section
namespace ac0
noncomputable section
open aR oR we yz MvPolynomial
open scoped BigOperators Pointwise
end
end ac0
end
section
namespace aeB
noncomputable section
open yz MeasureTheory MvPolynomial
open scoped BigOperators Pointwise
end
end aeB
end
section
namespace aY0
noncomputable section
open as3 MvPolynomial
end
end aY0
end
section
namespace aA1
noncomputable section
open aR oR MvPolynomial
open scoped Polynomial
end
end aA1
end
section
set_option backward.isDefEq.respectTransparency false
namespace aA9
noncomputable section
open zP MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end aA9
end
section
namespace bRg
noncomputable section
open Algebra KaehlerDifferential MvPolynomial
open scoped BigOperators IntermediateField.algebraAdjoinAdjoin
end
end bRg
end
section
namespace aeB
noncomputable section
open aR oR yz Qp MeasureTheory Filter
open scoped BigOperators Pointwise Topology
end
end aeB
end
section
namespace bz3
noncomputable section
open aR oR MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
end
end bz3
end
section
namespace abG
noncomputable section
open we yz zP MvPolynomial
end
end abG
end
section
namespace aFQ
noncomputable section
open aR oR we aeC Polynomial
end
end aFQ
end
section
namespace aF0
noncomputable section
open DdK1 aR cu Polynomial
open ana
end
end aF0
end
section
namespace cxS
noncomputable section
open we yz abG MvPolynomial IsLocalRing
open scoped TensorProduct
end
end cxS
end
section
namespace aFQ
noncomputable section
open aR oR we aeC Polynomial
open scoped BigOperators
end
end aFQ
end
section
namespace Mc
noncomputable section
open Polynomial Matrix
end
end Mc
end

end Merged6967_DdBG

section Merged6967_DdP6Defs
set_option Elab.async false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 12000
section
open _root_ renaming Finset.range→aU
set_option autoImplicit true
section
namespace bzq
open xE Finset
open scoped BigOperators

end bzq
end
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5
noncomputable section
open Polynomial Matrix CoreDefinitions Code gR ProximityPrize.Benchmark
open scoped BigOperators NNReal
abbrev a08:=DdP1.a08
abbrev target :a08:=⟨179876,0x1415c51a,0x40000000,2325,0x3b633efb605881a,0x22a0a042c6b0⟩
abbrev dw:=target.dw
end
end P5
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6
noncomputable section
open Polynomial Matrix CoreDefinitions Code gR ProximityPrize.Benchmark
open scoped BigOperators NNReal
abbrev a08:=DdP1.a08
abbrev target :a08:=⟨179759,0x141a0fff,0x40000000,2378,0x3d0c80576cde0d0,0x2f43b2e8c5a9⟩
abbrev dw:=target.dw
abbrev LM:=target.listBound
end
end P6
end

end Merged6967_DdP6Defs

section Merged6967_DdZgdIx1d
set_option Elab.async false






















































set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming AddCommGroup→vi,AdjoinRoot.algebraMap_eq'→zm,AdjoinRoot.mk→pQ,AdjoinRoot.mk_C→zi,AdjoinRoot.of→t7,Algebra→lI,Algebra.IsAlgebraic→v8,Algebra.TensorProduct.includeRight→t5,Algebra.TensorProduct.tensorQuotientEquiv→C9,Algebra.algebraMap→lz,Algebra.trdeg→ oy,CommRing→n5,DFunLike.congr_fun→pU,FaithfulSMul→wA,Field→c9,Finset→pz,Finset.le_sup→y5,Finset.sum_congr→uJ,Finset.sum_le_sum→th,FractionRing→ oD,Function.Injective→ oz,Function.Injective.isDomain→zc,Function.Surjective→Fa,Ideal→cy,Ideal.Quotient.eq_zero_iff_mem→vh,Ideal.Quotient.factor→vk,Ideal.Quotient.factor_mk→xI,Ideal.Quotient.factorₐ→z8,Ideal.Quotient.liftₐ→C5,Ideal.Quotient.mk→lJ,Ideal.Quotient.mk_surjective→u5,Ideal.Quotient.mkₐ→FQ,Ideal.map_map→xu,Ideal.mem_span_singleton_self→z9,Ideal.quotientEquivAlg→EP,Ideal.span→ oj,IntermediateField.adjoin→FR,Irreducible→nI,IsDomain→ oK,IsFractionRing→sI,IsFractionRing.lift_algebraMap→Et,IsFractionRing.map→pL,IsLocalRing.residue→vZ,IsLocalization.map_eq→qM,IsScalarTower→sH,IsScalarTower.algebraMap_apply→uh,IsScalarTower.of_algHom→Cy,IsScalarTower.of_algebraMap_eq→FK
open _root_ renaming LinearMap.finrank_range_of_inj→zR,LinearMap.ker→t8,LinearMap.mulLeft→zE,LinearMap.range→vG,Module.Finite→ ox,Module.Flat→zh,Module.Flat.lTensor_preserves_injective_linearMap→Dz,Module.finrank→ ov,MvPolynomial→aU,MvPolynomial.C→mD,MvPolynomial.X→nq,MvPolynomial.aeval→qy,MvPolynomial.affineDegree→uz,MvPolynomial.affineHilbertPolynomial→ oq,MvPolynomial.algebraTensorAlgEquiv→wB,MvPolynomial.algebraTensorAlgEquiv_tmul→vw,MvPolynomial.eval→qJ,MvPolynomial.eval₂Hom→ oZ,MvPolynomial.eval₂Hom_C→t3,MvPolynomial.eval₂Hom_X'→Fz,MvPolynomial.map→lV,MvPolynomial.mapAlgHom→Dw,MvPolynomial.map_C→wR,MvPolynomial.map_X→x7,MvPolynomial.mk_mem_quotientDegreeLE→zf,MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective→zk,MvPolynomial.quotientBidegreeLE→yJ,MvPolynomial.quotientDegreeLE→ oY,MvPolynomial.rename→Bf,MvPolynomial.restrictBidegree→t4,MvPolynomial.ringHom_ext→yU,MvPolynomial.support_map_subset→Ar,MvPolynomial.totalDegree_C→zg,MvPolynomial.totalDegree_finsetSum_le→Du,MvPolynomial.totalDegree_mul→ze,MvPolynomial.trdeg_of_isDomain→yQ,MvPolynomial.weightedHomogeneousComponent→uW,MvPolynomial.zeroLocus→qG,Nat.card_fin→yB,Option→nX,Option.some_ne_none→Ee,Polynomial→vj,Polynomial.C→pG,Polynomial.C_mul_X_pow_eq_monomial→Eg,Polynomial.X→qx,Polynomial.coe_eval₂RingHom→xW,Polynomial.coe_mapRingHom→sS,Polynomial.coeff_map→zS
open _root_ renaming Polynomial.eval_map_apply→Ea,Polynomial.eval₂_C→yo,Polynomial.induction_on'→Av,Polynomial.mapRingHom→t6,Polynomial.map_C→wY,Polynomial.map_injective→Df,Polynomial.map_map→EK,Polynomial.ringHom_ext→Aa,Polynomial.sylvester→zd,Polynomial.trdeg_of_isDomain→Au,RingHom.comp_apply→p6,RingHom.ext→xm,RingHom.ker→p7,RingHom.ker_isPrime→Ef,Submodule→u8,Subtype.ext→v9,Subtype.val_injective→FU,Sum.inr→p9,TensorProduct.AlgebraTensorModule.lTensor→yl,TensorProduct.inductionOn→z7,add_zero→p5,congrArg→qz,exists_finite_inj_algHom_of_fg→xL,faithfulSMul_iff_algebraMap_injective→vl,inferInstance→vH,injective_iff_map_eq_zero→C4,le_sup_left→yL,map_add→qU,map_mul→pC,smul_eq_mul→u9,trdeg_add_eq→qm,trdeg_eq_zero→t9,trdeg_le_of_injective→Dv
set_option autoImplicit true
section
namespace DQ
noncomputable section
open DdK1 cu Polynomial
open scoped BigOperators
end
end DQ
end
section
namespace Cu
noncomputable section
open DdK1 cu DQ
open scoped Polynomial BigOperators
end
end Cu
end
section
namespace Cu
noncomputable section
open DdK1 cu DQ
open scoped Polynomial BigOperators
end
end Cu
end
section
namespace ane
noncomputable section
open cu DQ MvPolynomial
end
end ane
end
section
namespace ane
noncomputable section
open cu DQ MvPolynomial
open scoped TensorProduct
end
end ane
end
section
namespace aqe
noncomputable section
open cu DQ MvPolynomial
end
end aqe
end
section
namespace aqe
noncomputable section
open cu DQ ane MvPolynomial
open scoped TensorProduct
end
end aqe
end
section
namespace aqe
noncomputable section
open MvPolynomial
end
end aqe
end
section
namespace MN
noncomputable section
open DdK1 cu Polynomial
open scoped BigOperators
end
end MN
end
section
namespace MN
noncomputable section
open Polynomial Finset DdK1 ProximityPrize.Benchmark
open scoped BigOperators
theorem aDW {α ι:Type*} [DecidableEq α] [DecidableEq ι]
    (marks :pz α) (nodes :pz ι) (B:α→pz ι) (x t cap:ℕ)
    (hB : ∀ a∈marks,B a⊆nodes∧(B a).card=x)
    (hpair : ∀ a∈marks,∀ b∈marks,a≠b→(B a∩B b).card≤t)
    (hocc : ∀ i∈nodes,(marks.filter fun a=>i∈B a).card≤ cap) :
    (marks.card*x)^2≤nodes.card*(marks.card*(x+(marks.card - 1)*t)) ∧
      marks.card*x≤nodes.card*cap:= by
  classical
  let occ (i:ι) :=(marks.filter fun a=>i∈B a).card
  have section_eq (V:pz ι) (hV:V⊆nodes) :
      (nodes.filter fun i=>i∈V)=V:= by
    ext i
    exact mem_filter.trans ⟨And.right,fun hi=>⟨hV hi,hi⟩⟩
  have first : ∑ i∈nodes,occ i=marks.card*x := by
    calc
      _ = ∑ a∈marks,(B a).card:= by
        simp only [occ,card_filter]
        rw [sum_comm]
        refine uJ rfl fun a ha => ?_
        rw [sum_boole,Nat.cast_id,section_eq _ (hB a ha).1]
      _ = _:= by rw [uJ rfl (fun a ha=>(hB a ha).2),sum_const,u9]
  have second : ∑ i∈nodes,occ i^2 =
      ∑ a∈marks,∑ b∈marks,(B a∩B b).card:= by
    simp only [occ,sq,card_filter]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    refine uJ rfl fun a ha => ?_
    rw [sum_comm]
    refine uJ rfl fun b _ => ?_
    have identity (i:ι) :
        (if i∈B a then 1 else 0:ℕ)*(if i∈B b then 1 else 0) =
          if i∈B a∩B b then 1 else 0:= by
      by_cases h₁:i∈B a <;> by_cases h₂:i∈B b <;> simp [h₁,h₂]
    simp_rw [identity]
    rw [sum_boole,Nat.cast_id,section_eq _ (inter_subset_left.trans (hB a ha).1)]
  have row (a :α) (ha :a∈marks) :
      ∑ b∈marks,(B a∩B b).card≤x+(marks.card - 1)*t:= by
    rw [← add_sum_erase marks _ ha,inter_self,(hB a ha).2]
    refine Nat.add_le_add_left ?_ _
    calc
      _ ≤ ∑ b∈marks.erase a,t:=th fun b hb =>
        hpair a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm
      _ = _:= by rw [sum_const,card_erase_of_mem ha,u9]
  have second_le : ∑ i∈nodes,occ i^2≤ marks.card*(x+(marks.card - 1)*t) := by
    rw [second]
    exact (th row).trans_eq (by rw [sum_const,u9])
  have cs :=sq_sum_le_card_mul_sum_sq (s :=nodes) (f :=occ)
  rw [first] at cs
  refine ⟨cs.trans (Nat.mul_le_mul_left _ second_le),?_⟩
  rw [← first,← u9,← sum_const]
  exact th hocc
end
end MN
end
section
namespace DQ
noncomputable section
open DdK1 cu Polynomial MvPolynomial Finset
open scoped BigOperators
end
end DQ
end
section
namespace Cu
noncomputable section
open DdK1 cu DQ
open scoped Polynomial
end
end Cu
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace aiO
noncomputable section
open DdK1 cu DQ Cu
open scoped Polynomial
open scoped TensorProduct
end
end aiO
end
section
set_option maxHeartbeats 800000
namespace aiO
noncomputable section
open DdK1 cu DQ Cu
open scoped Polynomial
end
end aiO
end
section
namespace XW
noncomputable section
open cu DQ Cu
open scoped BigOperators Polynomial
end
end XW
end
section
namespace XW
noncomputable section
open Algebra MvPolynomial cu DQ Cu
open scoped Polynomial
end
end XW
end
section
namespace XW
noncomputable section
open MvPolynomial
variable {k σ:Type*} [c9 k]
variable [Finite σ]
end
end XW
end
section
namespace UI
noncomputable section
open DdK1 cu DQ Cu
open scoped Polynomial
end
end UI
end
section
namespace aiO
noncomputable section
open DdK1 cu DQ Cu
open scoped TensorProduct
end
end aiO
end
section
namespace aiN
noncomputable section
open cu DQ Cu UI
open scoped Polynomial
end
end aiN
end
section
namespace akS
noncomputable section
open cu Cu MvPolynomial
open scoped TensorProduct
variable {F A:Type} [c9 F] [n5 A] [lI F A]
end
end akS
end
section
set_option maxHeartbeats 2000000
namespace aiO
noncomputable section
open DdK1 cu DQ Cu
end
end aiO
end

end Merged6967_DdZgdIx1d

section Merged6967_Fast022
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_2_3
open K1_13_2
open scoped BigOperators
def baseline (i : BlockIndex) : ℕ := blockBound i (fun _ => 0)
structure Powers where
  value : ℕ
  top : ℕ
  cubic : ℕ
def Powers.expand (p : Powers) : Fin 11 → ℕ :=
  ![p.value, 0, 0, p.top, 0, 0, 0, 0, 0, 0, p.cubic]
structure Window where
  gradeLo : ℕ
  gradeHi : ℕ
  offsetLo : ℕ
  offsetHi : ℕ
  diagonalLo : ℕ
  diagonalHi : ℕ
def Window.Contains (w : Window) (i : BlockIndex) : Prop :=
  w.gradeLo ≤ i.1.val ∧ i.1.val < w.gradeHi ∧
  w.offsetLo ≤ i.2.val ∧ i.2.val ≤ w.offsetHi ∧
  w.diagonalLo ≤ i.1.val + i.2.val ∧ i.1.val + i.2.val ≤ w.diagonalHi
instance (w : Window) (i : BlockIndex) : Decidable (w.Contains i) := by
  unfold Window.Contains
  infer_instance
def w1 : Window := ⟨1004, 2008, 993, 1581, 3000, 3070⟩
def w2 : Window := ⟨2008, 3012, 322, 1062, 3000, 3419⟩
def w3 : Window := ⟨3012, 3514, 23, 408, 3333, 3796⟩
def w4 : Window := ⟨3514, 4013, 0, 282, 3537, 4170⟩
def baselineSumOn (S : Finset BlockIndex) (lo hi : ℕ) : ℕ :=
  ∑ i ∈ S, if lo ≤ i.1.val ∧ i.1.val < hi then baseline i else 0
abbrev baselineSum (lo hi : ℕ) : ℕ := baselineSumOn Finset.univ lo hi
def savings (i : BlockIndex) (p : Powers) : ℕ := baseline i - blockBound i p.expand
def savingsSum (w : Window) (p : BlockIndex → Powers) : ℕ :=
  ∑ i : BlockIndex, if w.Contains i then savings i (p i) else 0
theorem residualFlag_expand (F : Flag) (p : Powers) :
    residualFlag F p.expand =
      ⟨F.degree - ((p.value : ℤ) + p.top + 3 * p.cubic),
        F.lower - (3 * (p.top : ℤ) + 2 * p.cubic),
        F.upper - (3 * (p.top : ℤ) + 3 * p.cubic),
        F.cap - ((p.top : ℤ) + p.cubic),
        F.order - (2 * (p.top : ℤ) + 3 * p.cubic)⟩ := by
  simp [residualFlag, Powers.expand, Fin.sum_univ_succ, factorFlag]
  ring_nf
  simp
end K1_13_2_3
end
section
namespace K1_13_2_3
open K1_13_2
open scoped BigOperators
private def difference (k : ℕ) (f : ℤ → ℤ) (u : ℤ) : ℤ := f u - f (u - k)
private theorem difference_comm (a b : ℕ) (f : ℤ → ℤ) :
    difference a (difference b f) = difference b (difference a f) := by
  funext u
  unfold difference
  rw [show u - (a : ℤ) - b = u - (b : ℤ) - a by ring]
  ring
private theorem difference_mul (k n : ℕ) (f : ℤ → ℤ) (u : ℤ) :
    difference (k * n) f u = ∑ j ∈ Finset.range n, difference k f (u - (k : ℤ) * j) := by
  induction n with
  | zero => simp [difference]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [difference, Nat.cast_mul, Nat.cast_succ]
    rw [show u - (k : ℤ) * ((n : ℤ) + 1) = u - (k : ℤ) * n - k by ring]
    ring
private theorem difference_mono_of_dvd {a b : ℕ} {f : ℤ → ℤ} (h : a ∣ b)
    (hm : Monotone (difference a f)) : Monotone (difference b f) := by
  obtain ⟨n, rfl⟩ := h
  intro u v huv
  rw [difference_mul, difference_mul]
  exact Finset.sum_le_sum fun j _ => hm (sub_le_sub_right huv _)
private theorem mono_of_difference_nonneg {f : ℤ → ℤ}
    (h : ∀ u, 0 ≤ difference 1 f u) : Monotone f := by
  intro u v huv
  let n := (v - u).toNat
  have hn : (n : ℤ) = v - u := Int.toNat_of_nonneg (by omega)
  have hz : 0 ≤ difference (1 * n) f v := by
    rw [difference_mul]
    exact Finset.sum_nonneg fun _ _ => h _
  simpa only [difference, Nat.cast_one, Nat.cast_mul, one_mul, hn, sub_sub_cancel,
    sub_nonneg] using hz
def polyDen (q r : ℤ) : ℤ :=
  2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
theorem scaled_denominator (u : ℤ) (hu : 0 ≤ u) :
    2 * denominator u = polyDen (u / 6) (u % 6) := by
  let q := u / 6
  let r := u % 6
  simp only [denominator, not_lt.mpr hu, ite_false, polyDen]
  change 2 * (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) = _
  have h := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at h
  change _ = 2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
  linear_combination h + q * twice_half r + (57 + 6 * r) * twice_half q
private theorem scaled_shift (u k : ℤ) (h : k ≤ u) :
    2 * denominator (u - k) = polyDen (u / 6 + (u % 6 - k) / 6) ((u % 6 - k) % 6) := by
  rw [scaled_denominator _ (by omega)]
  congr 1 <;> omega
theorem denominator_of_neg (u : ℤ) (h : u < 0) : denominator u = 0 := by
  simp only [denominator, ite_eq_left h]
private theorem simple_step (u : ℤ) :
    difference 1 (difference 2 (difference 3 denominator)) u = if u < 0 then 0 else 1 := by
  by_cases hu : u < 0
  · simp (disch := omega) only [difference, denominator_of_neg, hu, sub_self, ite_true]
  by_cases hs : u < 8
  · interval_cases u <;> decide
  rw [ite_eq_right hu]
  have hf : difference 1 (difference 2 (difference 3 denominator)) u =
      denominator u - denominator (u - 1) - denominator (u - 2) +
        denominator (u - 4) + denominator (u - 5) - denominator (u - 6) := by
    simp only [difference, Nat.cast_ofNat, Nat.cast_one]
    rw [show u - 2 - 3 = u - 5 by ring, show u - 1 - 3 = u - 4 by ring,
      show u - 1 - 2 = u - 3 by ring, show u - 3 - 3 = u - 6 by ring]
    ring
  rw [hf]
  apply (mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide))
  have hh (k : ℤ) (hk : k ≤ 8) := scaled_shift u k (by omega)
  have h0 := hh 0 (by decide)
  rw [sub_zero] at h0
  have h1 := hh 1 (by decide)
  have h2 := hh 2 (by decide)
  have h4 := hh 4 (by decide)
  have h5 := hh 5 (by decide)
  have h6 := hh 6 (by decide)
  have hd : 0 ≤ u % 6 := by omega
  have hb : u % 6 < 6 := by omega
  generalize u % 6 = r at h0 h1 h2 h4 h5 h6 hd hb
  interval_cases r <;> norm_num [polyDen] at h0 h1 h2 h4 h5 h6 <;>
    linear_combination (norm := ring_nf) h0 - h1 - h2 + h4 + h5 - h6
private theorem missing_one_step (u : ℤ) :
    difference 1 (difference 1 (difference 6 denominator)) u =
      if u < 0 ∨ u = 1 then 0 else 1 := by
  by_cases hu : u < 0
  · simp (disch := omega) only [difference, denominator_of_neg, hu, sub_self, true_or, ite_true]
  by_cases hs : u < 8
  · interval_cases u <;> decide
  rw [ite_eq_right (by omega)]
  have hf : difference 1 (difference 1 (difference 6 denominator)) u =
      denominator u - 2 * denominator (u - 1) + denominator (u - 2) -
        denominator (u - 6) + 2 * denominator (u - 7) - denominator (u - 8) := by
    simp only [difference, Nat.cast_ofNat, Nat.cast_one]
    rw [show u - 1 - 6 = u - 7 by ring, show u - 1 - 1 = u - 2 by ring,
      show u - 2 - 6 = u - 8 by ring]
    ring
  rw [hf]
  apply (mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide))
  have hh (k : ℤ) (hk : k ≤ 8) := scaled_shift u k (by omega)
  have h0 := hh 0 (by decide)
  rw [sub_zero] at h0
  have h1 := hh 1 (by decide)
  have h2 := hh 2 (by decide)
  have h6 := hh 6 (by decide)
  have h7 := hh 7 (by decide)
  have h8 := hh 8 (by decide)
  have hd : 0 ≤ u % 6 := by omega
  have hb : u % 6 < 6 := by omega
  generalize u % 6 = r at h0 h1 h2 h6 h7 h8 hd hb
  interval_cases r <;> norm_num [polyDen] at h0 h1 h2 h6 h7 h8 <;>
    linear_combination (norm := ring_nf) h0 - 2*h1 + h2 - h6 + 2*h7 - h8
private theorem difference_mono_three {a b c k l m : ℕ} (f : ℤ → ℤ)
    (ha : k ∣ a) (hb : l ∣ b) (hc : m ∣ c)
    (hm : Monotone (difference k (difference l (difference m f)))) :
    Monotone (difference a (difference b (difference c f))) := by
  have H₁ := difference_mono_of_dvd ha hm
  rw [difference_comm a l] at H₁
  have H₂ := difference_mono_of_dvd hb H₁
  rw [difference_comm b a, difference_comm b m, difference_comm a m] at H₂
  have H₃ := difference_mono_of_dvd hc H₂
  rwa [difference_comm c a, difference_comm c b] at H₃
private theorem simple_step_mono : Monotone (difference 1 (difference 2 (difference 3 denominator))) := by
  intro u v huv
  rw [simple_step, simple_step]
  split <;> split <;> omega
private theorem special_step_mono (a : ℕ) (ha : 2 ≤ a) :
    Monotone (difference a (difference 1 (difference 6 denominator))) := by
  apply mono_of_difference_nonneg
  intro u
  rw [difference_comm 1 a]
  simp only [difference]
  change 0 ≤ difference 1 (difference 1 (difference 6 denominator)) u -
    difference 1 (difference 1 (difference 6 denominator)) (u - a)
  rw [missing_one_step, missing_one_step]
  split <;> split <;> omega
private def rawCount (d : ℕ) : ℤ → ℤ :=
  difference (d + 1) (difference (d + 2) (difference (d + 3) denominator))
private theorem rawCount_mono (d : ℕ) : Monotone (rawCount d) := by
  unfold rawCount
  have hmod : d % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases hr : d % 6
  · exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
  · rw [difference_comm (d+2) (d+3), difference_comm (d+1) (d+3)]
    exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
  · rw [difference_comm (d+1) (d+2), difference_comm (d+1) (d+3), difference_comm (d+2) (d+3)]
    exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
  · rw [difference_comm (d+1) (d+2)]
    exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
  · have ha : 2 ≤ d + 1 := by omega
    rw [difference_comm (d+2) (d+3)]
    exact difference_mono_three _ (dvd_refl _) (one_dvd _) (by omega) (special_step_mono _ ha)
  · rw [difference_comm (d+1) (d+2), difference_comm (d+1) (d+3)]
    exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
private theorem rawCount_eq_zero (d : ℕ) (u : ℤ) (h : u < 0) : rawCount d u = 0 := by
  simp (disch := omega) only [rawCount, difference, denominator_of_neg, sub_self]
private theorem cumulative_eq_raw (d : ℕ) (u : ℤ) :
    cumulative d u = rawCount d (min u (3 * (d : ℤ))) := by
  by_cases hu : u < 0
  · rw [min_eq_left (by omega), rawCount_eq_zero _ _ hu]
    simp [cumulative, hu]
  · have hd : ¬ (d : ℤ) < 0 := by omega
    simp [cumulative, hu, hd, rawCount, difference]
    ring_nf
theorem cumulative_mono (d : ℕ) : Monotone (cumulative (d : ℤ)) := by
  intro u v huv
  rw [cumulative_eq_raw, cumulative_eq_raw]
  exact rawCount_mono d (min_le_min_right _ huv)
private theorem baseline_le_target (i : BlockIndex) :
    baseline i ≤ (targetCount (initialFlag i)).toNat := by
  have hk : kernelLower (initialFlag i) = oldCount (initialFlag i) - targetCount (initialFlag i) := by
    simp [kernelLower, initialFlag]
  unfold baseline blockBound
  dsimp
  split
  · exact Nat.zero_le _
  · apply Int.toNat_le_toNat
    apply (min_le_right _ _).trans
    have hm : kernelLower (initialFlag i) ≤ max 0 (max (kernelLower (initialFlag i))
        (kernelLower (residualFlag (initialFlag i) (fun _ => 0)))) :=
      (le_max_left _ _).trans (le_max_right _ _)
    omega
private theorem targetCount_low (s : Fin 4013) (j : Fin 4650) (hs : s.val < 551) :
    targetCount (initialFlag (s,j)) = cumulative (s.val : ℤ) (4649 - (s.val : ℤ) - j.val) -
      cumulative (s.val : ℤ) (1649 - (j.val : ℤ)) := by
  simp only [targetCount, initialFlag, offset, min_eq_left (show (s.val : ℤ) ≤ 1650 by omega)]
  rw [show 3000 - (s.val : ℤ) - ((j.val : ℤ) - 1650) - 1 -
    (-((j.val : ℤ) - 1650)) + s.val = (2999 : ℤ) by ring]
  norm_num only [Int.reduceLT, ite_false, Int.reduceDiv]
  rw [min_eq_left (show (s.val : ℤ) ≤ 749 by omega)]
  have hz (u : ℤ) : cumulative ((s.val : ℤ) - ((s.val : ℤ) + 1)) u = 0 := by
    simp [cumulative, show (s.val : ℤ) - ((s.val : ℤ) + 1) = -1 by ring]
  simp only [hz, sub_zero, add_zero]
  congr 1 <;> congr 1 <;> ring
private theorem sum_reverse_truncate (d a n : ℕ) (ha : a < n) :
    (∑ j ∈ Finset.range n, cumulative (d : ℤ) ((a : ℤ) - (j : ℤ))) =
      ∑ j ∈ Finset.range (a + 1), cumulative (d : ℤ) j := by
  calc
    _ = ∑ j ∈ Finset.range (a + 1), cumulative (d : ℤ) ((a : ℤ) - (j : ℤ)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hja
      have hlt : (a : ℤ) - (j : ℤ) < 0 := by rw [Finset.mem_range] at hja; omega
      simp [cumulative, hlt]
    _ = _ := by
      conv_rhs => rw [← Finset.sum_range_reflect (fun j => cumulative (d : ℤ) (j : ℤ)) (a+1)]
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      have hja := Finset.mem_range.mp hj
      rw [show a + 1 - 1 - j = a - j by omega, Nat.cast_sub (by omega)]
private theorem sum_target_low (s : Fin 4013) (hs : s.val < 551) :
    (∑ j : Fin 4650, targetCount (initialFlag (s,j))) =
      ((3000 - s.val : ℕ) : ℤ) * cumulative (s.val : ℤ) (3 * s.val) := by
  simp_rw [targetCount_low s _ hs]
  rw [Finset.sum_sub_distrib,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => cumulative (s.val : ℤ) (4649 - (s.val : ℤ) - j)),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => cumulative (s.val : ℤ) (1649 - (j : ℤ)))]
  rw [show (4649 : ℤ) - (s.val : ℤ) = ((4649 - s.val : ℕ) : ℤ) by omega]
  rw [sum_reverse_truncate _ _ _ (by omega)]
  have hr := sum_reverse_truncate s.val 1649 4650 (by decide)
  norm_num only [Nat.cast_ofNat] at hr
  rw [hr]
  rw [show 4649 - s.val + 1 = 1650 + (3000 - s.val) by omega, Finset.sum_range_add]
  rw [add_sub_cancel_left]
  have heq (j : ℕ) : cumulative (s.val : ℤ) ((1650 + j : ℕ) : ℤ) =
      cumulative (s.val : ℤ) (3 * s.val) := by
    rw [cumulative_eq_raw, cumulative_eq_raw, min_self, min_eq_right (by omega)]
  simp_rw [heq]
  simp
private theorem bound_grade_low (s : Fin 4013) (hs : s.val < 551) :
    (∑ j : Fin 4650, baseline (s,j)) ≤ (3000 - s.val) *
      (cumulative (s.val : ℤ) (3 * s.val)).toNat := by
  have hn (j : Fin 4650) : 0 ≤ targetCount (initialFlag (s,j)) := by
    rw [targetCount_low s j hs]
    exact sub_nonneg.mpr (cumulative_mono _ (by omega))
  have hc : 0 ≤ cumulative (s.val : ℤ) (3 * s.val) := by
    apply le_trans _ (cumulative_mono (s.val) (show -1 ≤ 3 * (s.val : ℤ) by omega))
    simp [cumulative]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4650)))
    (fun j _ => baseline_le_target (s,j))
  refine h.trans ?_
  exact_mod_cast (show ((∑ j : Fin 4650, (targetCount (initialFlag (s,j))).toNat : ℕ) : ℤ) ≤
    (((3000 - s.val) * (cumulative (s.val : ℤ) (3 * s.val)).toNat : ℕ) : ℤ) by
      rw [Nat.cast_sum, Nat.cast_mul]
      simp_rw [Int.toNat_of_nonneg (hn _)]
      rw [Int.toNat_of_nonneg hc, sum_target_low s hs])
private def gradeTotal (s : ℕ) : ℕ :=
  (3000 - s) * (cumulative (s : ℤ) (3 * s)).toNat
private def lowTotal : ℕ → ℕ
  | 0 => 0
  | n + 1 => lowTotal n + gradeTotal n
private theorem lowTotal_eq (n : ℕ) : lowTotal n = ∑ j ∈ Finset.range n, gradeTotal j := by
  induction n with
  | zero => simp [lowTotal]
  | succ n ih => rw [lowTotal, Finset.sum_range_succ, ih]
private def auxLowChunk (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | count + 1 => auxLowChunk start count + gradeTotal (start + count)
private theorem auxLowChunk_eq (start count : ℕ) :
    lowTotal (start + count) = lowTotal start + auxLowChunk start count := by
  induction count with
  | zero => simp [auxLowChunk]
  | succ count ih => rw [Nat.add_succ, lowTotal, auxLowChunk, ih, Nat.add_assoc]
private theorem auxLowChunk_extend {start count initial delta : ℕ}
    (hi : lowTotal start = initial) (hd : auxLowChunk start count = delta) :
    lowTotal (start + count) = initial + delta :=
  (auxLowChunk_eq start count).trans (congrArg₂ Nat.add hi hd)
private theorem auxLow_total_0 : lowTotal 0 = 0 := rfl
private theorem auxLow_total_16 : lowTotal 16 = 11581488 :=
  auxLowChunk_extend (count := 16) (delta := 11581488) auxLow_total_0 (by decide +kernel)
private theorem auxLow_total_32 : lowTotal 32 = 155781472 :=
  auxLowChunk_extend (count := 16) (delta := 144199984) auxLow_total_16 (by decide +kernel)
private theorem auxLow_total_48 : lowTotal 48 = 740303760 :=
  auxLowChunk_extend (count := 16) (delta := 584522288) auxLow_total_32 (by decide +kernel)
private theorem auxLow_total_64 : lowTotal 64 = 2260809408 :=
  auxLowChunk_extend (count := 16) (delta := 1520505648) auxLow_total_48 (by decide +kernel)
private theorem auxLow_total_80 : lowTotal 80 = 5396722416 :=
  auxLowChunk_extend (count := 16) (delta := 3135913008) auxLow_total_64 (by decide +kernel)
private theorem auxLow_total_96 : lowTotal 96 = 11007035424 :=
  auxLowChunk_extend (count := 16) (delta := 5610313008) auxLow_total_80 (by decide +kernel)
private theorem auxLow_total_112 : lowTotal 112 = 20126115408 :=
  auxLowChunk_extend (count := 16) (delta := 9119079984) auxLow_total_96 (by decide +kernel)
private theorem auxLow_total_128 : lowTotal 128 = 33959509376 :=
  auxLowChunk_extend (count := 16) (delta := 13833393968) auxLow_total_112 (by decide +kernel)
private theorem auxLow_total_144 : lowTotal 144 = 53879750064 :=
  auxLowChunk_extend (count := 16) (delta := 19920240688) auxLow_total_128 (by decide +kernel)
private theorem auxLow_total_160 : lowTotal 160 = 81422161632 :=
  auxLowChunk_extend (count := 16) (delta := 27542411568) auxLow_total_144 (by decide +kernel)
private theorem auxLow_total_176 : lowTotal 176 = 118280665360 :=
  auxLowChunk_extend (count := 16) (delta := 36858503728) auxLow_total_160 (by decide +kernel)
private theorem auxLow_total_192 : lowTotal 192 = 166303585344 :=
  auxLowChunk_extend (count := 16) (delta := 48022919984) auxLow_total_176 (by decide +kernel)
private theorem auxLow_total_208 : lowTotal 208 = 227489454192 :=
  auxLowChunk_extend (count := 16) (delta := 61185868848) auxLow_total_192 (by decide +kernel)
private theorem auxLow_total_224 : lowTotal 224 = 303982818720 :=
  auxLowChunk_extend (count := 16) (delta := 76493364528) auxLow_total_208 (by decide +kernel)
private theorem auxLow_total_240 : lowTotal 240 = 398070045648 :=
  auxLowChunk_extend (count := 16) (delta := 94087226928) auxLow_total_224 (by decide +kernel)
private theorem auxLow_total_256 : lowTotal 256 = 512175127296 :=
  auxLowChunk_extend (count := 16) (delta := 114105081648) auxLow_total_240 (by decide +kernel)
private theorem auxLow_total_272 : lowTotal 272 = 648855487280 :=
  auxLowChunk_extend (count := 16) (delta := 136680359984) auxLow_total_256 (by decide +kernel)
private theorem auxLow_total_288 : lowTotal 288 = 810797786208 :=
  auxLowChunk_extend (count := 16) (delta := 161942298928) auxLow_total_272 (by decide +kernel)
private theorem auxLow_total_304 : lowTotal 304 = 1000813727376 :=
  auxLowChunk_extend (count := 16) (delta := 190015941168) auxLow_total_288 (by decide +kernel)
private theorem auxLow_total_320 : lowTotal 320 = 1221835862464 :=
  auxLowChunk_extend (count := 16) (delta := 221022135088) auxLow_total_304 (by decide +kernel)
private theorem auxLow_total_336 : lowTotal 336 = 1476913397232 :=
  auxLowChunk_extend (count := 16) (delta := 255077534768) auxLow_total_320 (by decide +kernel)
private theorem auxLow_total_352 : lowTotal 352 = 1769207997216 :=
  auxLowChunk_extend (count := 16) (delta := 292294599984) auxLow_total_336 (by decide +kernel)
private theorem auxLow_total_368 : lowTotal 368 = 2101989593424 :=
  auxLowChunk_extend (count := 16) (delta := 332781596208) auxLow_total_352 (by decide +kernel)
private theorem auxLow_total_384 : lowTotal 384 = 2478632188032 :=
  auxLowChunk_extend (count := 16) (delta := 376642594608) auxLow_total_368 (by decide +kernel)
private theorem auxLow_total_400 : lowTotal 400 = 2902609660080 :=
  auxLowChunk_extend (count := 16) (delta := 423977472048) auxLow_total_384 (by decide +kernel)
private theorem auxLow_total_416 : lowTotal 416 = 3377491571168 :=
  auxLowChunk_extend (count := 16) (delta := 474881911088) auxLow_total_400 (by decide +kernel)
private theorem auxLow_total_432 : lowTotal 432 = 3906938971152 :=
  auxLowChunk_extend (count := 16) (delta := 529447399984) auxLow_total_416 (by decide +kernel)
private theorem auxLow_total_448 : lowTotal 448 = 4494700203840 :=
  auxLowChunk_extend (count := 16) (delta := 587761232688) auxLow_total_432 (by decide +kernel)
private theorem auxLow_total_464 : lowTotal 464 = 5144606712688 :=
  auxLowChunk_extend (count := 16) (delta := 649906508848) auxLow_total_448 (by decide +kernel)
private theorem auxLow_total_480 : lowTotal 480 = 5860568846496 :=
  auxLowChunk_extend (count := 16) (delta := 715962133808) auxLow_total_464 (by decide +kernel)
private theorem auxLow_total_496 : lowTotal 496 = 6646571665104 :=
  auxLowChunk_extend (count := 16) (delta := 786002818608) auxLow_total_480 (by decide +kernel)
private theorem auxLow_total_512 : lowTotal 512 = 7506670745088 :=
  auxLowChunk_extend (count := 16) (delta := 860099079984) auxLow_total_496 (by decide +kernel)
private theorem auxLow_total_528 : lowTotal 528 = 8444987985456 :=
  auxLowChunk_extend (count := 16) (delta := 938317240368) auxLow_total_512 (by decide +kernel)
private theorem auxLow_total_544 : lowTotal 544 = 9465707413344 :=
  auxLowChunk_extend (count := 16) (delta := 1020719427888) auxLow_total_528 (by decide +kernel)
private theorem lowTotal_check : lowTotal 551 = 9939265602560 :=
  auxLowChunk_extend (count := 7) (delta := 473558189216) auxLow_total_544 (by decide +kernel)
private theorem sum_cutoff (f : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    (∑ j ∈ Finset.range n, if j < m then f j else 0) = ∑ j ∈ Finset.range m, f j := by
  calc
    _ = ∑ j ∈ Finset.range m, if j < m then f j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono h)
      intro j _ hj
      rw [Finset.mem_range] at hj
      rw [ite_eq_right hj]
    _ = _ := Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
theorem baseline_low : baselineSum 0 551 ≤ 9939265602560 := by
  unfold baselineSum baselineSumOn
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [zero_le, true_and]
  calc
    _ ≤ ∑ s : Fin 4013, if s.val < 551 then gradeTotal s else 0 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s.val < 551
      · simpa only [ite_eq_left hs, gradeTotal] using bound_grade_low s hs
      · simp [hs]
    _ = ∑ j ∈ Finset.range 551, gradeTotal j := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < 551 then gradeTotal j else 0)]
      exact sum_cutoff gradeTotal (by decide)
    _ = _ := (lowTotal_eq _).symm.trans lowTotal_check
end K1_13_2_3
end
section
namespace K1_13_2_3
open K1_13_2
open scoped BigOperators
def c1 : Prop := baselineSum 551 1650 ≤ 196232494523570
def c2 : Prop := baselineSum 1650 2510 ≤ 101832665783054
def c3 : Prop := baselineSum 2510 4013 ≤ 36565173831277
def c4 : Prop := ∃ p : BlockIndex → Powers, 9573892230 ≤ savingsSum w1 p
theorem bound_le_baseline (i : BlockIndex) (p : Fin 11 → ℕ) :
    blockBound i p ≤ baseline i := by
  have hz (F : Flag) : residualFlag F (fun _ => 0) = F := by
    cases F
    simp [residualFlag]
  unfold baseline blockBound
  simp only [hz, max_self]
  split
  · rfl
  · apply Int.toNat_le_toNat
    apply min_le_min_left
    apply sub_le_sub_left
    exact max_le_max_left _ (le_max_left _ _)
private theorem sum_four_le {α : Type*} (S : Finset α)
    (a b c d f : α → ℕ) (h : ∀ i ∈ S, a i + b i + c i + d i ≤ f i) :
    (∑ i ∈ S, a i) + (∑ i ∈ S, b i) + (∑ i ∈ S, c i) + (∑ i ∈ S, d i) ≤
      ∑ i ∈ S, f i := by
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum h
private theorem sum_four_eq {α : Type*} (S : Finset α)
    (a b c d f : α → ℕ) (h : ∀ i ∈ S, f i = a i + b i + c i + d i) :
    (∑ i ∈ S, f i) = (∑ i ∈ S, a i) + (∑ i ∈ S, b i) + (∑ i ∈ S, c i) + (∑ i ∈ S, d i) := by
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl h
theorem sum_add_pointwise_eq {α : Type*} (S : Finset α)
    (f g t : α → ℕ) (h : ∀ i ∈ S, f i + g i = t i) :
    (∑ i ∈ S, f i) + (∑ i ∈ S, g i) = ∑ i ∈ S, t i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl h
private theorem baseline_parts_on (S : Finset BlockIndex) :
    (∑ i ∈ S, baseline i) = baselineSumOn S 0 551 + baselineSumOn S 551 1650 +
      baselineSumOn S 1650 2510 + baselineSumOn S 2510 4013 := by
  unfold baselineSumOn
  exact sum_four_eq S
    (fun i => if 0 ≤ i.1.val ∧ i.1.val < 551 then baseline i else 0)
    (fun i => if 551 ≤ i.1.val ∧ i.1.val < 1650 then baseline i else 0)
    (fun i => if 1650 ≤ i.1.val ∧ i.1.val < 2510 then baseline i else 0)
    (fun i => if 2510 ≤ i.1.val ∧ i.1.val < 4013 then baseline i else 0)
    baseline (fun i _ => by
      have h := i.1.isLt
      by_cases hs₁ : i.1.val < 551
      · have hn : ¬ 551 ≤ i.1.val := by omega
        have hn' : ¬ 1650 ≤ i.1.val := by omega
        have hn'' : ¬ 2510 ≤ i.1.val := by omega
        simp [hs₁, hn, hn', hn'']
      · have ha : 551 ≤ i.1.val := by omega
        by_cases hs₂ : i.1.val < 1650
        · have hn : ¬ 1650 ≤ i.1.val := by omega
          have hn' : ¬ 2510 ≤ i.1.val := by omega
          simp [hs₁, ha, hs₂, hn, hn']
        · have hb : 1650 ≤ i.1.val := by omega
          by_cases hs₃ : i.1.val < 2510
          · have hn : ¬ 2510 ≤ i.1.val := by omega
            simp [hs₁, hs₂, hb, hs₃, hn]
          · have hc : 2510 ≤ i.1.val := by omega
            simp [hs₁, hs₂, hs₃, hc, h])
theorem baseline_budget_on (S : Finset BlockIndex)
    (h₀ : baselineSumOn S 0 551 ≤ 9939265602560)
    (h₁ : baselineSumOn S 551 1650 ≤ 196232494523570)
    (h₂ : baselineSumOn S 1650 2510 ≤ 101832665783054)
    (h₃ : baselineSumOn S 2510 4013 ≤ 36565173831277) :
    (∑ i ∈ S, baseline i) ≤ 344569599740461 := calc
  _ = _ := baseline_parts_on S
  _ ≤ (9939265602560 + 196232494523570 + 101832665783054 + 36565173831277) :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h₀ h₁) h₂) h₃
  _ ≤ _ := by decide
def combine (p₁ p₂ p₃ p₄ : BlockIndex → Powers) (i : BlockIndex) : Powers :=
  if i.1.val < 2008 then p₁ i else if i.1.val < 3012 then p₂ i
  else if i.1.val < 3514 then p₃ i else p₄ i
theorem savings_parts (p₁ p₂ p₃ p₄ : BlockIndex → Powers) :
    savingsSum w1 p₁ + savingsSum w2 p₂ + savingsSum w3 p₃ + savingsSum w4 p₄ ≤
      ∑ i : BlockIndex, savings i (combine p₁ p₂ p₃ p₄ i) := by
  exact sum_four_le Finset.univ
    (fun i => if w1.Contains i then savings i (p₁ i) else 0)
    (fun i => if w2.Contains i then savings i (p₂ i) else 0)
    (fun i => if w3.Contains i then savings i (p₃ i) else 0)
    (fun i => if w4.Contains i then savings i (p₄ i) else 0)
    (fun i => savings i (combine p₁ p₂ p₃ p₄ i)) (fun i _ => by
      by_cases hs₁ : i.1.val < 2008
      · have hn₂ : ¬ w2.Contains i := by simp [w2, Window.Contains]; omega
        have hn₃ : ¬ w3.Contains i := by simp [w3, Window.Contains]; omega
        have hn₄ : ¬ w4.Contains i := by simp [w4, Window.Contains]; omega
        simp only [combine, hs₁, ite_true, hn₂, hn₃, hn₄, ite_false, add_zero]
        split <;> simp
      · have hn₁ : ¬ w1.Contains i := by simp [w1, Window.Contains, hs₁]
        by_cases hs₂ : i.1.val < 3012
        · have hn₃ : ¬ w3.Contains i := by simp [w3, Window.Contains]; omega
          have hn₄ : ¬ w4.Contains i := by simp [w4, Window.Contains]; omega
          simp only [combine, hs₁, hs₂, ite_false, ite_true, hn₁, hn₃, hn₄, zero_add, add_zero]
          split <;> simp
        · have hn₂ : ¬ w2.Contains i := by simp [w2, Window.Contains, hs₂]
          by_cases hs₃ : i.1.val < 3514
          · have hn₄ : ¬ w4.Contains i := by simp [w4, Window.Contains]; omega
            simp only [combine, hs₁, hs₂, hs₃, ite_false, ite_true, hn₁, hn₂, hn₄, zero_add, add_zero]
            split <;> simp
          · have hn₃ : ¬ w3.Contains i := by simp [w3, Window.Contains, hs₃]
            simp only [combine, hs₁, hs₂, hs₃, ite_false, hn₁, hn₂, hn₃, zero_add]
            split <;> simp)
end K1_13_2_3
end

end Merged6967_Fast022

section Merged6967_Fast029
set_option Elab.async false





















set_option Elab.async false

-- merged module Pack_K1_13_6_1_4Geometry
section Merged_Pack_K1_13_6_1_4Geometry
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_6
noncomputable section
open Polynomial K1 K1_13
open scoped BigOperators
abbrev GenericField := FractionRing (Polynomial Geom)
abbrev GeoField := AlgebraicClosure GenericField
abbrev GeoJets := MvPolynomial (Fin 4) GeoField
def genericCoeffs : (Polynomial Geom) →+* GeoField :=
  (algebraMap GenericField GeoField).comp (algebraMap (Polynomial Geom) GenericField)
def toGeneric (P : Row 4) : GeoJets := MvPolynomial.map genericCoeffs P
def evalGeneric (S : (Polynomial Geom)) : GeoJets →+* GeoField :=
  MvPolynomial.eval (fun i => genericCoeffs (jet S i))
def markIdeal (S : (Polynomial Geom)) : Ideal GeoJets := RingHom.ker (evalGeneric S)
def intersectionIdeal (f Q : Row 4) : Ideal GeoJets :=
  Ideal.span {toGeneric f, toGeneric Q}
def divisorIdeal (surface : Ideal GeoJets) (E : Row 4) : Ideal GeoJets :=
  surface ⊔ Ideal.span {toGeneric E}
def cycleLength (J surface : Ideal GeoJets) (hp : surface.IsPrime) : ℕ∞ :=
  letI := hp
  let L := Localization.AtPrime surface
  Module.length L (L ⧸ J.map (algebraMap GeoJets L))
def separant (g : Row 4) : Row 4 := MvPolynomial.pderiv 3 g
def coefficientDerivative (P : Row 4) : Row 4 :=
  ∑ m ∈ P.support, MvPolynomial.monomial m (derivative (P.coeff m))
def partialFlow (P : Row 4) : Row 4 :=
  coefficientDerivative P +
  ∑ i : Fin 3, MvPolynomial.C (C ((i.val + 1 : ℕ) : Geom)) *
    MvPolynomial.X i.succ * MvPolynomial.pderiv i.castSucc P
def flowNumerator (g P : Row 4) : Row 4 :=
  separant g * partialFlow P - partialFlow g * separant P
def clearedStep (g : Row 4) (a : ℕ) (P : Row 4) : Row 4 :=
  separant g * flowNumerator g P - (a : Row 4) * flowNumerator g (separant g) * P
def jetNumerator (g : Row 4) : ℕ → Row 4
  | 0 => MvPolynomial.X 0
  | n+1 => clearedStep g (2*n) (jetNumerator g n)
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength+1)
def Invariant (g : Row 4) (surface : Ideal GeoJets) : Prop :=
  ∀ P : Row 4, toGeneric P ∈ surface → toGeneric (flowNumerator g P) ∈ surface
def CanonicalChart (f : Row 4) (surface : Ideal GeoJets) (r : ℕ) : Prop :=
  r < (shape f).t ∧ (∀ j ≤ r, toGeneric ((separant^[j]) f) ∈ surface) ∧
    toGeneric (separant ((separant^[r]) f)) ∉ surface
structure HighChart (f Q : Row 4) (l : ℕ) (S : (Polynomial Geom))
    (surface : Ideal GeoJets) (r : ℕ) : Prop where
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  point : surface ≤ markIdeal S
  chart : CanonicalChart f surface r
  regular : atJet (separant ((separant^[r]) f)) S ≠ 0
  invariant : Invariant ((separant^[r]) f) surface
def HighMark (f Q : Row 4) (l : ℕ) (S : (Polynomial Geom)) : Prop :=
  ∃ surface r, HighChart f Q l S surface r
def CurveSections (Γ : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop := by
  classical
  exact ∀ x a : K, (∃ γ ∈ Γ, (s γ).eval x ≠ a) →
    (Γ.filter fun γ => (s γ).eval x = a).card ≤ d
structure Pieces (Γ : Finset K) where
  n : ℕ
  piece : Fin n → Finset K
  subset : ∀ i, piece i ⊆ Γ
  degree : Fin n → ℕ
def Pieces.union {Γ : Finset K} (C : Pieces Γ) : Finset K := by
  classical exact Finset.univ.biUnion C.piece
def Pieces.total {Γ : Finset K} (C : Pieces Γ) : ℕ := ∑ i, C.degree i
def Pieces.curves {Γ : Finset K} (C : Pieces Γ) (s : K → (Polynomial K)) : Prop :=
  ∀ i, CurveSections (C.piece i) s (C.degree i)
def SurfaceSections (Γ : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop := by
  classical
  exact ∀ x a : K, (∃ γ ∈ Γ, (s γ).eval x ≠ a) →
    let H := Γ.filter fun γ => (s γ).eval x = a
    ∃ C : Pieces H, H ⊆ C.union ∧ C.curves s ∧ (∀ i, 0 < C.degree i) ∧ C.total ≤ d
def Pieces.surfaces {Γ : Finset K} (C : Pieces Γ) (s : K → (Polynomial K)) : Prop :=
  ∀ i, SurfaceSections (C.piece i) s (C.degree i)
end
end K1_13_6
end
section
namespace K1_13_6
noncomputable section
open Polynomial K1_13
open scoped BigOperators
@[simp] private theorem coeff_coefficientDerivative (P : Row 4) (m : Fin 4 →₀ ℕ) :
    (coefficientDerivative P).coeff m = derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coefficientDerivative_C (p : (Polynomial Geom)) :
    coefficientDerivative (MvPolynomial.C p) = MvPolynomial.C (derivative p) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coefficientDerivative]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
private theorem coefficientDerivative_add (P Q : Row 4) :
    coefficientDerivative (P+Q) = coefficientDerivative P + coefficientDerivative Q := by
  ext m
  simp
private theorem coefficientDerivative_mul_X (P : Row 4) (j : Fin 4) :
    coefficientDerivative (P * MvPolynomial.X j) = coefficientDerivative P * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_coefficientDerivative, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs <;> simp
private theorem eval_chain (P : Row 4) (a : Fin 4 → (Polynomial Geom)) :
    derivative (MvPolynomial.eval a P) = MvPolynomial.eval a (coefficientDerivative P) +
      ∑ i, derivative (a i) * MvPolynomial.eval a (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [coefficientDerivative_C]
  | add P Q hP hQ =>
    simp only [map_add, coefficientDerivative_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P j ih =>
    rw [map_mul, MvPolynomial.eval_X, derivative_mul, ih, coefficientDerivative_mul_X,
      map_mul, MvPolynomial.eval_X]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval_X,
      mul_add, Finset.sum_add_distrib]
    have left : (∑ i, derivative (a i) *
          (MvPolynomial.eval a (MvPolynomial.pderiv i P) * a j)) =
        (∑ i, derivative (a i) * MvPolynomial.eval a (MvPolynomial.pderiv i P)) * a j := by
      simp only [Finset.sum_mul, mul_assoc]
    have right : (∑ i, derivative (a i) *
          (MvPolynomial.eval a P * MvPolynomial.eval a (MvPolynomial.pderiv i (MvPolynomial.X j)))) =
        derivative (a j) * MvPolynomial.eval a P := by
      simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]
    rw [left, right]
    ring
private theorem derivative_hasse (S : (Polynomial Geom)) (k : ℕ) :
    derivative (hasseDeriv k S) = C ((k+1 : ℕ) : Geom) * hasseDeriv (k+1) S := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := Geom) 1 k) S
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul, C_eq_natCast, Nat.add_comm, add_mul] using h
private theorem eval_partialFlow (P : Row 4) (S : (Polynomial Geom)) :
    derivative (atJet P S) = atJet (partialFlow P) S +
      derivative (jet S (3 : Fin 4)) * atJet (separant P) S := by
  unfold atJet partialFlow separant
  rw [eval_chain, Fin.sum_univ_castSucc, map_add, map_sum]
  rw [← add_assoc]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [jet, derivative_hasse, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Fin.val_castSucc, Fin.val_succ]
theorem eval_flowNumerator (g P : Row 4) (S : (Polynomial Geom)) (hg : atJet g S = 0) :
    atJet (flowNumerator g P) S = atJet (separant g) S * derivative (atJet P S) := by
  have hz : atJet (partialFlow g) S +
      derivative (jet S (3 : Fin 4)) * atJet (separant g) S = 0 := by
    rw [← eval_partialFlow, hg, map_zero]
  unfold flowNumerator
  rw [eval_partialFlow]
  change (MvPolynomial.eval (jet S)) (_ - _) = _
  rw [map_sub, map_mul, map_mul]
  change atJet (separant g) S * atJet (partialFlow P) S -
      atJet (partialFlow g) S * atJet (separant P) S = _
  linear_combination -atJet (separant P) S * hz
private theorem cleared_product_rule (a : ℕ) (U V : (Polynomial Geom)) :
    U * (U * derivative (U^a * V)) - (a : (Polynomial Geom)) * (U * derivative U) * (U^a * V) =
      U^(a+2) * derivative V := by
  cases a with
  | zero => simp [pow_two, mul_assoc]
  | succ a =>
    rw [derivative_mul, derivative_pow, Nat.succ_sub_one,
      pow_add U (a+1) 2, pow_succ' U a]
    simp only [C_eq_natCast]
    push_cast
    ring
theorem eval_jetNumerator (g : Row 4) (S : (Polynomial Geom)) (hg : atJet g S = 0) (n : ℕ) :
    atJet (jetNumerator g n) S =
      atJet (separant g) S ^ (2*n) * ((derivative (R := Geom))^[n]) S := by
  induction n with
  | zero =>
    simp [jetNumerator, atJet, jet]
  | succ n ih =>
    let e := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
    change e (clearedStep g (2*n) (jetNumerator g n)) = _
    unfold clearedStep
    rw [map_sub, map_mul, map_mul, map_mul, map_natCast]
    change atJet (separant g) S * atJet (flowNumerator g (jetNumerator g n)) S -
      (↑(2*n) : (Polynomial Geom)) * atJet (flowNumerator g (separant g)) S *
        atJet (jetNumerator g n) S = _
    rw [eval_flowNumerator _ _ _ hg, eval_flowNumerator _ _ _ hg, ih,
      cleared_product_rule,
      show 2*(n+1) = 2*n+2 by omega, Function.iterate_succ_apply']
end
end K1_13_6
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial K1_13 K1_13_6
abbrev TaylorIndex := Fin taylorLength
abbrev GeoPoint := Fin 4 → GeoField
def Chamber (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j
def GeoFits (g : GeoJets) (p : Shape) : Prop :=
  g.totalDegree ≤ p.b ∧ g.weightedTotalDegree Fin.val ≤ p.j ∧ g.degreeOf 3 ≤ p.t
structure TaylorChart where
  denom : GeoJets
  numerator : TaylorIndex → GeoJets
  initial : ∀ i : Fin 4,
    numerator (i.castLE (by decide : 4 ≤ taylorLength)) = MvPolynomial.X i * denom
def TaylorChart.Fits (C : TaylorChart) (h : Shape) : Prop :=
  GeoFits C.denom h ∧ ∀ i, GeoFits (C.numerator i) h
def TaylorChart.Recovers (C : TaylorChart) (S : (Polynomial Geom)) : Prop :=
  evalGeneric S C.denom ≠ 0 ∧
    ∀ i, evalGeneric S (C.numerator i) =
      evalGeneric S C.denom * genericCoeffs (hasseDeriv i.val S)
abbrev AffineForm := GeoField × (TaylorIndex → GeoField)
def TaylorChart.pullback (C : TaylorChart) (a : AffineForm) : GeoJets :=
  MvPolynomial.C a.1 * C.denom + ∑ i, MvPolynomial.C (a.2 i) * C.numerator i
def Isolated (f g u v : GeoJets) (y : GeoPoint) : Prop :=
  RingHom.ker (MvPolynomial.eval y) ∈ (Ideal.span ({f, g, u, v} : Set GeoJets)).minimalPrimes
def SliceBound (f g : GeoJets) (C : TaylorChart) (d : ℕ) : Prop :=
  ∀ a b : AffineForm, ∀ points : Finset GeoPoint,
    (∀ y ∈ points, Isolated f g (C.pullback a) (C.pullback b) y ∧
      MvPolynomial.eval y C.denom ≠ 0) → points.card ≤ d
end
end K1_13_7_1
end
section
namespace K1_13_6_1
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
abbrev anchorBox (f : Row 4) : Shape := (shape f).chamber
def HasMark (Γ : Finset K) (s : K → (Polynomial K)) (surface : Ideal GeoJets) : Prop :=
  ∃ γ ∈ Γ, surface ≤ markIdeal (extend (s γ))
def tangentCut (g P : Row 4) (a : ℕ) : Row 4 :=
  (flowNumerator g)^[a] P
def DerivativeWeight (f : Row 4) (surface : Ideal GeoJets) (r w : ℕ) : Prop :=
  let g := (separant^[r]) f
  ¬ f ∣ g ∧ InBox (shape g) (anchorBox f) ∧ 0 < w ∧
    ∃ hZ : (intersectionIdeal f g).IsMinimalPrime surface,
      cycleLength (intersectionIdeal f g) surface hZ.isPrime = (w : ℕ∞)
structure CurveOnFactor (f : Row 4) (C : Ideal GeoJets) : Prop where
  prime : C.IsPrime
  dim : ringKrullDim (GeoJets ⧸ C) = 1
  contains : toGeneric f ∈ C
abbrev SectionIndex (a : Shape) := Fin 4 → Fin (a.b + 1)
abbrev SectionField (a : Shape) := FractionRing (MvPolynomial (SectionIndex a) GeoField)
abbrev SectionJets (a : Shape) := MvPolynomial (Fin 4) (SectionField a)
def boxMonomials (a : Shape) : Finset (SectionIndex a) :=
  Finset.univ.filter fun m =>
    (∑ i, (m i).val) ≤ a.b ∧
      (∑ i, i.val * (m i).val) ≤ a.j ∧ (m 3).val ≤ a.t
def genericSection (a : Shape) : SectionJets a :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial (SectionIndex a) GeoField)
      (SectionField a) (MvPolynomial.X m)) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
def sectionDegree (C : Ideal GeoJets) (a : Shape) : ℕ :=
  let J := C.map (MvPolynomial.map (algebraMap GeoField (SectionField a))) ⊔
    Ideal.span {genericSection a}
  Module.finrank (SectionField a) (SectionJets a ⧸ J)
end
end K1_13_6_1
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open RingTheory.Sequence
open scoped Pointwise
theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
theorem toGeneric_injective : Function.Injective toGeneric :=
  MvPolynomial.map_injective _ genericCoeffs_injective
private theorem mem_smul_top_iff_dvd {R : Type*} [CommRing R] (f x : R) :
    x ∈ f • (⊤ : Submodule R R) ↔ f ∣ x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, smul_eq_mul]
  exact exists_congr fun _ => eq_comm
attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem proper_generic (f g : Row 4) (hf : Irreducible f) (hg : ¬ f ∣ g) :
    IsRelPrime (toGeneric f) (toGeneric g) := by
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  have hreg : IsWeaklyRegular (Row 4) [f, g] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
    refine ⟨mul_right_injective₀ hp.ne_zero, ?_⟩
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
    intro x hx
    exact (mem_smul_top_iff_dvd f x).mpr
      ((hp.dvd_mul.mp ((mem_smul_top_iff_dvd f (g * x)).mp hx)).resolve_left hg)
  let _ : Algebra (Polynomial Geom) GeoField := genericCoeffs.toAlgebra
  let _ : Module.IsTorsionFree (Polynomial Geom) GeoField :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr genericCoeffs_injective
  have hflat : Module.Flat (Row 4) GeoJets :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv (Polynomial Geom) (Row 4) GeoField GeoJets).symm.toLinearEquiv
  have h := hreg.of_flat (S := GeoJets)
  change IsWeaklyRegular GeoJets [toGeneric f, toGeneric g] at h
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at h
  rintro a ⟨b, hb⟩ ⟨c, hc⟩
  have hzero : toGeneric f ≠ 0 := fun hz => hp.ne_zero (toGeneric_injective (hz.trans (map_zero _).symm))
  have hprod : toGeneric g * b = toGeneric f * c := by rw [hc, hb]; ring
  have hdiv : toGeneric f ∣ b := (mem_smul_top_iff_dvd _ _).mp
    (mem_of_isSMulRegular_quotient_of_smul_mem h.2
      ((mem_smul_top_iff_dvd _ _).mpr ⟨c, hprod⟩))
  obtain ⟨q, hq⟩ := hdiv
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (hb ▸ hzero)
  have hu : a * q = 1 := mul_left_cancel₀ hb0 (by
    calc
      b * (a * q) = (a * b) * q := by ring
      _ = b := by rw [← hb, ← hq]
      _ = b * 1 := (mul_one _).symm)
  exact ⟨⟨a, q, hu, by rw [mul_comm, hu]⟩, rfl⟩
end
end K1_13_7_1
end
section
namespace K1_13_6_1_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators
def FullChamber (a : Shape) : Prop := Chamber a ∧ 0 < a.t
abbrev PairSectionIndex (a h : Shape) := SectionIndex a ⊕ SectionIndex h
abbrev PairSectionField (a h : Shape) :=
  FractionRing (MvPolynomial (PairSectionIndex a h) GeoField)
def sectionWith {σ : Type*} (a : Shape) (ι : SectionIndex a → σ) :
    MvPolynomial (Fin 4) (FractionRing (MvPolynomial σ GeoField)) :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial σ GeoField)
      (FractionRing (MvPolynomial σ GeoField)) (MvPolynomial.X (ι m))) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
def surfaceDegree (surface : Ideal GeoJets) (a h : Shape) : ℕ :=
  let F := PairSectionField a h
  let I := surface.map (MvPolynomial.map (algebraMap GeoField F)) ⊔
    Ideal.span {sectionWith a (Sum.inl : SectionIndex a → PairSectionIndex a h),
      sectionWith h (Sum.inr : SectionIndex h → PairSectionIndex a h)}
  Module.finrank F (MvPolynomial (Fin 4) F ⧸ I)
abbrev pairIdeal (F G : GeoJets) : Ideal GeoJets := Ideal.span {F, G}
end
end K1_13_6_1_4
end
section
namespace K1_13_6_1_4
noncomputable section
open MvPolynomial K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
private theorem krullDim_of_polynomial_normalization {k R : Type*} [Field k]
    [CommRing R] [IsDomain R] {d : ℕ} [Algebra (MvPolynomial (Fin d) k) R]
    [FaithfulSMul (MvPolynomial (Fin d) k) R] [Module.Finite (MvPolynomial (Fin d) k) R] :
    ringKrullDim R = (d : WithBot ℕ∞) := by
  let B := MvPolynomial (Fin d) k
  have hB : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [← hB]
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B R))
    intro x y hxy
    exact Ideal.IsIntegral.under_lt_under (show x.asIdeal < y.asIdeal from hxy)
  · obtain ⟨b, hb, hd⟩ := Ideal.exists_isPrime_le_height (n := d) hB.ge
    obtain ⟨z, hz⟩ :=
      Algebra.IsIntegral.comap_surjective B R (⟨b, hb⟩ : PrimeSpectrum B)
    have hz' : z.asIdeal.under B = b := congrArg PrimeSpectrum.asIdeal hz
    have hle := Ideal.height_under_le_height (R := B) z.asIdeal
    rw [hz'] at hle
    calc
      ringKrullDim B = (d : WithBot ℕ∞) := hB
      _ ≤ (z.asIdeal.height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (hd.trans hle)
      _ ≤ ringKrullDim R := Ideal.height_le_ringKrullDim_of_isPrime
private theorem krullDim_of_finite_hom {k R : Type*} [Field k] [CommRing R] [IsDomain R]
    {d : ℕ} (g : MvPolynomial (Fin d) k →+* R) (hg : Function.Injective g)
    (hgfin : g.Finite) : ringKrullDim R = (d : WithBot ℕ∞) := by
  let algebra := g.toAlgebra
  let := algebra
  let faithful : FaithfulSMul (MvPolynomial (Fin d) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let finite : Module.Finite (MvPolynomial (Fin d) k) R := hgfin
  exact @krullDim_of_polynomial_normalization k R _ _ _ d algebra faithful finite
theorem dim_eq_Hilbert {k σ : Type*} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    ringKrullDim (MvPolynomial σ k ⧸ I) =
      ((affineHilbertPolynomial I).natDegree : WithBot ℕ∞) := by
  obtain ⟨d, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have hH := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hgfin hg
  rw [Nat.card_fin] at hH
  rw [hH]
  exact krullDim_of_finite_hom g.toRingHom hg hgfin
theorem pair_dimension {F G : GeoJets} (hF : F ≠ 0) (hproper : IsRelPrime F G)
    {surface : Ideal GeoJets} (hZ : (pairIdeal F G).IsMinimalPrime surface) :
    ringKrullDim (GeoJets ⧸ surface) = 2 := by
  let := hZ.isPrime
  have hFZ : Ideal.span {F} ≤ surface :=
    le_trans (Ideal.span_mono (by simp)) hZ.le
  obtain ⟨D, hD, hDZ⟩ := Ideal.exists_minimalPrimes_le hFZ
  let := hD.isPrime
  have hD0 : D ≠ ⊥ := fun e =>
    hF (Ideal.mem_bot.mp (e ▸ hD.le (Ideal.subset_span (by simp))))
  have hDh : D.height = 1 :=
    le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ D hD)
      (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hD0))
  obtain ⟨a, ha, hap⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hD.isPrime hD0
  have heq := Ideal.eq_span_singleton_of_height_eq_one hDh ha hap
  have hGD : G ∉ D := by
    intro hG
    have hFa : a ∣ F := Ideal.mem_span_singleton.mp (heq ▸ hD.le (Ideal.subset_span (by simp)))
    have hGa : a ∣ G := Ideal.mem_span_singleton.mp (heq ▸ hG)
    exact hap.not_isUnit (hproper hFa hGa)
  have hpair : pairIdeal F G ≤ D ⊔ Ideal.span {G} := by
    rw [pairIdeal, Ideal.span_insert]
    exact sup_le (hD.le.trans le_sup_left) le_sup_right
  have hcut : (D ⊔ Ideal.span {G}).IsMinimalPrime surface :=
    ⟨⟨hZ.isPrime, sup_le hDZ ((Ideal.span_mono (by simp)).trans hZ.le)⟩,
      fun J hJ hJZ => hZ.2 ⟨hJ.1, hpair.trans hJ.2⟩ hJZ⟩
  have hDdeg := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hD
  have hZdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hGD hcut
  rw [Nat.card_fin] at hDdeg
  have hdeg : (affineHilbertPolynomial surface).natDegree = 2 := by omega
  simp [dim_eq_Hilbert surface, hdeg]
theorem curve_of_proper_cut {f P : Row 4} {surface C : Ideal GeoJets}
    (hZ : surface.IsPrime) (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (hf : toGeneric f ∈ surface) (hP : toGeneric P ∉ surface)
    (hC : (divisorIdeal surface P).IsMinimalPrime C) : CurveOnFactor f C := by
  let := hZ
  let := hC.isPrime
  have hZdeg : (affineHilbertPolynomial surface).natDegree = 2 := by
    have hd := (dim_eq_Hilbert surface).symm.trans hdim
    exact_mod_cast hd
  have hCdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hP hC
  have hd : (affineHilbertPolynomial C).natDegree = 1 := by omega
  have hle : surface ≤ C := (show surface ≤ divisorIdeal surface P from le_sup_left).trans hC.le
  exact ⟨hC.isPrime, by simp [dim_eq_Hilbert C, hd], hle hf⟩
end
end K1_13_6_1_4
end

end Merged_Pack_K1_13_6_1_4Geometry

-- merged module Fast023
section Merged_Fast023
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_14
noncomputable section
open K1 Polynomial
open scoped BigOperators
abbrev L := AlgebraicClosure K
abbrev FX := FractionRing (Polynomial L)
abbrev Seeds := MvPolynomial (Fin 2) FX
abbrev Equation := Polynomial Seeds
def liftPoly (g : (Polynomial K)) : (Polynomial L) := g.map (algebraMap K L)
def atX (g : (Polynomial K)) : FX := algebraMap (Polynomial L) FX (liftPoly g)
def seedEmbedding : K →+* FX :=
  (algebraMap (Polynomial L) FX).comp ((Polynomial.C : L →+* (Polynomial L)).comp (algebraMap K L))
def graphEval (z : K) : Seeds →+* FX :=
  MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z) ^ p]
def atMark (f : Equation) (z : K) (S : (Polynomial K)) : FX :=
  f.eval₂ (graphEval z) (atX S)
abbrev Jet := Polynomial Equation
structure Shape where
  m : ℕ
  B : ℕ
  J : ℕ
  U : ℕ
  deriving DecidableEq
structure Band where
  endpoint : ℕ
  yBound : ℕ
  seedBound : ℕ
  multiplicity : ℕ
  jetBound : ℕ
  vBound : ℕ
  subbankSeeds : ℕ
def band (w : ℤ) : Band :=
  if w ≤ 3554 then ⟨3554,5,144,836,1164,247,19371⟩
  else if w ≤ 8249 then ⟨8249,4,98,358,500,105,6798⟩
  else if w ≤ 23999 then ⟨23999,4,47,358,500,105,4860⟩
  else ⟨32680,4,36,358,500,105,3913⟩
def SeedBound (f : Equation) (b : ℕ) : Prop :=
  ∀ i, (f.coeff i).totalDegree ≤ b
def triangle (U : ℕ) : ℕ := (U + 1) * (U + 2) / 2
def slots (U spent : ℕ) : ℕ :=
  if spent ≤ U then triangle (U - spent) else 0
abbrev Banks := Shape → ℕ → Submodule FX Jet
def shapeSum (s : Shape) (g : ℕ → ℕ → ℕ) : ℕ :=
  ∑ q ∈ Finset.range (s.B+1), ∑ j ∈ Finset.range (min q s.J+1), g q j
def sourceDebit (h : ℕ) (s : Shape) : ℕ :=
  triangle s.U * 262144 * shapeSum s (fun q i => s.m + min q s.J - (q + 2*i)) +
    2*h*(s.U+1)*shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q))
def terminalShape (w : ℤ) : Shape :=
  let b := band w
  ⟨b.multiplicity, b.jetBound, b.vBound, b.subbankSeeds⟩
def scheduled (w : ℤ) : List Shape :=
  let sub := terminalShape w
  if w ≤ 3554 then
    [⟨59,82,18,1899⟩,⟨136,190,40,8441⟩,⟨66,92,21,2076⟩,⟨150,210,44,9356⟩,
     ⟨73,102,23,2261⟩,⟨164,229,48,10272⟩,⟨80,112,25,2455⟩,⟨178,249,52,11191⟩,
     ⟨94,131,30,2824⟩,⟨213,298,62,12959⟩,⟨115,160,36,3401⟩,⟨262,366,77,15611⟩,
     ⟨136,190,43,4204⟩,⟨325,454,96,19187⟩,⟨178,248,56,5332⟩,⟨409,572,121,24615⟩,
     ⟨241,336,78,7235⟩,⟨570,797,169,33523⟩,⟨325,453,104,9976⟩,⟨759,1061,224,46271⟩,
     ⟨836,1164,247,273617⟩, sub]
  else
    [⟨45,63,14,812⟩,⟨84,118,24,2907⟩,⟨57,80,18,1041⟩,⟨114,160,33,3775⟩,
     ⟨81,114,26,1383⟩,⟨144,203,42,5064⟩,⟨123,173,40,2173⟩,⟨231,325,67,8061⟩,
     ⟨358,500,105,66251⟩, sub]
def jetAt (P : Jet) (z : K) (S : (Polynomial K)) : FX :=
  P.eval₂ (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
def translateSeed (i : Fin 2) : Seeds →+* Polynomial Seeds :=
  MvPolynomial.eval₂Hom (C.comp MvPolynomial.C)
    (fun j => C (MvPolynomial.X j : Seeds) + if j = i then Polynomial.X (R := Seeds) else 0)
def seedHasse (i : Fin 2) (r : ℕ) (P : Jet) : Jet :=
  P.sum fun j g => monomial j (g.sum fun k c => monomial k ((translateSeed i c).coeff r))
structure JetSource {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) : Prop where
  nested : ∀ s ∈ scheduled M.overhead, ∀ s' ∈ scheduled M.overhead,
    s.m = s'.m → s.B = s'.B → s.J = s'.J → s.U ≤ s'.U →
    ∀ W W', W ≤ W' → rows s W ≤ rows s' W'
  necessary : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m*180265 → ∀ P ∈ rows s W,
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ j i,
    ((P.coeff j).coeff i) ≠ 0 →
      i+j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U
  leading : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, P ≠ 0 →
    (P.leadingCoeff.natDegree + P.natDegree)*(131071-M.overhead.toNat) ≤ W + P.natDegree
  shift : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ i r,
    seedHasse i r P ∈ rows s (W + 2*M.overhead.toNat*r)
  floor_bound : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m*180265 →
    (∀ q ≤ s.B, ∀ j ≤ min q s.J, q*(131071-M.overhead.toNat) ≤ W+1+j) →
    triangle s.U * shapeSum s (fun q j => W+1+j - q*(131071-M.overhead.toNat)) ≤
      sourceDebit M.overhead.toNat s + ∑ t ∈ Finset.range (W+1), Module.finrank FX (rows s t)
end
end K1_14
end
section
namespace K1_14
noncomputable section
open K1 Polynomial
open scoped BigOperators
end
end K1_14
end
section
namespace K1_14
noncomputable section
open K1 Polynomial
theorem trim (P : (Polynomial L)) (h : ℕ) (hh : h ≤ P.natDegree) :
    ∃ H : (Polynomial L), H.Monic ∧ H.natDegree = h ∧ H ∣ P := by
  classical
  have hc : 0 < (P.roots.powersetCard h).card := by
    rw [Multiset.card_powersetCard, IsAlgClosed.card_roots_eq_natDegree]
    exact Nat.choose_pos hh
  obtain ⟨s, hs⟩ := Multiset.card_pos_iff_exists_mem.mp hc
  obtain ⟨hle, hsize⟩ := Multiset.mem_powersetCard.mp hs
  exact ⟨_, monic_multisetProd_X_sub_C s, (natDegree_multiset_prod_X_sub_C_eq_card s).trans hsize,
    (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)).trans P.prod_multiset_X_sub_C_dvd⟩
theorem twist_lift (P : (Polynomial K)) :
    liftPoly (P.map twist) = (liftPoly P).map (frobenius L p) := by
  simp only [liftPoly, Polynomial.map_map, twist, RingHom.frobenius_comm]
end
end K1_14
end

end Merged_Fast023

-- merged module Fast029
section Merged_Fast029
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_14_2
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
structure Stage where
  reserve : ℕ
  cheap : Shape
  layered : Shape
def stages : List Stage :=
  [⟨0, ⟨59,82,18,1899⟩, ⟨136,190,40,8441⟩⟩,
   ⟨1, ⟨66,92,21,2076⟩, ⟨150,210,44,9356⟩⟩,
   ⟨2, ⟨73,102,23,2261⟩, ⟨164,229,48,10272⟩⟩,
   ⟨3, ⟨80,112,25,2455⟩, ⟨178,249,52,11191⟩⟩,
   ⟨5, ⟨94,131,30,2824⟩, ⟨213,298,62,12959⟩⟩,
   ⟨8, ⟨115,160,36,3401⟩, ⟨262,366,77,15611⟩⟩,
   ⟨12, ⟨136,190,43,4204⟩, ⟨325,454,96,19187⟩⟩,
   ⟨18, ⟨178,248,56,5332⟩, ⟨409,572,121,24615⟩⟩,
   ⟨28, ⟨241,336,78,7235⟩, ⟨570,797,169,33523⟩⟩,
   ⟨42, ⟨325,453,104,9976⟩, ⟨759,1061,224,46271⟩⟩]
def full : Shape := ⟨836,1164,247,273617⟩
def shapes : List Shape := full :: stages.flatMap (fun s => [s.cheap, s.layered])
def bufferedAt (w : ℤ) (r : ℕ) (s : Shape) : ℕ :=
  s.m * 180265 - 1 - 2 * w.toNat * r
def UsesSeed (G : Jet) : Prop :=
  ∃ j i, 0 < ((G.coeff j).coeff i).totalDegree
abbrev ODE := Polynomial (Polynomial FX)
def fixedAt (G : ODE) (S : (Polynomial K)) : FX :=
  G.eval₂ (evalRingHom (atX S)) (atX S.derivative)
def FixedEquation {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (T : Finset K) (B J : ℕ) : Prop :=
  ∃ G : ODE, G ≠ 0 ∧ G.natDegree ≤ J ∧
    (∀ j i, ((G.coeff j).coeff i) ≠ 0 → i+j ≤ B) ∧
    ∀ γ ∈ T, fixedAt G (F.scalar γ) = 0
def fixedKeys : List (ℕ × ℕ) := (507836, 93976) :: shapes.map (fun s => (s.B, s.J))
def endpointDegree : ℕ := 134625
def fixedPrice (B J : ℕ) : ℕ :=
  let d := endpointDegree
  let t := 2*d-3
  let a := 1+t*(B-1)
  let v := min a (t*(J-1)+d)
  let gap := 180265-d
  (81879*((B-J)*v+J*a)+gap-1)/gap+B^2
def fixedTotal : ℕ := (fixedKeys.map fun k => fixedPrice k.1 k.2).sum
def directPrice : ℕ :=
  5980 + ((p+1)*1052972+19635660) + (p+1)*(shapes.map Shape.U).sum + 310966947964
def lossSeedCap : ℕ := 220891211
def lossYCap : ℕ := 4783514411
def movingPrice : ℕ := 86954269798767161
abbrev Ambient := MvPolynomial (Fin 4) FX
abbrev RootAmbient := MvPolynomial (Fin 3) FX
def rootSeeds : Seeds →+* RootAmbient :=
  (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3))).toRingHom
def rootIncl : RootAmbient →+* Ambient :=
  (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4))).toRingHom
def toRoot : Equation →+* RootAmbient := eval₂RingHom rootSeeds (MvPolynomial.X 2)
def toJet : Jet →+* Ambient := eval₂RingHom (rootIncl.comp toRoot) (MvPolynomial.X 3)
def rootMarkHom (z : K) (S : (Polynomial K)) : RootAmbient →+* FX :=
  MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z)^p, atX S]
def jetMarkHom (z : K) (S : (Polynomial K)) : Ambient →+* FX :=
  MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z)^p, atX S, atX S.derivative]
private theorem eval_root (a b y : FX) (f : Equation) :
    MvPolynomial.eval ![a,b,y] (toRoot f) = f.eval₂ (MvPolynomial.eval ![a,b]) y := by
  have hseed : (MvPolynomial.eval ![a,b,y]).comp rootSeeds = MvPolynomial.eval ![a,b] := by
    apply RingHom.ext
    intro g
    change MvPolynomial.eval ![a,b,y] (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3)) g) = _
    rw [MvPolynomial.eval_rename]
    have hvec : ![a,b,y] ∘ Fin.castLE (by decide : 2 ≤ 3) = ![a,b] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec]
  change MvPolynomial.eval ![a,b,y] (f.eval₂ rootSeeds (MvPolynomial.X 2)) = _
  rw [Polynomial.hom_eval₂, hseed, MvPolynomial.eval_X]
  rfl
private theorem eval_incl (a b y v : FX) (f : RootAmbient) :
    MvPolynomial.eval ![a,b,y,v] (rootIncl f) = MvPolynomial.eval ![a,b,y] f := by
  change MvPolynomial.eval ![a,b,y,v] (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4)) f) = _
  rw [MvPolynomial.eval_rename]
  have hvec : ![a,b,y,v] ∘ Fin.castLE (by decide : 3 ≤ 4) = ![a,b,y] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
theorem eval_rootIncl_toRoot (z : K) (S : (Polynomial K)) (f : Equation) :
    jetMarkHom z S (rootIncl (toRoot f)) = atMark f z S :=
  (eval_incl (seedEmbedding z) _ _ _ (toRoot f)).trans (eval_root (seedEmbedding z) _ _ f)
theorem eval_toJet (z : K) (S : (Polynomial K)) (P : Jet) :
    jetMarkHom z S (toJet P) = jetAt P z S := by
  have h : (jetMarkHom z S).comp (rootIncl.comp toRoot) =
      eval₂RingHom (graphEval z) (atX S) := by
    exact RingHom.ext (eval_rootIncl_toRoot z S)
  have hv : jetMarkHom z S (MvPolynomial.X 3) = atX S.derivative := by
    simp [jetMarkHom]
  change jetMarkHom z S (P.eval₂ (rootIncl.comp toRoot) (MvPolynomial.X 3)) = _
  rw [Polynomial.hom_eval₂, h, hv]
  rfl
def OnJet (I : Ideal Ambient) (z : K) (S : (Polynomial K)) : Prop :=
  I ≤ RingHom.ker (jetMarkHom z S)
def OnRoot (I : Ideal RootAmbient) (z : K) (S : (Polynomial K)) : Prop :=
  I ≤ RingHom.ker (rootMarkHom z S)
abbrev SeedField := FractionRing Seeds
def generic (i : Fin 2) : SeedField :=
  algebraMap Seeds SeedField (MvPolynomial.X i)
def seedLine {n : ℕ} (i j : Fin n) : MvPolynomial (Fin n) SeedField :=
  MvPolynomial.X i + MvPolynomial.C (generic 0) * MvPolynomial.X j -
    MvPolynomial.C (generic 1)
def ySection {n : ℕ} (i : Fin n) : MvPolynomial (Fin n) SeedField :=
  MvPolynomial.X i - MvPolynomial.C (generic 1)
abbrev CoordinateRing {R : Type} [CommRing R] (I : Ideal R) := R ⧸ I
abbrev JetSeedSection (I : Ideal Ambient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {seedLine 0 1})
abbrev JetYSection (I : Ideal Ambient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {ySection 2})
abbrev RootSeedSection (I : Ideal RootAmbient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {seedLine 0 1})
abbrev RootYSection (I : Ideal RootAmbient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {ySection 2})
def LossCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (T : Finset K) : Prop :=
  ∃ cs : Finset (Ideal Ambient),
    (∀ I ∈ cs, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 1 ∧
      Module.Finite SeedField (JetSeedSection I) ∧
      0 < Module.finrank SeedField (JetSeedSection I) ∧
      Module.Finite SeedField (JetYSection I)) ∧
    (∑ I ∈ cs, Module.finrank SeedField (JetSeedSection I)) ≤ lossSeedCap ∧
    (∑ I ∈ cs, Module.finrank SeedField (JetYSection I)) ≤ lossYCap ∧
    ∀ γ ∈ T, ∃ I ∈ cs, OnJet I (M.label γ) (F.scalar γ)
def SmallRootCurve (I : Ideal RootAmbient) (g H : ℕ) : Prop :=
  I.IsPrime ∧
    ∃ C₀ : MvPolynomial (Fin 2) L, Irreducible C₀ ∧
      I.comap rootSeeds =
        Ideal.span {(MvPolynomial.map
          ((algebraMap (Polynomial L) FX).comp (Polynomial.C : L →+* (Polynomial L))) C₀)} ∧
      Module.Finite SeedField (RootSeedSection I) ∧
      Module.finrank SeedField (RootSeedSection I) = C₀.totalDegree * g ∧
      Module.Finite SeedField (RootYSection I) ∧
      Module.finrank SeedField (RootYSection I) ≤ H
abbrev FibreRing := MvPolynomial (Fin 2) SeedField
def mapGenericSeed : Ambient →+* FibreRing :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
    ![MvPolynomial.C (generic 0), MvPolynomial.C (generic 1), MvPolynomial.X 0, MvPolynomial.X 1]
abbrev OverSeeds (I : Ideal Ambient) :=
  CoordinateRing (I.map mapGenericSeed)
def mapGenericJets : Ambient →+* FibreRing :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C (generic 0), MvPolynomial.C (generic 1)]
abbrev OverJets (I : Ideal Ambient) :=
  CoordinateRing (I.map mapGenericJets)
structure RetainedParents (rows : Banks) where
  ideals : Finset (Ideal Ambient)
  prime : ∀ I ∈ ideals, I.IsPrime
  seed_finite : ∀ I ∈ ideals, Module.Finite SeedField (OverSeeds I)
  seed_size : ∀ I ∈ ideals, 0 < Module.finrank SeedField (OverSeeds I) ∧
    Module.finrank SeedField (OverSeeds I) < p
  jet_finite : ∀ I ∈ ideals, Module.Finite SeedField (OverJets I)
  jet_size : ∀ I ∈ ideals, 0 < Module.finrank SeedField (OverJets I) ∧
    Module.finrank SeedField (OverJets I) < p
  terminal : ∀ I ∈ ideals, ∀ P ∈ rows full (full.m * 180265 - 1), toJet P ∈ I
structure Geometry {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) where
  direct : Finset K
  lost : Finset K
  kept : Finset K
  fixedGroups : (ℕ × ℕ) → Finset K
  parents : RetainedParents rows
  direct_card : direct.card ≤ directPrice
  fixed_eq : ∀ k ∈ fixedKeys, fixedGroups k ⊆ Γ ∧ FixedEquation F (fixedGroups k) k.1 k.2
  lost_subset : lost ⊆ Γ
  loss_cover : LossCover M F lost
  kept_subset : kept ⊆ Γ
  kept_cover : ∀ γ ∈ kept, ∃ I ∈ parents.ideals, OnJet I (M.label γ) (F.scalar γ)
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ (∃ k ∈ fixedKeys, γ ∈ fixedGroups k) ∨ γ ∈ lost ∨ γ ∈ kept
end
end K1_14_2
end
section
namespace K1_14_2
noncomputable section
open K1 K1_14 Polynomial
set_option maxRecDepth 12000 in
private theorem ledger (w : ℤ) (hw : w ≤ 3554) :
    directPrice + fixedTotal + movingPrice ≤ highPrefix w := by
  have he : highPrefix w = 132117856182247703 := by simp [highPrefix, hw]
  rw [he]
  decide +kernel
end
end K1_14_2
end
section
namespace K1_14_2_1
open K1_14 K1_14_2
def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * 180265 - 2 * h * r
def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)
def rawVolume (h r : ℕ) (s : Shape) : ℕ :=
  triangle s.U * shapeSum s (rawWidth h r s)
def movingCeiling (h : ℕ) (s : Shape) : ℕ :=
  triangle s.U * shapeSum s (fun _ j => 2 * h * j)
end K1_14_2_1
end
section
set_option maxSynthPendingDepth 8
namespace K1_14_2_1
noncomputable section
open K1_14 K1_14_2 Polynomial UniqueFactorizationMonoid
private def divisible (V : Submodule FX Jet) (G : Jet) : Submodule FX V where
  carrier := {Q | G ∣ (Q : Jet)}
  zero_mem' := dvd_zero G
  add_mem' := fun hP hQ => dvd_add hP hQ
  smul_mem' a := by
    rintro Q ⟨R, hR⟩
    exact ⟨a • R, by
      change a • (Q : Jet) = G * (a • R)
      rw [hR, mul_smul_comm]⟩
theorem exists_layered (P : Jet) (hP : P ≠ 0) (V : Submodule FX Jet)
    (hn : ∃ Q ∈ V, Q ≠ 0)
    (hproper : ∀ G : Jet, Irreducible G → G ∣ P → 0 < G.natDegree → UsesSeed G →
      ∃ Q ∈ V, ¬ G ∣ Q) :
    ∃ Q ∈ V, Q ≠ 0 ∧
      ∀ G : Jet, Irreducible G → G ∣ P → 0 < G.natDegree → UsesSeed G → ¬ G ∣ Q := by
  classical
  let : Infinite FX := Infinite.of_injective _ (IsFractionRing.injective (Polynomial L) FX)
  let I := {H : Jet // H ∈ factors P}
  let : Finite I := Set.finite_coe_iff.mpr (factors P).finite_toSet
  let tests : Option I → Submodule FX V := fun k =>
    match k with
    | none => ⊥
    | some H =>
      if ∃ G : Jet, Irreducible G ∧ G ∣ P ∧ 0 < G.natDegree ∧ UsesSeed G ∧
          Associated G H.val then divisible V H.val else ⊥
  have bot_proper : (⊥ : Submodule FX V) ≠ ⊤ := by
    obtain ⟨Q, hQ, hnQ⟩ := hn
    intro heq
    have hmem : (⟨Q, hQ⟩ : V) ∈ (⊥ : Submodule FX V) := heq ▸ Submodule.mem_top
    exact hnQ (congrArg Subtype.val ((Submodule.mem_bot FX).mp hmem))
  have ht : ∀ k, tests k ≠ ⊤ := by
    intro k
    cases k with
    | none => exact bot_proper
    | some H =>
      change (if _ then divisible V H.val else ⊥) ≠ ⊤
      split_ifs with h
      · obtain ⟨G, hi, hd, hv, hs, ha⟩ := h
        obtain ⟨Q, hQ, hnQ⟩ := hproper G hi hd hv hs
        intro heq
        have hmem : (⟨Q, hQ⟩ : V) ∈ divisible V H.val := heq ▸ Submodule.mem_top
        exact hnQ (ha.dvd.trans (show H.val ∣ Q from hmem))
      · exact bot_proper
  obtain ⟨Q, hQ⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (K := FX) (M := V) tests ht
  refine ⟨Q.val, Q.property, ?_, ?_⟩
  · intro hz
    exact hQ none ((Submodule.mem_bot FX).mpr (Subtype.ext hz))
  · intro G hi hd hv hs hdiv
    obtain ⟨H, hH, ha⟩ := exists_mem_factors_of_dvd hP hi hd
    let k : I := ⟨H, hH⟩
    apply hQ (some k)
    change Q ∈ (if _ then divisible V H else ⊥)
    rw [ite_eq_left ⟨G, hi, hd, hv, hs, ha⟩]
    exact ha.symm.dvd.trans hdiv
end
end K1_14_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_3
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
abbrev JetPlane := Polynomial (Polynomial FX)
abbrev Surface := PrimeSpectrum Jet
def fixedEmbedding : JetPlane →+* Jet :=
  Polynomial.mapRingHom (Polynomial.mapRingHom MvPolynomial.C)
def fixedAt (G : JetPlane) (S : (Polynomial K)) : FX :=
  G.eval₂ (evalRingHom (atX S)) (atX S.derivative)
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
def JetCaps {R : Type*} [Semiring R] (G : Polynomial (Polynomial R)) (b j : ℕ) : Prop :=
  ∀ v y, (G.coeff v).coeff y ≠ 0 → y + v ≤ b ∧ v ≤ j
def RowCaps (G : Jet) (s : Shape) : Prop :=
  ∀ v y, (G.coeff v).coeff y ≠ 0 →
    y + v ≤ s.B ∧ v ≤ s.J ∧ ((G.coeff v).coeff y).totalDegree ≤ s.U
def cheapShape (i : Fin 4) : Shape :=
  ![⟨45,63,14,812⟩, ⟨57,80,18,1041⟩, ⟨81,114,26,1383⟩, ⟨123,173,40,2173⟩] i
def layeredShape (i : Fin 4) : Shape :=
  ![⟨84,118,24,2907⟩, ⟨114,160,33,3775⟩, ⟨144,203,42,5064⟩, ⟨231,325,67,8061⟩] i
def reserve (i : Fin 4) : ℕ := ![0,2,5,12] i
def fullShape : Shape := ⟨358,500,105,66251⟩
def reserveCutoff (h : ℕ) (s : Shape) (i : Fin 4) : ℕ :=
  s.m * 180265 - 1 - 2*h*reserve i
def contactPower (h : ℕ) (s : Shape) (W : ℕ) : ℕ :=
  1 + (s.m * 180265 - 1 - W) / (2*h)
def SeedShift (h : ℕ) (rows : Banks) (s : Shape) : Prop :=
  ∀ W, ∀ P ∈ rows s W, ∀ i r, seedHasse i r P ∈ rows s (W + 2*h*r)
def LeadingFilter (h : ℕ) (rows : Banks) (s : Shape) : Prop :=
  ∀ W, ∀ P ∈ rows s W, P ≠ 0 →
    (P.leadingCoeff.natDegree + P.natDegree) * (131071-h) ≤ W + P.natDegree
def NoMovingCommon (P Q : Jet) : Prop :=
  ∀ D : Jet, Irreducible D → D ∣ P → D ∣ Q → 0 < D.natDegree →
    D ∈ Set.range fixedEmbedding
structure BufferedPair (h : ℕ) (rows : Banks) (i : Fin 4) where
  cheap : Jet
  layered : Jet
  cheap_ne : cheap ≠ 0
  layered_ne : layered ≠ 0
  cheap_mem : cheap ∈ rows (cheapShape i) (reserveCutoff h (cheapShape i) i)
  layered_mem : layered ∈ rows (layeredShape i) (reserveCutoff h (layeredShape i) i)
  cheap_caps : RowCaps cheap (cheapShape i)
  layered_caps : RowCaps layered (layeredShape i)
  no_moving : NoMovingCommon cheap layered
abbrev SeedField := FractionRing Seeds
abbrev SeedClosure := AlgebraicClosure SeedField
abbrev JetField := FractionRing JetPlane
abbrev JetClosure := AlgebraicClosure JetField
abbrev FibreJet := Polynomial (Polynomial SeedClosure)
def seedGeneric : Seeds →+* SeedClosure :=
  (algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField)
def jetGeneric : JetPlane →+* JetClosure :=
  let first : JetPlane →+* JetField := algebraMap JetPlane JetField
  let second : JetField →+* JetClosure := algebraMap JetField JetClosure
  second.comp first
def seedFibreEval (y v : SeedClosure) : Jet →+* SeedClosure :=
  eval₂RingHom (eval₂RingHom seedGeneric y) v
def OnSeedFibre (q : Surface) (y v : SeedClosure) : Prop :=
  RingHom.ker (seedFibreEval y v) = q.asIdeal
structure Parent (q : Surface) : Prop where
  height_two : q.asIdeal.height = 2
  seed_side : ∃ y v, OnSeedFibre q y v ∧ IsSeparable SeedField y ∧ IsSeparable SeedField v
  jet_side : ∃ g : Jet →+* JetClosure,
    g.comp fixedEmbedding = jetGeneric ∧ RingHom.ker g = q.asIdeal ∧
      ∀ i : Fin 2, IsSeparable JetField (g (C (C (MvPolynomial.X i))))
def fibreRow (P : Jet) : FibreJet := P.map (Polynomial.mapRingHom seedGeneric)
def fibrePoint (y v : SeedClosure) : Ideal FibreJet :=
  Ideal.span {C (R := Polynomial SeedClosure) (Polynomial.X (R := SeedClosure) - C y),
    Polynomial.X (R := Polynomial SeedClosure) - C (C v)}
def OrderAt (q : Surface) (P : Jet) (m : ℕ) : Prop :=
  ∀ y v, OnSeedFibre q y v → fibreRow P ∈ fibrePoint y v ^ m
abbrev ClearedSeeds := MvPolynomial (Fin 2) (Polynomial L)
abbrev ClearedEquation := Polynomial ClearedSeeds
def liftEquation : ClearedEquation →+* Equation :=
  Polynomial.mapRingHom (MvPolynomial.map (algebraMap (Polynomial L) FX))
def clearedDx (g : ClearedEquation) : ClearedEquation :=
  g.sum fun j a => monomial j (∑ e ∈ MvPolynomial.support a, MvPolynomial.monomial e (AddMonoidAlgebra.coeff a e).derivative)
def ordinaryCutter (g : ClearedEquation) : Jet :=
  C (liftEquation (clearedDx g)) + X * C (liftEquation g.derivative)
def IsClearing (f : Equation) (g : ClearedEquation) (a : (Polynomial L)) : Prop :=
  a ≠ 0 ∧ liftEquation g = C (MvPolynomial.C (algebraMap (Polynomial L) FX a)) * f
def Compatible (P Q : Jet) (q : Surface) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    C f ∈ q.asIdeal → ∀ g a, IsClearing f g a → ordinaryCutter g ∈ q.asIdeal
inductive Slice where
  | seed | ordinate | mixed | jets
abbrev SectionField := FractionRing (MvPolynomial (Fin 4) FX)
abbrev SectionSeeds := MvPolynomial (Fin 2) SectionField
abbrev SectionJet := Polynomial (Polynomial SectionSeeds)
def sectionMap : Jet →+* SectionJet :=
  Polynomial.mapRingHom (Polynomial.mapRingHom
    (MvPolynomial.map (algebraMap FX SectionField)))
def sectionScalar (i : Fin 4) : SectionJet :=
  C (C (MvPolynomial.C (algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i))))
def sectionEquations (slice : Slice) : Set SectionJet :=
  let t₀ : SectionJet := C (C (MvPolynomial.X 0))
  let t₁ : SectionJet := C (C (MvPolynomial.X 1))
  let y : SectionJet := C (R := Polynomial SectionSeeds) (Polynomial.X (R := SectionSeeds))
  let v : SectionJet := Polynomial.X (R := Polynomial SectionSeeds)
  let seedLine := t₀ + sectionScalar 0 * t₁
  let jetLine := y + sectionScalar 1 * v
  let a := sectionScalar 2
  let b := sectionScalar 3
  match slice with
  | .seed => {t₀ - a, t₁ - b}
  | .ordinate => {seedLine - a, y - b}
  | .mixed => {seedLine - a, jetLine - b}
  | .jets => {y - a, v - b}
def sectionDegree (q : Surface) (slice : Slice) : ℕ :=
  let J := q.asIdeal.map sectionMap ⊔ Ideal.span (sectionEquations slice)
  Module.finrank SectionField (SectionJet ⧸ J)
def mass (qs : Finset Surface) (s : Slice) : ℚ :=
  ∑ q ∈ qs, (sectionDegree q s : ℚ)
structure MassCap (qs : Finset Surface) (a c z : ℚ) : Prop where
  seed : mass qs .seed ≤ a
  ordinate : mass qs .ordinate ≤ c
  mixed : mass qs .mixed ≤ z
structure SeedCover where
  curve : Seeds
  curve_ne : curve ≠ 0
  points : Finset (FX × FX)
def SeedCover.Covers (C : SeedCover) (z : K) : Prop :=
  graphEval z C.curve = 0 ∨ (seedEmbedding z, seedEmbedding z ^ p) ∈ C.points
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) where
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  masses : MassCap parents 2891 60998 381269
  jetMass : mass parents .jets ≤ 3019828
  seeds : SeedCover
  seedDegree : seeds.curve.totalDegree ≤ 381269 + 812 + 2907
  seedPoints : seeds.points.card ≤ 3019828
  ordinates : Finset FX
  ordinateCount : ordinates.card ≤ 2891
  lowJet : JetPlane
  fixedCheap : JetPlane
  fixedLayered : JetPlane
  lowJet_ne : lowJet ≠ 0
  fixedCheap_ne : fixedCheap ≠ 0
  fixedLayered_ne : fixedLayered ≠ 0
  lowJet_caps : JetCaps lowJet 381269 60998
  fixedCheap_caps : JetCaps fixedCheap 63 14
  fixedLayered_caps : JetCaps fixedLayered 118 24
  cover : ∀ γ ∈ Γ,
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ ordinates ∨
    fixedAt lowJet (F.scalar γ) = 0 ∨ fixedAt fixedCheap (F.scalar γ) = 0 ∨
    fixedAt fixedLayered (F.scalar γ) = 0 ∨ ∃ q ∈ parents, MarkOn M F q γ
structure ProjectedProduct (qs : Finset Surface) (f : Equation) : Prop where
  positive : 0 < f.natDegree
  primitive : f.IsPrimitive
  separable : (f.map (algebraMap Seeds SeedField)).Separable
  vanishes : ∀ q ∈ qs, C f ∈ q.asIdeal
  divides_leading : ∀ (P : Jet) (k : ℕ), P ≠ 0 →
    (∀ q ∈ qs, OrderAt q P k) → f ^ (k - P.natDegree) ∣ P.leadingCoeff
end
end K1_14_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
open scoped Classical
def stageAt (i : Fin 10) : Stage :=
  stages.get ⟨i.val, by simp [stages]⟩
def RowCaps (P : Jet) (s : Shape) : Prop :=
  ∀ j i, (P.coeff j).coeff i ≠ 0 →
    i+j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U
def ODECaps (G : ODE) (B J : ℕ) : Prop :=
  G ≠ 0 ∧ G.natDegree ≤ J ∧ ∀ j i, (G.coeff j).coeff i ≠ 0 → i+j ≤ B
structure RowPair (w : ℤ) (rows : Banks) (i : Fin 10) where
  cheap : Jet
  layered : Jet
  cheap_ne : cheap ≠ 0
  layered_ne : layered ≠ 0
  cheap_mem : cheap ∈ rows (stageAt i).cheap (bufferedAt w (stageAt i).reserve (stageAt i).cheap)
  layered_mem : layered ∈ rows (stageAt i).layered (bufferedAt w (stageAt i).reserve (stageAt i).layered)
  cheap_caps : RowCaps cheap (stageAt i).cheap
  layered_caps : RowCaps layered (stageAt i).layered
  no_moving : ∀ G : Jet, Irreducible G → G ∣ cheap → 0 < G.natDegree →
    UsesSeed G → ¬ G ∣ layered
def fixedIncl : ODE →+* Jet := K1_14_3.fixedEmbedding
structure FixedPart (P : Jet) (s : Shape) where
  equation : ODE
  equation_caps : ODECaps equation s.B s.J
  residual : Jet
  factorization : P = fixedIncl equation * residual
  stripped : ∀ G : ODE, Irreducible (fixedIncl G) → ¬ fixedIncl G ∣ residual
structure FixedPair {w rows i} (B : RowPair w rows i) where
  cheap : FixedPart B.cheap (stageAt i).cheap
  layered : FixedPart B.layered (stageAt i).layered
def compatible (P Q : Jet) (I : Ideal Ambient) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    rootIncl (toRoot f) ∈ I →
    ∀ g a, K1_14_3.IsClearing f g a → toJet (K1_14_3.ordinaryCutter g) ∈ I
def fixedOn (G : ODE) (I : Ideal Ambient) : Prop :=
  toJet (fixedIncl G) ∈ I
abbrev SectionField := FractionRing (MvPolynomial (Fin 4) FX)
abbrev SectionAmbient := MvPolynomial (Fin 4) SectionField
def sliceParameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def sectionBase : Ambient →+* SectionAmbient := MvPolynomial.map (algebraMap FX SectionField)
def sectionSeedLine : SectionAmbient :=
  MvPolynomial.X 0 + MvPolynomial.C (sliceParameter 0) * MvPolynomial.X 1 -
    MvPolynomial.C (sliceParameter 2)
def sectionJetLine : SectionAmbient :=
  MvPolynomial.X 2 + MvPolynomial.C (sliceParameter 1) * MvPolynomial.X 3 -
    MvPolynomial.C (sliceParameter 3)
abbrev OverOrdinate (I : Ideal Ambient) :=
  CoordinateRing (I.map sectionBase ⊔ Ideal.span {sectionSeedLine, (MvPolynomial.X 2 -
    MvPolynomial.C (sliceParameter 3))})
abbrev OverMixed (I : Ideal Ambient) :=
  CoordinateRing (I.map sectionBase ⊔ Ideal.span {sectionSeedLine, sectionJetLine})
def ordinateIncl : Polynomial FX →+* Ambient :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X 2)
def jetPlaneIncl : ODE →+* Ambient := toJet.comp fixedIncl
structure Active (I : Ideal Ambient) : Prop where
  prime : I.IsPrime
  dimension : ringKrullDim (CoordinateRing I) = 2
  seed_finite : Module.Finite SeedField (OverSeeds I)
  ordinate_finite : Module.Finite SectionField (OverOrdinate I)
  mixed_finite : Module.Finite SectionField (OverMixed I)
  jet_finite : Module.Finite SeedField (OverJets I)
  seed_size : 0 < Module.finrank SeedField (OverSeeds I) ∧
    Module.finrank SeedField (OverSeeds I) < p
  mixed_lt : Module.finrank SectionField (OverMixed I) < p
  jet_lt : Module.finrank SeedField (OverJets I) < p
  ordinate_dominant : Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)
def dual (I : Ideal Ambient) : Prop := 0 < Module.finrank SeedField (OverJets I)
def sectionDegree (I : Ideal Ambient) : Fin 4 → ℕ :=
  ![Module.finrank SeedField (OverSeeds I), Module.finrank SectionField (OverOrdinate I),
    Module.finrank SectionField (OverMixed I), Module.finrank SeedField (OverJets I)]
def mass (S : Finset (Ideal Ambient)) (k : Fin 4) : ℕ :=
  ∑ I ∈ S, sectionDegree I k
def Fits (S : Finset (Ideal Ambient)) (cap : Fin 4 → ℕ) : Prop :=
  ∀ k, mass S k ≤ cap k
def orderOn (I : Ideal Ambient) (P : Jet) (m : ℕ) : Prop :=
  let imageIdeal := if dual I then ⊥ else (I.comap jetPlaneIncl).map jetPlaneIncl
  ∃ a : Ambient, a ∉ I ∧ a * toJet P ∈ I^m ⊔ imageIdeal
def budget (n : ℕ) : Fin 4 → ℕ :=
  match n with
  | 0 => ![5980,227898,1052972,16029459]
  | 1 => ![3767,143910,648356,4855764]
  | 2 => ![3019,114928,521837,4855764]
  | 3 => ![2687,101858,521837,3052656]
  | 4 => ![422,15662,158698,1993744]
  | 5 => ![280,10171,103959,1285200]
  | 6 => ![225,8016,68569,995828]
  | 7 => ![170,6245,54168,776610]
  | 8 => ![145,5264,47174,606347]
  | _ => ![123,4633,40170,512888]
def weight (s : Shape) (fee : Fin 3) : Fin 4 → ℕ :=
  ![![s.U, s.B-s.J, s.J, 0],
    ![0, s.U, 0, s.J],
    ![0,0, s.U, s.B]] fee
def dot (weight values : Fin 4 → ℕ) : ℕ := ∑ k, weight k * values k
def initialPrice : ℕ := 5980 + ((p+1)*1052972+19635660) + (p+1)*(1899+8441)
def OnParent {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop :=
  OnJet I (M.label γ) (F.scalar γ)
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (cheapFixed layeredFixed : ODE) where
  parents : Finset (Ideal Ambient)
  geometric : ∀ I ∈ parents, Active I
  initial_mass : Fits parents (budget 0)
  direct : Finset K
  direct_card : direct.card ≤ initialPrice
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ fixedAt cheapFixed (F.scalar γ) = 0 ∨
    fixedAt layeredFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent M F I γ
def CurveGeometry (I : Ideal Ambient) : Prop :=
  I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 1 ∧
    Module.Finite SeedField (JetSeedSection I) ∧
    0 < Module.finrank SeedField (JetSeedSection I) ∧
    Module.Finite SeedField (JetYSection I)
structure CutCover where
  direct : Finset K
  curves : Finset (Ideal Ambient)
  geometric : ∀ I ∈ curves, CurveGeometry I
def curveSeedMass (C : Finset (Ideal Ambient)) : ℕ :=
  ∑ I ∈ C, Module.finrank SeedField (JetSeedSection I)
def curveYMass (C : Finset (Ideal Ambient)) : ℕ :=
  ∑ I ∈ C, Module.finrank SeedField (JetYSection I)
def CutCover.cost (C : CutCover) (fee : Fin 3) : ℕ :=
  ![curveSeedMass C.curves, curveYMass C.curves, C.direct.card] fee
end
end K1_14_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_2_2
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
open scoped Classical
theorem eval_fixed (z : K) (S : (Polynomial K)) (G : ODE) :
    jetMarkHom z S (toJet (fixedIncl G)) = fixedAt G S := by
  rw [eval_toJet]
  change (G.map (Polynomial.mapRingHom MvPolynomial.C)).eval₂
      (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative) =
    G.eval₂ (evalRingHom (atX S)) (atX S.derivative)
  rw [eval₂_map]
  have h : (eval₂RingHom (graphEval z) (atX S)).comp (Polynomial.mapRingHom MvPolynomial.C) =
      evalRingHom (atX S) := by
    apply RingHom.ext
    intro f
    change (f.map MvPolynomial.C).eval₂ (graphEval z) (atX S) = f.eval (atX S)
    rw [eval₂_map, ← eval₂_id]
    have hc : (graphEval z).comp MvPolynomial.C = RingHom.id FX := by
      ext c
      simp [graphEval]
    rw [hc]
  rw [h]
theorem mass_mono {S T : Finset (Ideal Ambient)} (h : S ⊆ T) (k : Fin 4) :
    mass S k ≤ mass T k :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)
theorem sum_union_le {α : Type*} (f : α → ℕ) (A B : Finset α) :
    (∑ a ∈ A ∪ B, f a) ≤ (∑ a ∈ A, f a) + ∑ a ∈ B, f a := by
  have h := Finset.sum_union_inter (f := f) (s₁ := A) (s₂ := B)
  omega
theorem sum_biUnion_le {α β : Type*} (A : Finset α) (B : α → Finset β) (f : β → ℕ) :
    (∑ x ∈ A.biUnion B, f x) ≤ ∑ i ∈ A, ∑ x ∈ B i, f x := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (sum_union_le f _ _).trans (Nat.add_le_add_left ih _)
def joinCuts {α : Type*} (A : Finset α) (B : α → CutCover) : CutCover where
  direct := A.biUnion (fun i => (B i).direct)
  curves := A.biUnion (fun i => (B i).curves)
  geometric := fun I hI => by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hI
    exact (B i).geometric I hi
theorem joinCuts_cost {α : Type*} (A : Finset α) (B : α → CutCover) (fee : Fin 3) :
    (joinCuts A B).cost fee ≤ ∑ i ∈ A, (B i).cost fee := by
  fin_cases fee
  · exact sum_biUnion_le _ _ _
  · exact sum_biUnion_le _ _ _
  · exact Finset.card_biUnion_le
theorem sum_dot (A : Finset (Ideal Ambient)) (w : Fin 4 → ℕ) :
    (∑ I ∈ A, dot w (sectionDegree I)) = dot w (mass A) := by
  simp only [dot, mass, Finset.mul_sum]
  exact Finset.sum_comm
def emptyCut : CutCover :=
  ⟨∅, ∅, by simp⟩
theorem fits_mono {S T : Finset (Ideal Ambient)} {cap : Fin 4 → ℕ} (hs : S ⊆ T)
    (ht : Fits T cap) : Fits S cap :=
  fun k => (mass_mono hs k).trans (ht k)
end
end K1_14_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
def ordinarySeedDegree (f : Equation) : ℕ :=
  f.support.sup fun y => (f.coeff y).totalDegree
structure ProperPair (P Q : Jet) : Prop where
  left_ne : P ≠ 0
  right_ne : Q ≠ 0
  no_common : ∀ D : Jet, Irreducible D → D ∣ P → ¬ D ∣ Q
def markEval (z : K) (S : (Polynomial K)) : Jet →+* FX :=
  eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
def AtSurface (q : Surface) (z : K) (S : (Polynomial K)) : Prop :=
  q.asIdeal ≤ RingHom.ker (markEval z S)
structure PreparedPair (P Q : Jet) where
  seedContent : Seeds
  fixedCheap : JetPlane
  fixedLayered : JetPlane
  cheap : Jet
  layered : Jet
  ordinary : Finset Equation
  seedContent_ne : seedContent ≠ 0
  seedContent_degree : seedContent.totalDegree ≤ 812 + 2907
  fixedCheap_ne : fixedCheap ≠ 0
  fixedLayered_ne : fixedLayered ≠ 0
  fixedCheap_caps : JetCaps fixedCheap 63 14
  fixedLayered_caps : JetCaps fixedLayered 118 24
  cheap_caps : RowCaps cheap (cheapShape 0)
  layered_caps : RowCaps layered (layeredShape 0)
  proper : ProperPair cheap layered
  ordinary_factors : ∀ f ∈ ordinary, Irreducible f ∧ 0 < f.natDegree
  ordinary_seed : ∑ f ∈ ordinary, ordinarySeedDegree f ≤ 812
  ordinary_y : ∑ f ∈ ordinary, f.natDegree ≤ 63
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    graphEval z seedContent = 0 ∨ fixedAt fixedCheap S = 0 ∨ fixedAt fixedLayered S = 0 ∨
      (jetAt cheap z S = 0 ∧ jetAt layered z S = 0) ∨
      ∃ f ∈ ordinary, atMark f z S = 0
end
end K1_14_3_2
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators Classical
theorem seed_count {T : Finset K} {label : K → K} (hinj : Set.InjOn label (T : Set K))
    (C : SeedCover) (hdeg : C.curve.totalDegree < p)
    (hcover : ∀ γ ∈ T, C.Covers (label γ)) :
    T.card ≤ (p+1)*C.curve.totalDegree + C.points.card := by
  classical
  let zero := T.filter (fun γ => graphEval (label γ) C.curve = 0)
  let other := T.filter (fun γ => graphEval (label γ) C.curve ≠ 0)
  have inj : Set.InjOn (fun γ => seedEmbedding (label γ)) (T : Set K) :=
    fun _ ha _ hb h => hinj ha hb (seedEmbedding.injective h)
  have hzero : zero.card ≤ (p+1)*C.curve.totalDegree := by
    have hcard : (zero.image (fun γ => seedEmbedding (label γ))).card = zero.card :=
      Finset.card_image_iff.mpr (inj.mono (by exact Finset.filter_subset _ _))
    have hb := frobenius_coefficient_exception_count p
      C.curve.totalDegree C.curve.totalDegree (by decide) C.curve C.curve_ne
      (C.curve.degreeOf_le_totalDegree 0) hdeg (C.curve.degreeOf_le_totalDegree 1)
      (zero.image (fun γ => seedEmbedding (label γ))) (by
        intro x hx
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hγ).2)
    simpa only [hcard, Nat.add_mul, Nat.one_mul, Nat.add_comm (C.curve.totalDegree)] using hb
  have hother : other.card ≤ C.points.card := by
    apply Finset.card_le_card_of_injOn
      (fun γ => (seedEmbedding (label γ), seedEmbedding (label γ)^p))
    · intro γ hγ
      have hm := Finset.mem_filter.mp (show γ ∈ other from hγ)
      exact (hcover γ hm.1).resolve_left hm.2
    · intro x hx y hy h
      exact inj (Finset.mem_filter.mp (show x ∈ other from hx)).1
        (Finset.mem_filter.mp (show y ∈ other from hy)).1 (congrArg Prod.fst h)
  rw [← Finset.card_filter_add_card_filter_not (s := T)
    (p := fun γ => graphEval (label γ) C.curve = 0)]
  exact Nat.add_le_add hzero hother
theorem scalar_atX_injective : Function.Injective atX :=
  (IsFractionRing.injective (Polynomial L) FX).comp
    (Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective)
theorem label_injective {u del} (M : AnchorModel u del) : Function.Injective M.label :=
  fun _ _ h => sub_left_inj.mp h
def joinCovers {ι : Type*} (I : Finset ι) (C : ι → SeedCover) : SeedCover := by
  classical
  exact ⟨∏ i ∈ I, (C i).curve,
    Finset.prod_ne_zero_iff.mpr (fun i _ => (C i).curve_ne),
    I.biUnion (fun i => (C i).points)⟩
theorem joinCovers_degree {ι : Type*} (I : Finset ι) (C : ι → SeedCover) :
    (joinCovers I C).curve.totalDegree ≤ ∑ i ∈ I, (C i).curve.totalDegree :=
  MvPolynomial.totalDegree_finsetProd I _
theorem joinCovers_points {ι : Type*} (I : Finset ι) (C : ι → SeedCover) :
    (joinCovers I C).points.card ≤ ∑ i ∈ I, (C i).points.card :=
  Finset.card_biUnion_le
theorem joinCovers_covers {ι : Type*} {I : Finset ι} {C : ι → SeedCover} {i : ι}
    (hi : i ∈ I) {z : K} (hz : (C i).Covers z) :
    (joinCovers I C).Covers z := by
  classical
  rcases hz with h | h
  · left
    change graphEval z (∏ j ∈ I, (C j).curve) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero hi h
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
end
end K1_14_3
end

end Merged_Fast029

end Merged6967_Fast029
