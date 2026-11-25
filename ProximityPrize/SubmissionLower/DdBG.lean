import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.TrivSqZeroExt.Ideal
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
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
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
