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
