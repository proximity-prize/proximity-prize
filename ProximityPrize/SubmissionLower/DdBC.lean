import ArkLib.Data.MvPolynomial.WeightedOrder
import ArkLib.Data.Polynomial.SpecializationAvoidance
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Field
import ArkLib.ToMathlib.RingTheory.MvPolynomial.StandardMonomials
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.RingTheory.Polynomial.UniqueFactorization
set_option Elab.async false
set_option maxHeartbeats 3000000
open _root_ renaming AddCommGroup→Bf,AdjoinRoot→qJ,Algebra→n5,Algebra.FiniteType→xu,Algebra.FormallySmooth→FK,Algebra.IsAlgebraic→JW,Algebra.IsPushout→X8,Algebra.TensorProduct.includeRight→Wl,Algebra.TensorProduct.rightAlgebra→Np,Algebra.algebraMap→aU,Algebra.algebraMapSubmonoid→HZ,Algebra.linearMap→ IU,Algebra.lmul→ Iw,Algebra.smul_def→vi,Algebra.trdeg→J4,Cardinal.toNat_add→NY,Classical.propDecidable→KI,CommRing→lz,DecidableEq→ ox,ExpChar→t3,FaithfulSMul→Kl,Field→cy,Fin.prod_univ_succ→Qx,Fin.sum_univ_eq_sum_range→Vl,Fin.sum_univ_succ→Pc,Finite.of_injective→Un,FiniteDimensional→RJ,Finset→nI,Finset.card_filter_add_card_filter_not→WW,Finset.card_image_of_injective→Vq,Finset.card_univ→zk,Finset.mem_filter→Ee,Finset.mem_univ→u5,Finset.mul_sum→sI,Finset.sum_add_distrib→VO,Finset.sum_apply→yQ,Finset.sum_comm→zS,Finset.sum_congr→pC,Finset.sum_const→GR,Finset.sum_const_zero→SW,Finset.sum_eq_single_of_mem→Xp,Finset.sum_eq_zero→S2,Finset.sum_le_sum→G9,Finset.sum_mul→yL,Finset.univ→vj,Finsupp.prod_fintype→Nr,Finsupp.sum_fintype→N0,Finsupp.weight_apply→Pj
open _root_ renaming Fintype→lJ,Fintype.card→lV,Fintype.card_fin→t8,Fintype.equivFinOfCardEq→G2,FractionRing→G4,Function.Injective→mD,Function.Surjective→yU,Ideal→nX,Ideal.Quotient.eq_zero_iff_mem→Ml,Ideal.Quotient.mk→p7,Ideal.Quotient.mk_surjective→uh,Ideal.annihilator_quotient→XJ,Ideal.map_pow→ II,Ideal.mem_map_of_mem→NX,Ideal.mem_sup_left→PD,Ideal.mem_sup_right→XB,Ideal.mul_mem_mul→VS,Ideal.ofList→wY,Ideal.ofList_cons→Mw,Ideal.pow_le_pow_right→Fa,Ideal.pow_mem_pow→MK,Ideal.radical_mono→Ww,Ideal.smul_top_eq_map→UY,Ideal.span→nq,Ideal.span_singleton_eq_bot→Wm,Ideal.span_singleton_le_iff_mem→Gj,Ideal.subset_span→Dw,Infinite→Cy,IntermediateField.adjoin→Ye,IntermediateField.subset_adjoin→WX,IsAlgebraic→p6,IsAssociatedPrime→G5,IsDomain→t5,IsFractionRing.injective→Gn,IsIntegral→v9,IsIntegral.of_pow→Te,IsLocalRing→t4,IsLocalRing.CotangentSpace→x7,IsLocalRing.ResidueField→pG,IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal→Xu,IsLocalRing.maximalIdeal→lI,IsLocalRing.residue_eq_zero_iff→JQ,IsLocalRing.residue_surjective→C4,IsNoetherianRing→zm,IsReduced→Et,IsSMulRegular→FQ
open _root_ renaming IsScalarTower→vl,IsScalarTower.algebraMap_apply→Pr,IsScalarTower.algebraMap_smul→KH,IsScalarTower.of_algHom→PA,Lagrange.coeff_eq_sum→Pk,Lagrange.degree_interpolate_lt→SM,Lagrange.eval_interpolate_at_node→Up,Lagrange.interpolate→Re,LinearIndepOn→ Il,LinearIndependent→vw,LinearMap.finrank_le_finrank_of_injective→UZ,LinearMap.finrank_range_add_finrank_ker→t6,LinearMap.id→LO,LinearMap.ker→ oK,LinearMap.range→ In,List.mem_cons_of_mem→Kz,List.perm_append_comm→Yc,Localization.AtPrime→yB,Localization.Away→SL,Matrix→c9,Matrix.cramer_apply→yJ,Matrix.det_transpose→JK,Matrix.map_apply→Du,Matrix.map_updateCol→Qw,Matrix.mulVec→th,Matrix.mulVec_cramer→WK,Matrix.mulVec_mulVec→UP,Matrix.mulVec_single_one→WY,Matrix.mulVec_smul→Lf,Matrix.mulVec_sub→LQ,Matrix.rank_eq_finrank_span_cols→Mj,Matrix.rank_eq_finrank_span_row→Gi,Matrix.row→EP,Matrix.submatrix_apply→NI,Matrix.updateCol_ne→Rm,Matrix.updateCol_self→Vz,Module.Basis→ze,Module.Finite→pz,Module.Flat→z9,Module.annihilator→qz,Module.finrank→ oz,Module.finrank_fintype_fun_eq_card→zd,Module.finrank_pi_fintype→Mk,Module.length→t7,Module.length_eq_of_surjective→Ob,Module.length_le_of_surjective→SU,Module.length_quotient→Sv,Module.rank→GF
open _root_ renaming Module.rank_lt_aleph0→wR,ModuleCat.of→z8,MvPolynomial→ ov,MvPolynomial.X→zh,MvPolynomial.affineHilbertFunction→qM,MvPolynomial.affineHilbertPolynomial→uW,MvPolynomial.eval→p9,MvPolynomial.eval₂Hom→zR,MvPolynomial.eventually_eval_affineHilbertPolynomial→TH,MvPolynomial.le_degreeOf_of_mem_support→u8,MvPolynomial.natDegree_aeval_le_weightedTotalDegree→Vs,MvPolynomial.quotientDegreeLE→qm,MvPolynomial.ringHom_ext→xL,Nat.add_le_add_right→WD,Nat.add_mul_mod_self_left→XG,Nat.cast_add→zg,Nat.eq_of_mul_eq_mul_left→MS,Nat.exists_eq_succ_of_ne_zero→Yi,Nat.mod_eq_of_lt→F9,Option→vH,Order.coheight→FU,Pi.single→v8,Pi.single_apply→G6,Pi.single_eq_same→Pv,Pi.smul_apply→qx,Pi.sub_apply→LP,Pi.zero_apply→u9,Polynomial.C→uJ,Polynomial.C_mul_X_pow_eq_monomial→Kv,Polynomial.X→qU,Polynomial.aeval→Dz,Polynomial.card_le_degree_of_subset_roots→Fz,Polynomial.coe_evalRingHom→Ok,Polynomial.coeff_monomial→R9,Polynomial.coeff_zero→QL,Polynomial.derivative→uz,Polynomial.evalRingHom→ oq,Polynomial.eval_eq_sum_range'→S1,Polynomial.eval_mul→vh,Polynomial.finsetSum_coeff→TZ,Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity→Yo,Polynomial.map_map→Xg,Polynomial.map_mul→Qy,Polynomial.map_prod→VH,Polynomial.mem_roots→xW,Polynomial.monomial→yo,Polynomial.natDegree_C_mul_le→Sd,Polynomial.natDegree_le_of_eventually_eval_natCast_le→LR
open _root_ renaming Polynomial.natDegree_lt_iff_degree_lt→Mz,Polynomial.natDegree_mul→G3,Polynomial.natDegree_mul_le→FR,Polynomial.natDegree_sum_le_of_forall_le→Ea,RingHom.comp_apply→RP,RingHom.congr_fun→P7,RingHom.ker→qG,RingHom.ker_eq_comap_bot→RD,RingHom.mapMatrix_apply→yl,RingHom.mem_ker→FV,RingHomInvPair.of_ringEquiv→Ts,Set.InjOn→Gk,Set.Subsingleton.finite→NZ,Set.mem_range_self→EK,Set.range→ oZ,Set.subset_univ→Df,Submodule→pL,Submodule.eq_of_le_of_finrank_eq→Xo,Submodule.factor→MO,Submodule.factor_surjective→SD,Submodule.mem_span_range_iff_exists_fun→NW,Submodule.span→pU,Submodule.subset_span→Dv,Submodule.sum_mem→Kp,Subsingleton→Ef,Subtype.ext→vk,Subtype.val→Av,WithBot→vZ,add_sub_cancel_right→ IT,add_zero→wB,associatedPrimes→xm,associatedPrimes.finite→Xx,biUnion_associatedPrimes_eq_compl_regular→OJ,congrArg→ oj,congrFun→ oy,div_eq_mul_inv→KA,dotProduct→sS,exists_linearIndependent'→Pf,faithfulSMul_iff_algebraMap_injective→Hw,finrank_span_eq_card→G1,finrank_span_singleton→TI,frobenius→zE,frobenius_def→Gr,inferInstance→xI,injective_iff_map_eq_zero→PM,integralClosure→wA
open _root_ renaming inv_mul_cancel₀→G8,isAlgebraic_algebraMap→SC,isIntegral_algebraMap→C9,isReduced_of_injective→Kh,iterateFrobenius→t9,iterateFrobenius_def→Oc,iterateFrobenius_inj→RC,le_antisymm→z7,le_sup_left→G7,le_sup_right→X4,liftOfDerivationToSquareZero_apply→Nj,map_add→Aa,map_mul→ oD,map_sub→sH,map_sum→ oY,map_zero→p5,mul_assoc→Ar,mul_comm→qy,mul_left_cancel₀→Au,mul_ne_zero→zi,nonZeroDivisors→JM,pow_add→vG,pow_ne_zero→Kc,ringKrullDim→y5,smul_eq_mul→pQ,sub_eq_zero→G0,sub_self→zc,trdeg_add_eq→zf,trdeg_eq_zero→GY,true_and→Eg
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace baC
noncomputable section
open scoped nonZeroDivisors
variable {F A:Type} [cy F] [lz A] [t5 A] [n5 F A]
local notation "K" => FractionRing A
local notation "B" => integralClosure A (FractionRing A)
end
end baC
end
section
namespace bjD
open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise
universe u v
section Local
variable {k :Type v} [cy k] [Cy k]
variable {R:Type u} [lz R] [zm R] [t4 R] [n5 k R]
end Local
end bjD
end
section
namespace gR
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
def mL (x :ι→F) (S:nI ι) :(Polynomial F) :=
 ∏ i∈S,(X - C (x i))
theorem S8 (x :ι→F) (S:nI ι) : (mL x S).Monic :=
 Polynomial.monic_prod_of_monic S _ (fun _ _=>monic_X_sub_C _)
theorem ZQ (x :ι→F) (S:nI ι) :
  (mL x S).natDegree=S.card:= by
 rw [mL,Polynomial.natDegree_prod_of_monic S _ (fun _ _=>monic_X_sub_C _)]
 simp
theorem arK (x :ι→F) (S:nI ι) (i:ι) (hi:i∈S) :
  (mL x S).eval (x i)=0:= by
 simp only [mL,eval_prod,eval_sub,eval_X,eval_C]
 exact Finset.prod_eq_zero hi (zc _)
variable (p:ℕ) [t3 F p]
end
end gR
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F:Type*} [cy F]
variable {ι:Type*} [lJ ι] [ox ι]
end
end gR
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.apT
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {R c:Type*} [lz R] [lJ c] [ox c]
section Field
variable {K:Type*} [cy K]
variable {row:Type*}
end Field
section Polynomial
variable {F:Type*} [cy F]
end Polynomial
end
end gR.apT
end
section
namespace gR.aRz
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {K:Type*} [cy K]
end
end gR.aRz
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K] [lJ col] [ox col]
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.asZ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
section Ring
variable {R row col:Type*} [lz R] [lJ col] [ox col]
variable {r :ℕ}
end Ring
section Field
variable {K row col:Type*} [cy K] [lJ col] [ox col]
variable {r :ℕ}
end Field
section Polynomial
variable {F K row col:Type*} [cy F] [cy K] [lJ col] [ox col]
variable {φ:(Polynomial F) →+* K} {M:c9 row col (Polynomial F)} {r :ℕ}
end Polynomial
end
end gR.asZ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K] [lJ col] [ox col]
variable {φ:(Polynomial F) →+* K} {M:c9 row col (Polynomial F)} {r :ℕ}
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K]
 [lJ row] [lJ col] [ox col]
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K]
 [lJ row] [ox row] [lJ col] [ox col]
variable {φ:(Polynomial F) →+* K} {M:c9 row col (Polynomial F)} {r :ℕ}
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K col:Type*} [cy F] [cy K] [lJ col] [ox col]
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.M4
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F col:Type*} [cy F] [lJ col]
end
end gR.M4
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.asZ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K] [lJ col] [ox col]
variable {φ:(Polynomial F) →+* K} {M:c9 row col (Polynomial F)} {r :ℕ}
end
end gR.asZ
end
section
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace gR.Bx
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F row col:Type*} [cy F] [lJ row] [lJ col] [ox col]
abbrev lN (F:Type*) [cy F] :=G4 (Polynomial F)
end
end gR.Bx
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Bx
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
end
end gR.Bx
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.asZ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K] [lJ row]
 [lJ col] [ox col]
variable {φ:(Polynomial F) →+* K} {M:c9 row col (Polynomial F)} {r :ℕ}
end
end gR.asZ
end
section
namespace gR
noncomputable section
open Polynomial Finset
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
end
end gR
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {K:Type*} [cy K]
end
end gR.kL
end
section
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type} [cy F] [lJ ι] [ox ι]
end
end gR.Principal
end
section
namespace yP.C52
open scoped BigOperators Matrix
noncomputable section
theorem fTe
   {F R C C' : Type*} [cy F] [lJ C] [lJ C']
   (M:c9 R C F) (rep:C' → C)
   (h : ∀ c,M.col c=0 ∨ ∃ j,M.col c=M.col (rep j)) :
   M.rank≤(M.submatrix id rep).rank := by
 classical
 rw [Mj,Mj]
 have :=FiniteDimensional.span_of_finite (K:=F)
   (Set.finite_range (M.submatrix id rep).col)
 apply Submodule.finrank_mono
 apply Submodule.span_le.mpr
 rintro _ ⟨c,rfl⟩
 rcases h c with hz | ⟨j,hj⟩
 · rw [hz]
   exact Submodule.zero_mem _
 · rw [hj]
   exact Dv ⟨j,rfl⟩
end
end yP.C52
end
section
set_option maxRecDepth 10000
namespace wT
open Finset
end wT
end
section
namespace wT
noncomputable section
open Polynomial Finset
end
end wT
end
section
namespace aiH
noncomputable section
open Polynomial
end
end aiH
end
section
namespace aY4
noncomputable section
open MvPolynomial Filter
open scoped BigOperators
variable {k σ τ F E :Type} [cy k] [Finite σ] [Finite τ]
variable [cy F] [cy E] [n5 k F] [n5 k E] [n5 F E]
variable {P:nX (ov σ k)} {Q:nX (ov τ k)}
local notation "A" => MvPolynomial τ k ⧸ Q
local notation "B" => MvPolynomial σ k ⧸ P
variable [vl k F E]
end
end aY4
end
section
namespace bzE
noncomputable section
open scoped TensorProduct
variable {k E R S:Type*} [cy k] [cy E] [lz R] [lz S]
 [n5 k E] [n5 k R] [n5 k S] [n5 R S] [n5 E S]
 [vl k R S] [vl k E S] [ X8 k R E S]
 [IsPurelyInseparable k E]
end
end bzE
end
section
set_option backward.isDefEq.respectTransparency false
namespace bzV
open scoped Polynomial
open MvPolynomial
end bzV
end
section
namespace bzS
noncomputable section
open Polynomial
variable {M E :Type*} [cy M] [cy E] [n5 M E]
end
end bzS
end
section
namespace aKu
open Polynomial Algebra TensorProduct
noncomputable section
variable {A:Type*} [lz A]
end
end aKu
end
section
namespace aKx
open scoped BigOperators nonZeroDivisors
open Module
end aKx
end
section
namespace aKx
open Polynomial
open scoped Polynomial
end aKx
end
section
namespace aRV
noncomputable section
open IsLocalRing KaehlerDifferential MvPolynomial
open scoped TensorProduct
variable {k R:Type*} [cy k] [lz R] [t4 R] [n5 k R]
end
end aRV
end
section
namespace aRV
noncomputable section
open MvPolynomial IsLocalRing
open scoped BigOperators
end
end aRV
end
section
namespace cu
noncomputable section
open MvPolynomial Finset
variable {F:Type*} [cy F]
end
end cu
end
section
namespace BN
noncomputable section
open MvPolynomial Finset
variable {F:Type*} [cy F]
end
end BN
end
section
namespace aFY
noncomputable section
open IsLocalRing
end
end aFY
end
