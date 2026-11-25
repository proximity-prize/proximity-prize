import ProximityPrize.SubmissionLower.DdZgdIx1d
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
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open _root_ renaming AddCommGroup→vj,AddMonoidAlgebra.single→t9,AddMonoidAlgebra.single_mul_single→Av,AlgEquiv.apply_symm_apply→qy,AlgHom.coe_ringHom_injective→G7,AlgHom.commutes→yo,AlgHom.id→wB,Algebra→c9,Algebra.IsAlgebraic→GB,Algebra.TensorProduct.cancelBaseChange→GR,Algebra.TensorProduct.comm→yJ,Algebra.TensorProduct.comm_tmul→G5,Algebra.TensorProduct.includeRight→Gn,Algebra.TensorProduct.lift_tmul→Cy,Algebra.TensorProduct.map→zm,Algebra.TensorProduct.tmul_mul_tmul→zi,Algebra.algebraMap→aU,Algebra.ofId→yB,AlgebraicIndependent→zg,CommRing→n5,DFunLike.congr_fun→zh,Field→mD,Finset.mem_image_of_mem→Fz,Finset.mem_singleton→Et,Finset.mem_univ→yU,Finset.smul_sum→wA,Finset.sum_congr→uz,Finsupp.comapDomain_sumElim_comapDomain→G0,Finsupp.optionElim_some→FV,Finsupp.single→zf,Finsupp.weight→ oY,Finsupp.weight_apply→Du,Finsupp.weight_eq_sum→Aa,Fintype.sum_option→z7,Fintype.sum_sum_type→Gk,Fintype.univ_bool→Ef,Function.Injective→sS,Function.Surjective→G2,Function.iterate_succ_apply'→EK,Ideal→ oD,Ideal.Quotient.eq_zero_iff_mem→Ar,Ideal.Quotient.mk→ ox,Ideal.Quotient.mkₐ→G9,Ideal.map_map→wY,Ideal.mem_span_singleton_sup→Gr,Ideal.span→t3
open _root_ renaming IsAlgebraic→zS,IsDomain→th,IsFractionRing→t4,IsFractionRing.injective→wR,IsLocalization→uh,IsLocalization.mk'_mem_map_algebraMap_iff→Fa,IsLocalization.mul_mk'_eq_mk'_of_mul→FK,IsScalarTower→vh,IsScalarTower.algebraMap_apply→Dz,IsScalarTower.of_algebraMap_eq→u9,IsScalarTower.toAlgHom→vk,LinearMap.finrank_le_finrank_of_surjective→G6,Module.Finite→ oZ,Module.Finite.equiv→y5,Module.Finite.of_surjective→Ea,Module.finBasis→xL,Module.finrank→pG,MvPolynomial→lJ,MvPolynomial.C→nq,MvPolynomial.X→cy,MvPolynomial.affineHilbertPolynomial→vl,MvPolynomial.algebraMap_eq→t7,MvPolynomial.algebraMvPolynomial→Bf,MvPolynomial.algebraTensorAlgEquiv→u5,MvPolynomial.algebraTensorAlgEquiv_tmul→FR,MvPolynomial.coeff_weightedHomogeneousComponent→Eg,MvPolynomial.commAlgEquiv→t5,MvPolynomial.eval→qz,MvPolynomial.eval₂Hom_C→vH,MvPolynomial.eval₂Hom_X'→G4,MvPolynomial.induction_on'→EP,MvPolynomial.isLocalization→Dw,MvPolynomial.isWeightedHomogeneous_X→zk,MvPolynomial.map→lI,MvPolynomial.map_X→qm,MvPolynomial.map_map→C4,MvPolynomial.mem_restrictBidegree→qG,MvPolynomial.mem_restrictBidegree_iff_weightedTotalDegree_le→Au,MvPolynomial.mem_support_iff→G8,MvPolynomial.monomial→ oj,MvPolynomial.monomial_add_single→xu,MvPolynomial.mul_mem_restrictBidegree→pL,MvPolynomial.optionEquivLeft→u8,MvPolynomial.pderiv_eq_zero_of_degreeOf_eq_zero→G3,MvPolynomial.quotientBidegreeLE→vG,MvPolynomial.renameEquiv_apply→z8,MvPolynomial.restrictBidegree→sH,MvPolynomial.ringHom_ext→v8
open _root_ renaming MvPolynomial.smul_eq_C_mul→GF,MvPolynomial.support_X→Dv,MvPolynomial.support_map_subset→C9,MvPolynomial.weightedHomogeneousComponent→uJ,MvPolynomial.weightedTotalDegree_pderiv_le_sub→F9,Nat.add_comm→p5,Nat.add_left_comm→FU,Nat.add_sub_of_le→G1,Nat.eq_zero_of_le_zero→Gj,Nat.mul_le_mul_left→Df,Nat.sub_le_sub_right→Ee,Nat.zero_add→uW,Option→lV,Polynomial→ oq,Polynomial.C→ ov,Polynomial.X→pQ,Polynomial.aeval→ oy,Polynomial.aeval_C→xI,Polynomial.aeval_X→zE,Polynomial.degreeLT→xm,Polynomial.derivative_map→FQ,Polynomial.eval_map→ze,Polynomial.le_natDegree_of_ne_zero→Gi,Polynomial.map→x7,Polynomial.ringHom_ext→C5,Prod.mk_add_mk→yL,Prod.snd_sum→zc,RingHom.congr_fun→t8,RingHom.ext→vi,Set.range→p9,Submodule.span→vw,Submodule.subset_span→xW,Submodule.sum_mem→GY,Submonoid→v9,Submonoid.powers→yQ,Subsingleton.elim→yl,congrArg→ oz,inferInstance→vZ,map_add→pC,map_mul→nI,map_ne_zero_iff→zR,map_one→pU,map_pow→sI,map_sub→p7,map_sum→pz,map_zero→ oK
open _root_ renaming mul_assoc→qJ,mul_comm→qx,mul_one→qM,nonZeroDivisors→zd,nonZeroDivisors.ne_zero→z9,one_mul→p6
set_option autoImplicit true
section
namespace aqf
noncomputable section
open DQ ane
end
end aqf
end
section
namespace aR1
noncomputable section
open akS
open scoped Polynomial TensorProduct
variable {F A:Type} [mD F] [n5 A] [c9 F A]
end
end aR1
end
section
namespace czC
noncomputable section
open cu DQ ane aqf MvPolynomial
open scoped BigOperators TensorProduct
end
end czC
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace czy
open aiO
open scoped TensorProduct
noncomputable section
end
end czy
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
namespace aZa
noncomputable section
open DdK1 cu DQ vq MvPolynomial
open scoped Polynomial
variable {n:ℕ}
end
end aZa
end
section
namespace czx
open aiO
open scoped TensorProduct nonZeroDivisors
noncomputable section
set_option backward.isDefEq.respectTransparency false
end
end czx
end
section
namespace czr
noncomputable section
open cu Cu
open MvPolynomial
variable (C₀:sQ)
end
end czr
end
section
namespace MN
noncomputable section
open Finset DdK1 MvPolynomial
open scoped BigOperators Polynomial
theorem aM6 {k σ:Type*} [mD k] [Finite σ]
  (P:oD (lJ σ k)) (hP:P.IsPrime)
  (hdim: (vl P).natDegree=1) :
  ∃ δ:ℕ,0<δ∧affineDegree P=(δ:ℚ) := by
 let H :=vl P
 have hlin:H=ov (H.coeff 0)+Polynomial.C (H.coeff 1)*Polynomial.X:= by
  have hH :H.natDegree<2 := by change (vl P).natDegree<2; omega
  simpa [Finset.sum_range_succ] using H.as_sum_range_C_mul_X_pow' hH
 have evalH (u:ℚ) :H.eval u=H.coeff 0+H.coeff 1*u:= by
  conv_lhs=>rw [hlin]
  simp
 obtain ⟨N,hN⟩:=exists_eval_affineHilbertPolynomial P
 let m:=affineHilbertFunction P (N+1)
 let n:=affineHilbertFunction P N
 have hdiff :affineDegree P=(m:ℚ)-(n:ℚ) := by
  rw [affineDegree,hdim,Nat.factorial_one,Nat.cast_one,p6,Polynomial.leadingCoeff,hdim]
  dsimp only [m,n]
  rw [← hN (N+1) (by omega),← hN N le_rfl]
  change H.coeff 1=H.eval ((N+1 :ℕ) :ℚ) - H.eval (N :ℚ)
  rw [evalH,evalH,Nat.cast_add,Nat.cast_one]
  ring
 have hmn:n< m:= by
  have hpos :=affineDegree_pos hP.ne_top
  rw [hdiff] at hpos
  exact_mod_cast sub_pos.mp hpos
 exact ⟨m-n,Nat.sub_pos_of_lt hmn,hdiff.trans (Nat.cast_sub hmn.le).symm⟩
end
end MN
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace czB
noncomputable section
open cu DQ aqf MvPolynomial
end
end czB
end
section
namespace aZa
noncomputable section
open DdK1 cu DQ MvPolynomial
open scoped Polynomial BigOperators
variable {n:ℕ}
end
end aZa
end
section
namespace aqe
noncomputable section
open cu DQ ane MvPolynomial
end
end aqe
end
section
namespace vq
noncomputable section
open cu MN MvPolynomial
end
end vq
end
section
namespace czA
noncomputable section
open cu DQ aqe MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
end
end czA
end
section
namespace czz
noncomputable section
open aqe MvPolynomial
variable {n:ℕ} {k :Type} [mD k]
variable (I:oD (lJ (lV (Fin n)) k))
end
end czz
end
section
namespace baF
noncomputable section
open DdK1 cu MN MvPolynomial
open scoped Polynomial
end
end baF
end
section
namespace aR1
open DQ Cu akS
open scoped Polynomial
end aR1
end
