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
