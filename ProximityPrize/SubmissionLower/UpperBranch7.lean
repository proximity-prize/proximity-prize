import ProximityPrize.SubmissionLower.GoldBranch6N5
import ProximityPrize.SubmissionLower.UpperBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_7
noncomputable section
open Polynomial MvPolynomial
open P1 (I K node p)
open K1_14 (FX L seedEmbedding)
open K1_14_6 (Biform ClosedField rootPoint)
abbrev box (a b : ℕ) := restrictBidegree (Fin 2) FX a b
structure CRTChart (w : ℕ) where
  denominator : Biform
  numerator : (Polynomial Biform)
  degree_numerator : numerator.natDegree < 2 * w
  bound_denominator : denominator ∈ box 0 (2 * w)
  bound_numerator : ∀ j, numerator.coeff j ∈ box 0 (2 * w)
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open Polynomial Finset MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
open P1 (K I node agreement blockLength)
open K1_14 (FX)
open K1_14_6 (Biform ClosedField rootPoint)
open K1_14_6 (card_le_sum_cover)
open K1_14_6_2 (closedPoint eval_extend)
end
end P1_7_7
end
section
namespace P1_7_7
open P1 (HighBand agreement blockLength)
open P1_7 (degreeAt   quotientOrder   ceilRatio )
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
open P1 (K)
open P1_7 (regularRoot)
open K1_14 (Equation FX SeedBound atMark)
open K1_14_6 (ClosedField)
open K1_14_6_2 (closedPoint)
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open MvPolynomial
open K1_14_6 (ClosedField)
open scoped BigOperators
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open Polynomial MvPolynomial
open P1 (AnchorModel AnchoredFamily HighBand I K agreement node p)
open P1_7 (AdjacentChart GradeIndex  Reduced regularRoot grades )
open K1_14 (Equation FX L SeedBound seedEmbedding)
open scoped BigOperators
end
end P1_7_7
end
section
namespace P1_7_7_1
noncomputable section
open Polynomial Module K1_14_1
open K1_14 (L)
open scoped Polynomial BigOperators
open K1_14_1_1 (quotientBasis mulMatrix mulMatrix_entry mulMatrix_specialize mulMatrix_det_ne_zero eval_map_constants)
end
end P1_7_7_1
end
section
namespace P1_7_7_1
noncomputable section
open P1 (AnchorModel AnchoredFamily K p)
open P1_7 (AdjacentChart)
open K1_14 (L FX liftPoly seedEmbedding)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair)
open K1_14_6 (Biform rootPoint)
open P1_7_7 (CRTChart box)
open MvPolynomial (mem_restrictBidegree mem_restrictBidegree_mono mul_mem_restrictBidegree)
open Polynomial
open scoped Polynomial BigOperators
end
end P1_7_7_1
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open Polynomial
open scoped BigOperators
end
end P1_7_7_2
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open P1 (K p)
open K1_14 (Equation FX SeedBound seedEmbedding atX liftPoly)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant     cleared
  markEval eval_cleared derivativeAt)
open P1_7_7 (box)
open MvPolynomial
open scoped Polynomial
local notation "Y" => MvPolynomial.X (R := FX) (none : Option (Fin 2))
end
end P1_7_7_2
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open P1 (I K node p)
open P1_7 (regularRoot)
open P1_7_7 (CRTChart box  )
open K1_14 (L FX seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant   markEval eval_flatten )
open Polynomial MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
end
end P1_7_7_2
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial
open scoped BigOperators
end
end P1_7_7_3
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial Filter
variable {k σ : Type*} [Field k]
private def quotientDegreeLEFactor {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J) (N : ℕ) :
    quotientDegreeLE I N →ₗ[k] quotientDegreeLE J N :=
  ((Ideal.Quotient.factorₐ k hIJ).toLinearMap.domRestrict (quotientDegreeLE I N)).codRestrict
    (quotientDegreeLE J N) fun x ↦ by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
      rw [LinearMap.domRestrict_apply, ← hpx]
      exact mk_mem_quotientDegreeLE hp
private theorem quotientDegreeLEFactor_surjective {I J : Ideal (MvPolynomial σ k)}
    (hIJ : I ≤ J) (N : ℕ) : Function.Surjective (quotientDegreeLEFactor hIJ N) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
  exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩
private def mulQuotient (I K : Ideal (MvPolynomial σ k)) (s : MvPolynomial σ k)
    (h : ∀ p ∈ I, s * p ∈ K) : (MvPolynomial σ k ⧸ I) →ₗ[k] MvPolynomial σ k ⧸ K :=
  (I.restrictScalars k).liftQ ((Ideal.Quotient.mkₐ k K).toLinearMap ∘ₗ LinearMap.mulLeft k s)
    fun p hp ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h p hp)
private theorem mulQuotient_mk {I K : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    (h : ∀ p ∈ I, s * p ∈ K) (p : MvPolynomial σ k) :
    mulQuotient I K s h (Ideal.Quotient.mk I p) = Ideal.Quotient.mk K (s * p) :=
  rfl
end
end P1_7_7_3
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial
open scoped BigOperators
end
end P1_7_7_3
end
