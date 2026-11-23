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
  numerator : Biform[X]
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
open private card_le_sum_cover from ProximityPrize.SubmissionLower.Fast055
open private closedPoint eval_extend  from ProximityPrize.SubmissionLower.Fast055
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
open private closedPoint   from ProximityPrize.SubmissionLower.Fast055
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
open private K1_14_1_1.quotientBasis K1_14_1_1.mulMatrix K1_14_1_1.mulMatrix_entry mulMatrix_specialize
  mulMatrix_det_ne_zero eval_map_constants from ProximityPrize.SubmissionLower.Fast065
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
open private quotientDegreeLEFactor quotientDegreeLEFactor_surjective from
  ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbert
open private mulQuotient mulQuotient_mk from
  ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComponents
variable {k σ : Type*} [Field k]
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
