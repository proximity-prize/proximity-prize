import ProximityPrize.SubmissionLower.MovingSourceWholeCount6814

/-! Identify the canonical generic target field with the rational-base
structure expected by the existing embedding-point certificate. -/
namespace ProximityPrize.SubmissionLower.MovingSourceTargetField6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open RCN135

variable (K : Type) [Field K]

theorem coefficientEmbedding_eq_algebraMap :
    coefficientEmbedding K=algebraMap K (GenericField K) := by
  ext c
  change algebraMap (RationalBase K) (GenericField K)
    (algebraMap (Polynomial K) (RationalBase K) (algebraMap K (Polynomial K) c))=
      algebraMap K (GenericField K) c
  rw [←IsScalarTower.algebraMap_apply K (Polynomial K) (RationalBase K),
    ←IsScalarTower.algebraMap_apply K (RationalBase K) (GenericField K)]

def rationalEmbedding : RatFunc K →ₐ[K] GenericField K :=
  (IsScalarTower.toAlgHom K (RationalBase K) (GenericField K)).comp
    (RatFunc.toFractionRingAlgEquiv K K).toAlgHom

theorem rationalEmbedding_variable :
    rationalEmbedding K (RCN202.rationalVariable K)=initialCoordinate K := by
  change algebraMap (RationalBase K) (GenericField K)
    ((algebraMap (Polynomial K) (RatFunc K) Polynomial.X).toFractionRing)=_
  rw [←RatFunc.ofFractionRing_algebraMap]
  rfl

abbrev targetAlgebra : Algebra (RatFunc K) (GenericField K) :=
  (rationalEmbedding K).toRingHom.toAlgebra

theorem target_tower :
    letI := targetAlgebra K
    IsScalarTower K (RatFunc K) (GenericField K) := by
  letI := targetAlgebra K
  exact IsScalarTower.of_algebraMap_eq fun c => ((rationalEmbedding K).commutes c).symm

theorem target_variable :
    letI := targetAlgebra K
    algebraMap (RatFunc K) (GenericField K) (RCN202.rationalVariable K)=initialCoordinate K :=
  rationalEmbedding_variable K

#print axioms target_tower
#print axioms target_variable
end
end ProximityPrize.SubmissionLower.MovingSourceTargetField6814
