import ProximityPrize.SubmissionLower.MovingSourceFactorIsolation6814
import ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814
namespace ProximityPrize.SubmissionLower.MovingSourcePairMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814
open MovingSourceMovingDegrees6814 MovingSourceCoupledClearing6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
local instance : Algebra (RatFunc Omega) OmegaT := targetAlgebra Omega
local instance : IsScalarTower Omega (RatFunc Omega) OmegaT := target_tower Omega

end
end ProximityPrize.SubmissionLower.MovingSourcePairMovingDegrees6814
