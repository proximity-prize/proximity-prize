import ProximityPrize.SubmissionLower.MovingSourceSliceMovingBudget6814
namespace ProximityPrize.SubmissionLower.MovingSourceAllSliceCount6814
open RCN057 (WeightBound)
open scoped Classical BigOperators
open RCN002 RCN007 RCN074 RCN076 RCN084 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN159
open RCN199 RCN207 RCN208 RCN234 RCN237 RCN243 RCN244 RCN248 RCN264 RCN267 RCN313 RCN341
open GenericSlicePoints6807 WeightedSliceAssignment6807 SmallSliceBudgets6807 ActiveSliceAssembly6807
open MovingFiberThreeSources6811 HFreeDir6813
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceExtendedPointCount6814 MovingSourcePairFirstCutPole6814 MovingSourceSliceMovingBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000

variable {K I E T : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [Algebra (GenericField K) E] [CharP E 2130706433] [Fintype T]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w
local notation "eta" => (algebraMap Ω E)
local notation "phiE" => RingHom.comp (algebraMap Ω E) (polynomialEmbedding K)

end
end ProximityPrize.SubmissionLower.MovingSourceAllSliceCount6814
