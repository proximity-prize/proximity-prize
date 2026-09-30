import ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814
namespace ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN135 RCN136 RCN159 RCN174
open RCN238 RCN243 RCN244 RCN264 RCN312 RCN341
open MovingSourceProjectionFamily6814 MovingSourceGammaProjections6814 MovingSourceLinearCycleFamily6814
open MovingSourceFrameZeroCount6814 MovingSourceProperSeedCount6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev PersistentComponent (S : Stage K I Gamma x p flag errorCap stageSupport) :=
  {C : FirstTailComponent S //
    Transcendental (GenericField K) (coordinate (GenericField K) C.1 2) ∧
      ∀ delay, globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1+delay)∈C.1}

end
end ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814
