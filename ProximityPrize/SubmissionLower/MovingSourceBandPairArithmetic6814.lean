import ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814
import ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814
namespace ProximityPrize.SubmissionLower.MovingSourceBandPairArithmetic6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN095 BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
open MovingSourcePairRetainedStage6814 MovingSourcePairStageSupplier6814 MovingSourceCoupledClearing6814

def coefficient (t y r : ℕ) (j : Fin 3) : ℕ :=
  4*(RCN326.w+1)*weight (cellNormal t y r) j+3*65539*weight (rawFirstFlag t y r) j

def fixedNumerator (t y r : ℕ) (p : FlagDegree) : ℕ :=
  ∑ j : Fin 3, weight (cellNormal t y r) j*
    flagMixed p (HFreeDir6813.hfreeFirstDir t y r j) (direction j)

theorem pairNumerator_eq (scale z u v t y r : ℕ) (p : FlagDegree) :
    pairNumerator scale z u v t y r p=
      scale*fixedNumerator t y r p+coefficient t y r 0*z+
      coefficient t y r 1*u+coefficient t y r 2*v := by
  simp only [pairNumerator,fixedNumerator,coefficient,price,weight,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Matrix.cons_val_succ]
  ring

end
end ProximityPrize.SubmissionLower.MovingSourceBandPairArithmetic6814
