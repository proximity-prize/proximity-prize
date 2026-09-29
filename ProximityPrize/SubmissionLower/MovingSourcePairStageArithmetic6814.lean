import ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814

/-! Check that the actual retained Stage numerator agrees with the paper
main-term ledger. This is not the leading-exception or full packet sum. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePairStageArithmetic6814
open MovingSourcePairRetainedStage6814

theorem checked_pair_numerator :
    pairNumerator 7 4491 (7*28420) (7*98890) 3561 57 12 ⟨3504,45,12⟩=
      5708344862295980862 := by decide +kernel

theorem checked_pair_main_fits :
    pairNumerator 7 4491 (7*28420) (7*98890) 3561 57 12 ⟨3504,45,12⟩/(3*7)=
      271825945823618136 ∧ 271825945823618136<272069082261391681 := by
  rw [checked_pair_numerator]
  decide +kernel

#print axioms checked_pair_main_fits
end ProximityPrize.SubmissionLower.MovingSourcePairStageArithmetic6814
