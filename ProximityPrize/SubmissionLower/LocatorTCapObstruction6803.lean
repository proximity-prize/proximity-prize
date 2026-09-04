import ProximityPrize.SubmissionLower.LocatorCapArithmetic6803
import ProximityPrize.SubmissionLower.LocatorSelectionArithmetic6803
import ProximityPrize.SubmissionLower.PackedLegacyCore2

/-! The isolated TCap quotient-dimension obstruction. -/

namespace ProximityPrize.SubmissionLower.LocatorTCapObstruction6803

open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156
  RCN130

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

theorem common_total_le
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (F : MvPolynomial (Fin 4) IRSProfile.Field) (hF : F ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := IRSProfile.Field)
      32826703 131071 6679 56 181 IRSProfile.domain u0 u1,
      F ∣ reconstruct IRSProfile.Field 32826703 131071 6679 56 v.1) :
    wt residualTotalWeights F ≤ 6676 := by
  by_contra hnot
  have ht : 6677 ≤ wt residualTotalWeights F :=
    Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnot)
  have hdivK : ∀ v : ConstraintKernel (K := IRSProfile.Field)
      32826703 131071 6679 56 181 IRSProfile.domain u0 u1,
      F ∣ kernelReconstructLinear (K := IRSProfile.Field)
        32826703 131071 6679 56 181 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq : ∀ v : ConstraintKernel (K := IRSProfile.Field)
      32826703 131071 6679 56 181 IRSProfile.domain u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K := IRSProfile.Field)
          (I := IRSProfile.Index) 32826703 131071 6679 56 181
          IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox IRSProfile.Field
          32826703 131071 2 56 := by
    have h := LocatorLowQuotient.quotient_box_of_full_divisor
      (K := IRSProfile.Field) (I := IRSProfile.Index)
      32826703 131071 6679 56 181 0 6677 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht
      (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero, show 6679 - 6677 = 2 by decide] using h v
  have hobs :
      coefficientCount 32826703 131071 6679 56 -
        Fintype.card IRSProfile.Index * localRankBound 181 6679 56 ≤
          coefficientCount 32826703 131071 2 56 :=
    common_divisor_dimension_obstruction
      (K := IRSProfile.Field) (I := IRSProfile.Index)
      32826703 131071 6679 56 181 32826703 2 56
      IRSProfile.domain u0 u1 F hF hdivK hq
  rw [LocatorCapArithmetic6803.index_card] at hobs
  exact (not_lt_of_ge hobs)
    (by
      simpa only [LocatorSelectionArithmetic6803.weightedTCap] using
        LocatorSelectionArithmetic6803.kernelTCap_total_quotient_lt)

end

end ProximityPrize.SubmissionLower.LocatorTCapObstruction6803
