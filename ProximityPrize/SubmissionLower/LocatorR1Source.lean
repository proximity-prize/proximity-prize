import ProximityPrize.SubmissionLower.LocatorR1Rank

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1Source. -/
section PackedLocator_LocatorR1Source

/-! Semantic kernel source backed by the isolated R1 receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorR1Source

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

abbrev Kernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 217647600 131071 82100 370 1200
    IRSProfile.domain u0 u1

theorem weighted_exact : 1200 * 181373 = 217647600 := by
  decide

theorem shape : 217647600 + 370 ≤ 131071 * (1660 + 1) := by
  decide

theorem nullity_exact :
    coefficientCount 217647600 131071 82100 370 -
      262144 * localRankBound 1200 82100 370 =
        18811500529412710 := by
  rw [LocatorR1Coefficient.coefficientCount_exact,
    LocatorR1Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    18811500529412710 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    217647600 82100 370 1200 18811500529412710 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorR1Source
end PackedLocator_LocatorR1Source

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier27 : True := by trivial
end ProximityPrize.SubmissionLower

