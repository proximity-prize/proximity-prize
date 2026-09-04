import ProximityPrize.SubmissionLower.LocatorSplit500Rank

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Source. -/
section PackedLocator_LocatorSplit500Source

/-! Semantic kernel source backed by the isolated Split500 receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit500Source

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
  ConstraintKernel (K := K) 181373000 131071 42000 310 1000
    IRSProfile.domain u0 u1

theorem weighted_exact : 1000 * 181373 = 181373000 := by
  decide

theorem shape : 181373000 + 310 ≤ 131071 * (1383 + 1) := by
  decide

theorem nullity_exact :
    coefficientCount 181373000 131071 42000 310 -
      262144 * localRankBound 1000 42000 310 = 4161068143836058 := by
  rw [LocatorSplit500Coefficient.coefficientCount_exact,
    LocatorSplit500Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    4161068143836058 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    181373000 42000 310 1000 4161068143836058 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorSplit500Source
end PackedLocator_LocatorSplit500Source

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier36 : True := by trivial
end ProximityPrize.SubmissionLower

