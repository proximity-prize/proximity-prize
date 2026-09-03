import ProximityPrize.SubmissionLower.LocatorSplit500Coefficient
import ProximityPrize.SubmissionLower.LocatorSplit500Rank

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
  ConstraintKernel (K := K) 90696000 131071 21000 155 500
    IRSProfile.domain u0 u1

theorem weighted_exact : 500 * 181392 = 90696000 := by
  decide

theorem shape : 90696000 + 155 ≤ 131071 * (691 + 1) := by
  decide

theorem nullity_exact :
    coefficientCount 90696000 131071 21000 155 -
      262144 * localRankBound 500 21000 155 = 230574129441305 := by
  rw [LocatorSplit500Coefficient.coefficientCount_exact,
    LocatorSplit500Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    230574129441305 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    90696000 21000 155 500 230574129441305 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorSplit500Source
