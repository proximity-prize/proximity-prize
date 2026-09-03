import ProximityPrize.SubmissionLower.LocatorSplit390Coefficient
import ProximityPrize.SubmissionLower.LocatorSplit390Rank

/-! Semantic kernel source backed by the isolated Split390 receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit390Source

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
  ConstraintKernel (K := K) 70742880 131071 19500 120 390
    IRSProfile.domain u0 u1

theorem weighted_exact : 390 * 181392 = 70742880 := by
  decide

theorem shape : 70742880 + 120 ≤ 131071 * (539 + 1) := by
  decide

theorem nullity_exact :
    coefficientCount 70742880 131071 19500 120 -
      262144 * localRankBound 390 19500 120 = 103687669979190 := by
  rw [LocatorSplit390Coefficient.coefficientCount_exact,
    LocatorSplit390Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    103687669979190 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    70742880 19500 120 390 103687669979190 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorSplit390Source
