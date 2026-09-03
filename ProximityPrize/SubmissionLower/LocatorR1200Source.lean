import ProximityPrize.SubmissionLower.LocatorR1200Coefficient
import ProximityPrize.SubmissionLower.LocatorR1200Rank

/-! Semantic kernel source backed by the isolated R1200 receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorR1200Source

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
  ConstraintKernel (K := K) 217670400 131071 82100 370 1200
    IRSProfile.domain u0 u1

theorem weighted_exact : 1200 * 181392 = 217670400 := by
  decide

theorem shape : 217670400 + 370 ≤ 131071 * (1660 + 1) := by
  decide

theorem nullity_exact :
    coefficientCount 217670400 131071 82100 370 -
      262144 * localRankBound 1200 82100 370 =
        19825077939631510 := by
  rw [LocatorR1200Coefficient.coefficientCount_exact,
    LocatorR1200Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    19825077939631510 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    217670400 82100 370 1200 19825077939631510 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorR1200Source
