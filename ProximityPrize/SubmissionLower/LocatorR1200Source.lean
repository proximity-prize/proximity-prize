import ProximityPrize.SubmissionLower.LocatorR1200Rank

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Source. -/
section PackedLocator_LocatorR1200Source

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
  ConstraintKernel (K := K) 870590400 131071 328400 1480 4800
    IRSProfile.domain u0 u1

theorem weighted_exact : 4800 * 181373 = 870590400 := by
  decide

theorem shape : 870590400 + 1480 ≤ 131071 * (6642 + 1) := by
  decide

theorem nullity_exact :
    coefficientCount 870590400 131071 328400 1480 -
      262144 * localRankBound 4800 328400 1480 =
        5227117860923383312 := by
  rw [LocatorR1200Coefficient.coefficientCount_exact,
    LocatorR1200Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    5227117860923383312 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    870590400 328400 1480 4800 5227117860923383312 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorR1200Source
end PackedLocator_LocatorR1200Source

