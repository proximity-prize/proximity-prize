import ProximityPrize.SubmissionLower.LowerGeometry



namespace ProximityPrize.SubmissionLower.Koala6831MovingStages

open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (SourceNumbers)
open LocatorPhase6800Audit (powerBandBudget_mono_fuel)

theorem room_remaining_caps (roomOrder : ℕ) (remaining incoming source : FlagDegree)
    (hincoming : Below remaining incoming)
    (hsource : Below ((roomOrder + 1) • remaining) source) :
    remaining.all ≤ min incoming.all (source.all / (roomOrder + 1)) ∧
    middle remaining ≤ min (middle incoming) (middle source / (roomOrder + 1)) ∧
    total remaining ≤ min (total incoming) (total source / (roomOrder + 1)) := by
  have hpos : 0 < roomOrder + 1 := Nat.succ_pos _
  refine ⟨le_min hincoming.1 ((Nat.le_div_iff_mul_le hpos).2 ?_),
    le_min hincoming.2.1 ((Nat.le_div_iff_mul_le hpos).2 ?_),
    le_min hincoming.2.2 ((Nat.le_div_iff_mul_le hpos).2 ?_)⟩
  · rw [Nat.mul_comm]
    exact hsource.1
  · rw [Nat.mul_comm, middle, Nat.mul_add]
    exact hsource.2.1
  · rw [Nat.mul_comm, total, Nat.mul_add, Nat.mul_add]
    exact hsource.2.2







end ProximityPrize.SubmissionLower.Koala6831MovingStages
