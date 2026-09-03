import ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC2

/-!
Version-neutral entry points for the 6802 C2 bound.

The fixed-stage realization imported above carries the 6802 row constants.
This module exposes only the generic cost oracle so finite-accounting code does
not depend on the structural proof's internal geometry.
-/

namespace ProximityPrize.SubmissionLower.LocatorC2Scaffold

open RCN095
open LocatorHybridCostC2

/-- The alternate state-local cost used by the C2 finite-accounting oracle. -/
def rawCostC2 (r v z : ℕ) : ℕ :=
  ordinaryCostOfC2 (⟨z, v, r⟩ : FlagDegree)

theorem rawCostC2_le_padded (r v z : ℕ) :
    rawCostC2 r v z ≤
      LocatorFactorAggregate.paddedCost 131072 131073
        (⟨z, v, r⟩ : FlagDegree) := by
  exact ordinaryCostOfC2_le_padded _

/-- Convert the structural two-branch C2 witness into the scalar oracle used
by a base-envelope certificate. -/
theorem ownBoundC2_le_rawCostC2 {count r v z : ℕ}
    (h : OwnBoundC2 count (⟨z, v, r⟩ : FlagDegree)) :
    count ≤ rawCostC2 r v z := by
  simpa [rawCostC2] using ownBound_le_ordinaryCostOfC2 h

end ProximityPrize.SubmissionLower.LocatorC2Scaffold
