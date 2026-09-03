import ProximityPrize.SubmissionLower.LocatorC2Scaffold

namespace ProximityPrize.SubmissionLower.LocatorC2Arithmetic

open RCN095 LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1
  LocatorHybridCostC2

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- On every state where the C2 branch is available, it is already below the
padded branch.  Thus the defensive minimum in `ordinaryCostOfC2` never changes
branches. -/
theorem hybridCostC2_le_padded_of_applies (p : FlagDegree)
    (hp : HybridAppliesC2 p) :
    hybridCostC2 p ≤ paddedCost 131072 131073 p := by
  rcases p with ⟨z, v, r⟩
  change 3 ≤ r ∧ r + 2 ≤ v + r at hp
  have hr : 3 ≤ r := hp.1
  have hv : 2 ≤ v := by omega
  have hpadS : padS (⟨z, v, r⟩ : FlagDegree) = r := by
    unfold padS
    change max r 2 = r
    exact max_eq_left (by omega)
  have hpadY : padY (⟨z, v, r⟩ : FlagDegree) = v + r := by
    unfold padY
    rw [hpadS]
    simp only [middle]
    exact max_eq_left (by omega)
  have hpadT : padT (⟨z, v, r⟩ : FlagDegree) = z + v + r := by
    unfold padT
    rw [hpadY]
    simp only [total]
    exact max_eq_left (by omega)
  have hrShift : r = (r - 3) + 3 := by omega
  have hvShift : v = (v - 2) + 2 := by omega
  unfold hybridCostC2 reducedTail hybridCoordinateC1 paddedCost paddedTail
    movingFiber movingCut rationalFlag flagMixed
  simp only [hpadS, hpadY, hpadT, add_zOnly, add_yz, add_all]
  rw [hrShift, hvShift]
  simp +arith
  have hmiddle :
      (v - 2) + (r - 3) + 2 - (r - 3) = (v - 2) + 2 := by omega
  have hmiddlePred :
      (v - 2) + 2 - 1 = (v - 2) + 1 := by omega
  have htotal :
      z + (v - 2) + (r - 3) - ((v - 2) + (r - 3)) = z := by omega
  rw [hmiddle, hmiddlePred, htotal]
  let extra :=
    1271204674566 +
    738678144483 * z +
    738678144483 * (v - 2) +
    1082267794820 * (r - 3) +
    206142439272 * (v - 2) * z +
    103071219636 * (v - 2) ^ 2 +
    481011695368 * (r - 3) * z +
    481011695368 * (r - 3) * (v - 2) +
    240505847684 * (r - 3) ^ 2 +
    103074496464 * (r - 3) * (v - 2) * z +
    51537248232 * (r - 3) * (v - 2) ^ 2 +
    51537248232 * (r - 3) ^ 2 * z +
    51537248232 * (r - 3) ^ 2 * (v - 2) +
    17179082744 * (r - 3) ^ 3
  calc
    _ ≤ _ + extra := Nat.le_add_right _ _
    _ = _ := by
      dsimp only [extra]
      ring

theorem ordinaryCostOfC2_eq_hybrid (p : FlagDegree)
    (hp : HybridAppliesC2 p) : ordinaryCostOfC2 p = hybridCostC2 p := by
  unfold ordinaryCostOfC2
  rw [if_pos hp, min_eq_left (hybridCostC2_le_padded_of_applies p hp)]

end ProximityPrize.SubmissionLower.LocatorC2Arithmetic
