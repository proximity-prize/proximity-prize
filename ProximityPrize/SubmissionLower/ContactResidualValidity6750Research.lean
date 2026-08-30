import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTwoTailResidualGeneric6750Research

 







namespace ProximityPrize.SubmissionLower.ContactResidualValidity6750Research

open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch
open ContactTwoTailResidualGeneric6750Research

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 300000

def ResidualValidityConditions (P : UnequalParameters)
    (S : TightParameters) : Prop :=
  P.n = ContactTwoTailParameters6750Research.n ∧
  S.n = ContactTwoTailParameters6750Research.n ∧
  P.w = S.w ∧
  P.a = S.a ∧
  1 ≤ S.s ∧
  S.s < ContactTwoTailParameters6750Research.prime ∧
  1 ≤ S.w ∧
  S.w < ContactTwoTailParameters6750Research.prime ∧
  S.w < S.kappa * S.D ∧
  1 ≤ S.algebraicCap ∧
  S.implicitYCap < ContactTwoTailParameters6750Research.prime ∧
  S.algebraicCap < ContactTwoTailParameters6750Research.prime ∧
  2 * S.implicitYCap * S.algebraicCap <
    ContactTwoTailParameters6750Research.prime ∧
  S.w < S.a ∧
  S.a ≤ S.n ∧
  0 < P.gap ∧
  S.gap = P.gap ∧
  (S.D - 1) / S.w ≤ P.leftY ∧
  S.s ≤ P.leftR ∧
  S.L ≤ P.leftZ ∧
  1 ≤ P.leftR ∧
  P.leftY < ContactTwoTailParameters6750Research.prime ∧
  P.leftR < ContactTwoTailParameters6750Research.prime ∧
  P.leftZ < ContactTwoTailParameters6750Research.prime ∧
  P.mixedCost.y < ContactTwoTailParameters6750Research.prime ∧
  P.mixedCost.r < ContactTwoTailParameters6750Research.prime ∧
  P.mixedCost.z < ContactTwoTailParameters6750Research.prime

theorem validity_of_conditions {P : UnequalParameters} {S : TightParameters}
    (h : ResidualValidityConditions P S) : ResidualValidity P S := by
  rcases h with ⟨hPn, hSn, hw, ha, hs1, hsSmall, hw1, hwSmall,
    hkD, halg1, himpSmall, halgSmall, hmixedSmall, hwa, han,
    hgap, hgapEq, hqY, hqR, hqZ, hleftR1, hleftYSmall,
    hleftRSmall, hleftZSmall, hmixedY, hmixedR, hmixedZ⟩
  exact ⟨hPn, hSn, hw, ha, hs1, hsSmall, hw1, hwSmall,
    hkD, halg1, himpSmall, halgSmall, hmixedSmall, hwa, han,
    hgap, hgapEq, hqY, hqR, hqZ, hleftR1, hleftYSmall,
    hleftRSmall, hleftZSmall, hmixedY, hmixedR, hmixedZ⟩

theorem firstStageConditions_of_bounded_cell :
    ∀ t : Fin 1667, ∀ y : Fin 66, ∀ r : Fin 15,
      ResidualValidityConditions
        (firstStage (t.1 - 1) (y.1 - 1) (r.1 - 1) r.1)
        (firstPivot (t.1 - 1) (r.1 - 1)) := by
  intro t y r
  have hkD : 131071 <
      (2 * (29 - (r.1 - 1)) - 1) * 17097096 := by
    have hr := r.isLt
    omega
  have hsHi : 29 - (r.1 - 1) ≤ 29 := Nat.sub_le _ _
  have hkLo : 1 ≤ 2 * (29 - (r.1 - 1)) - 1 := by omega
  have hkHi : 2 * (29 - (r.1 - 1)) - 1 ≤ 57 := by omega
  have hLLo : 1 ≤ 1668 - (t.1 - 1) := by
    have ht := t.isLt
    omega
  have hLHi : 1668 - (t.1 - 1) ≤ 1668 := Nat.sub_le _ _
  have hAlgPos : 1 ≤
      (2 * (29 - (r.1 - 1)) - 1) * (1668 - (t.1 - 1)) :=
    Nat.mul_pos hkLo hLLo
  have hAlgBound :
      (2 * (29 - (r.1 - 1)) - 1) * (1668 - (t.1 - 1)) ≤
        57 * 1668 := Nat.mul_le_mul hkHi hLHi
  have hAlgSmall :
      (2 * (29 - (r.1 - 1)) - 1) * (1668 - (t.1 - 1)) <
        2130706433 := hAlgBound.trans_lt (by norm_num)
  have hDProd : (2 * (29 - (r.1 - 1)) - 1) * 17097096 ≤
      57 * 17097096 := Nat.mul_le_mul_right 17097096 hkHi
  have hImp :
      ((2 * (29 - (r.1 - 1)) - 1) * 17097096 - 1) / 131071 ≤
        7435 := by omega
  have hMixedSmall :
      2 * (((2 * (29 - (r.1 - 1)) - 1) * 17097096 - 1) / 131071) *
          ((2 * (29 - (r.1 - 1)) - 1) * (1668 - (t.1 - 1))) <
        2130706433 := by
    calc
      _ ≤ 2 * 7435 * (57 * 1668) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hImp) hAlgBound
      _ < 2130706433 := by norm_num
  have hRightZ : 645635 - (t.1 - 1) ≤ 645635 := Nat.sub_le _ _
  have hRightR : 14 - (r.1 - 1) ≤ 14 := Nat.sub_le _ _
  have hRightY :
      (8548548 - (131071 * (y.1 - 1) - r.1) - 1) / 131071 ≤ 65 := by
    omega
  have hMixedY :
      (29 - (r.1 - 1)) * (645635 - (t.1 - 1)) +
          (1668 - (t.1 - 1)) * (14 - (r.1 - 1)) < 2130706433 := by
    calc
      _ ≤ 29 * 645635 + 1668 * 14 :=
        Nat.add_le_add (Nat.mul_le_mul hsHi hRightZ)
          (Nat.mul_le_mul hLHi hRightR)
      _ < 2130706433 := by norm_num
  have hMixedR :
      130 * (645635 - (t.1 - 1)) +
          (1668 - (t.1 - 1)) *
            ((8548548 - (131071 * (y.1 - 1) - r.1) - 1) / 131071) <
        2130706433 := by
    calc
      _ ≤ 130 * 645635 + 1668 * 65 :=
        Nat.add_le_add (Nat.mul_le_mul_left 130 hRightZ)
          (Nat.mul_le_mul hLHi hRightY)
      _ < 2130706433 := by norm_num
  have hMixedZ :
      130 * (14 - (r.1 - 1)) +
          (29 - (r.1 - 1)) *
            ((8548548 - (131071 * (y.1 - 1) - r.1) - 1) / 131071) <
        2130706433 := by
    calc
      _ ≤ 130 * 14 + 29 * 65 :=
        Nat.add_le_add (Nat.mul_le_mul_left 130 hRightR)
          (Nat.mul_le_mul hsHi hRightY)
      _ < 2130706433 := by norm_num
  norm_num [ResidualValidityConditions, firstStage, firstPivot,
    UnequalParameters.gap, UnequalParameters.mixedCost,
    TightParameters.gap, TightParameters.kappa,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    ContactTwoTailParameters6750Research.n,
    ContactTwoTailParameters6750Research.w,
    ContactTwoTailParameters6750Research.errors,
    ContactTwoTailParameters6750Research.prime,
    ContactTwoTailParameters6750Research.agreements,
    ContactTwoTailParameters6750Research.profileA,
    ContactTwoTailParameters6750Research.profileB,
    ContactTwoTailParameters6750Research.Profile.weightedCap]
  repeat' apply And.intro
  all_goals first
    | exact hkD
    | exact hAlgPos
    | exact hAlgSmall
    | exact hMixedSmall
    | exact hMixedY
    | exact hMixedR
    | exact hMixedZ
    | omega

theorem secondStageConditions_of_bounded_cell :
    ∀ t : Fin 1667, ∀ y : Fin 66, ∀ r : Fin 15,
      ResidualValidityConditions
        (secondStage (t.1 - 1) (y.1 - 1) (r.1 - 1) r.1)
        (secondPivot (t.1 - 1) (r.1 - 1)) := by
  intro t y r
  have hkD : 131071 <
      (2 * (14 - (r.1 - 1)) - 1) * 8548548 := by
    have hr := r.isLt
    omega
  have hsHi : 14 - (r.1 - 1) ≤ 14 := Nat.sub_le _ _
  have hkLo : 1 ≤ 2 * (14 - (r.1 - 1)) - 1 := by
    have hr := r.isLt
    omega
  have hkHi : 2 * (14 - (r.1 - 1)) - 1 ≤ 27 := by omega
  have hLLo : 1 ≤ 1666 - (t.1 - 1) := by
    have ht := t.isLt
    omega
  have hLHi : 1666 - (t.1 - 1) ≤ 1666 := Nat.sub_le _ _
  have hAlgPos : 1 ≤
      (2 * (14 - (r.1 - 1)) - 1) * (1666 - (t.1 - 1)) :=
    Nat.mul_pos hkLo hLLo
  have hAlgBound :
      (2 * (14 - (r.1 - 1)) - 1) * (1666 - (t.1 - 1)) ≤
        27 * 1666 := Nat.mul_le_mul hkHi hLHi
  have hAlgSmall :
      (2 * (14 - (r.1 - 1)) - 1) * (1666 - (t.1 - 1)) <
        2130706433 := hAlgBound.trans_lt (by norm_num)
  have hDProd : (2 * (14 - (r.1 - 1)) - 1) * 8548548 ≤
      27 * 8548548 := Nat.mul_le_mul_right 8548548 hkHi
  have hImp :
      ((2 * (14 - (r.1 - 1)) - 1) * 8548548 - 1) / 131071 ≤
        1760 := by omega
  have hMixedSmall :
      2 * (((2 * (14 - (r.1 - 1)) - 1) * 8548548 - 1) / 131071) *
          ((2 * (14 - (r.1 - 1)) - 1) * (1666 - (t.1 - 1))) <
        2130706433 := by
    calc
      _ ≤ 2 * 1760 * (27 * 1666) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hImp) hAlgBound
      _ < 2130706433 := by norm_num
  have hRightZ : 645635 - (t.1 - 1) ≤ 645635 := Nat.sub_le _ _
  have hRightR : 14 - (r.1 - 1) ≤ 14 := Nat.sub_le _ _
  have hRightY :
      (8548548 - (131071 * (y.1 - 1) - r.1) - 1) / 131071 ≤ 65 := by
    omega
  have hMixedY :
      (14 - (r.1 - 1)) * (645635 - (t.1 - 1)) +
          (1666 - (t.1 - 1)) * (14 - (r.1 - 1)) < 2130706433 := by
    calc
      _ ≤ 14 * 645635 + 1666 * 14 :=
        Nat.add_le_add (Nat.mul_le_mul hsHi hRightZ)
          (Nat.mul_le_mul hLHi hRightR)
      _ < 2130706433 := by norm_num
  have hMixedR :
      65 * (645635 - (t.1 - 1)) +
          (1666 - (t.1 - 1)) *
            ((8548548 - (131071 * (y.1 - 1) - r.1) - 1) / 131071) <
        2130706433 := by
    calc
      _ ≤ 65 * 645635 + 1666 * 65 :=
        Nat.add_le_add (Nat.mul_le_mul_left 65 hRightZ)
          (Nat.mul_le_mul hLHi hRightY)
      _ < 2130706433 := by norm_num
  have hMixedZ :
      65 * (14 - (r.1 - 1)) +
          (14 - (r.1 - 1)) *
            ((8548548 - (131071 * (y.1 - 1) - r.1) - 1) / 131071) <
        2130706433 := by
    calc
      _ ≤ 65 * 14 + 14 * 65 :=
        Nat.add_le_add (Nat.mul_le_mul_left 65 hRightR)
          (Nat.mul_le_mul hsHi hRightY)
      _ < 2130706433 := by norm_num
  norm_num [ResidualValidityConditions, secondStage, secondPivot,
    UnequalParameters.gap, UnequalParameters.mixedCost,
    TightParameters.gap, TightParameters.kappa,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    ContactTwoTailParameters6750Research.n,
    ContactTwoTailParameters6750Research.w,
    ContactTwoTailParameters6750Research.errors,
    ContactTwoTailParameters6750Research.prime,
    ContactTwoTailParameters6750Research.agreements,
    ContactTwoTailParameters6750Research.profileA,
    ContactTwoTailParameters6750Research.profileB,
    ContactTwoTailParameters6750Research.profileC,
    ContactTwoTailParameters6750Research.Profile.weightedCap]
  repeat' apply And.intro
  all_goals first
    | exact hkD
    | exact hAlgPos
    | exact hAlgSmall
    | exact hMixedSmall
    | exact hMixedY
    | exact hMixedR
    | exact hMixedZ
    | omega

theorem firstStageValidity_of_bounded_cell
    (t : Fin 1667) (y : Fin 66) (r : Fin 15) :
    FirstStageValidity6750 (t.1 - 1) (y.1 - 1) (r.1 - 1) r.1 :=
  validity_of_conditions
    (firstStageConditions_of_bounded_cell t y r)

theorem secondStageValidity_of_bounded_cell
    (t : Fin 1667) (y : Fin 66) (r : Fin 15) :
    SecondStageValidity6750 (t.1 - 1) (y.1 - 1) (r.1 - 1) r.1 :=
  validity_of_conditions
    (secondStageConditions_of_bounded_cell t y r)

theorem residualCellValidity_of_bounded_cell
    (t : Fin 1667) (y : Fin 66) (r : Fin 15) :
    ResidualCellValidity6750 (t.1 - 1) (y.1 - 1) (r.1 - 1) r.1 :=
  ⟨firstStageValidity_of_bounded_cell t y r,
    secondStageValidity_of_bounded_cell t y r⟩

end ProximityPrize.SubmissionLower.ContactResidualValidity6750Research

#print axioms ProximityPrize.SubmissionLower.ContactResidualValidity6750Research.residualCellValidity_of_bounded_cell
