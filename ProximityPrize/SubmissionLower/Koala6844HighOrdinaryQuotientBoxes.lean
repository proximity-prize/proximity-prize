import ProximityPrize.SubmissionLower.Koala6831QuotientBoxes
import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryQuotient

namespace ProximityPrize.SubmissionLower.Koala6844HighOrdinaryQuotient

export Koala6831Quotient (separatedExponents SeparatedIndex separatedBox separatedColumns separatedBox_finrank separatedColumns_mono_cutoff ordinaryExponents OrdinaryIndex ordinaryBox ordinaryColumns ordinaryBox_finrank ordinaryColumns_mono_cutoff)

open scoped BigOperators

theorem longSeparatedDimensionGate (excess : ℕ) (long : 9800 ≤ excess) :
    separatedColumns (16 * 180958 - 131071 - excess) 131071 21 21 177 161 +
      262144 * (separatedColumns 16 1 15 22 178 162 -
        separatedColumns 15 1 14 21 177 161) <
      separatedColumns (16 * 180958) 131071 22 22 178 162 := by
  have threshold :
      separatedColumns (16 * 180958 - 131071 - 9800) 131071 21 21 177 161 +
        262144 * (separatedColumns 16 1 15 22 178 162 -
          separatedColumns 15 1 14 21 177 161) <
        separatedColumns (16 * 180958) 131071 22 22 178 162 := by
    decide +kernel
  apply lt_of_le_of_lt _ threshold
  exact Nat.add_le_add_right (separatedColumns_mono_cutoff _ _ _ _ _ (Nat.sub_le_sub_left long _)) _

def ordinaryProfiles : Fin 9 → ℕ × ℕ × ℕ :=
  ![(14, 19, 166), (11, 15, 65), (6, 8, 30), (5, 6, 19), (4, 5, 13),
    (3, 4, 15), (3, 4, 13), (3, 4, 12), (2, 2, 14)]

set_option maxRecDepth 30000 in
theorem ordinaryDimensionGate (c : Fin 9) (excess : ℕ) (large : 11500 ≤ excess) :
    let (m, y, L) := ordinaryProfiles c
    ordinaryColumns (m * 180958 - 131071 - excess) 131071 (y - 1) (L - (c.val + 2)) +
      262144 * (ordinaryColumns m 1 (m - 1) L -
        ordinaryColumns (m - 1) 1 (m - 2) (L - (c.val + 2))) <
      ordinaryColumns (m * 180958) 131071 y L := by
  have threshold :
      let (m, y, L) := ordinaryProfiles c
      ordinaryColumns (m * 180958 - 131071 - 11500) 131071 (y - 1) (L - (c.val + 2)) +
        262144 * (ordinaryColumns m 1 (m - 1) L -
          ordinaryColumns (m - 1) 1 (m - 2) (L - (c.val + 2))) <
        ordinaryColumns (m * 180958) 131071 y L := by
    fin_cases c <;> decide +kernel
  cases profile : ordinaryProfiles c with
  | mk m caps =>
      obtain ⟨y, L⟩ := caps
      simp only [profile] at threshold ⊢
      apply lt_of_le_of_lt _ threshold
      exact Nat.add_le_add_right (ordinaryColumns_mono_cutoff _ _ _ (Nat.sub_le_sub_left large _)) _


end ProximityPrize.SubmissionLower.Koala6844HighOrdinaryQuotient
