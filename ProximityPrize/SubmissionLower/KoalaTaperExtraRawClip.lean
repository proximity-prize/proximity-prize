import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option Elab.async false
set_option autoImplicit false

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

/-- A chunk outside the possible offset range has no grade to count. -/
theorem rawChunk_zero (w : Window) (start count : ℕ)
    (outside : start + count + w.gradeHi ≤ w.diagonalLo + 1 ∨
      w.diagonalHi + 1 ≤ start + w.gradeLo) :
    rawChunk w start count = 0 := by
  unfold rawChunk
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro x hx
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp ho
  have empty : min w.gradeHi (w.diagonalHi + 1 - o) ≤
      max w.gradeLo (w.diagonalLo - o) := by
    rcases outside with before | after
    · exact (min_le_left ..).trans ((by omega : w.gradeHi ≤ w.diagonalLo - o).trans
        (le_max_right ..))
    · exact (min_le_right ..).trans
        ((by omega : w.diagonalHi + 1 - o ≤ w.gradeLo).trans (le_max_left ..))
  unfold rawAt
  simp [Nat.sub_eq_zero_of_le empty]

end Low48PrimaryPivot.RawReceipt
