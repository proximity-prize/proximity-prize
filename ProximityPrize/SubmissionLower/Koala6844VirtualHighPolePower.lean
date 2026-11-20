import ProximityPrize.SubmissionLower.LowerFoundation



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators
open RCN344

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem poleOrder_pow (v : Place K L) (x : L) (n : ℕ) :
    RCN187.poleOrder v.val (x^n) = (n : ℤ) * RCN187.poleOrder v.val x := by
  unfold RCN187.poleOrder
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  by_cases h : (v.val x).log ≤ 0
  · rw [max_eq_left h, mul_zero, max_eq_left
      (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) h)]
  · have hpos := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right hpos, max_eq_right (mul_nonneg (Int.natCast_nonneg n) hpos)]

theorem finite_pole_sum_le_of_separating_power [IsAlgClosed K]
    (c : SeparableCoordinate K L) (x : L) (n bound : ℕ)
    (power : SeparableCoordinate.value K L c ^ n = x)
    (budget : n * SeparableCoordinate.degree K L c ≤ bound) (W : Finset (Place K L)) :
    (∑ v ∈ W, RCN187.poleOrder v.val x) ≤ (bound : ℤ) := by
  rw [← power]
  simp only [poleOrder_pow, ← Finset.mul_sum]
  have h := SeparableCoordinate.finite_sum_pole_le_degree K L c W
  exact (mul_le_mul_of_nonneg_left h (Int.natCast_nonneg n)).trans
    (by exact_mod_cast budget)

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
