import ProximityPrize.SubmissionBinaryLower.P64C7Retained
import ProximityPrize.SubmissionBinaryLower.P64S3

/-!
# The coefficient-count inequality behind the low-bias profile

All constants are integers. The interpolation count is evaluated by a closed
sum, and its remainder is bounded symbolically.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7ProfileArithmetic

theorem twice_mbox (W : ℕ) :
    2 * (P64Surf.Mbox W : ℤ) =
      ((W / 1048575 : ℕ) + 1 : ℤ) * (2 * W + 2 - 1048575 * (W / 1048575 : ℕ)) := by
  let J := W / 1048575
  have hj : 1048575 * J ≤ W := by simpa [J, Nat.mul_comm] using Nat.div_mul_le_self W 1048575
  have ht : ∀ j ∈ Finset.range (J + 1), ((W - 1048575 * j + 1 : ℕ) : ℤ) =
      (W : ℤ) + 1 - 1048575 * j := by
    intro j hmem
    have hj' : 1048575 * j ≤ W :=
      (Nat.mul_le_mul_left _ (by have := Finset.mem_range.mp hmem; omega)).trans hj
    rw [Nat.cast_add, Nat.cast_sub hj']
    push_cast
    ring
  have he : (P64Surf.Mbox W : ℤ) = ∑ j ∈ Finset.range (J + 1), ((W : ℤ) + 1 - 1048575 * j) := by
    unfold P64Surf.Mbox
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl ht
  have hs := P64Interp.six_mul_sum_range 1 0 ((W : ℤ) + 1) 1048575 (J + 1)
  simp only [zero_mul, sub_zero, one_mul, Nat.cast_add, Nat.cast_one] at hs
  change 2 * (P64Surf.Mbox W : ℤ) = ((J : ℤ) + 1) * (2 * W + 2 - 1048575 * J)
  rw [he]
  nlinarith only [hs]

theorem mbox_quadratic_lower (W : ℕ) :
    (W : ℤ) ^ 2 + 1048577 * W ≤ 2097150 * (P64Surf.Mbox W : ℤ) := by
  let J := W / 1048575
  let r := W % 1048575
  have he : (W : ℤ) = 1048575 * J + r := by
    exact_mod_cast (Nat.div_add_mod W 1048575).symm
  have hr : (r : ℤ) < 1048575 := by exact_mod_cast Nat.mod_lt W (by norm_num : 0 < 1048575)
  have hp : (0 : ℤ) ≤ (1048575 - r) * (r + 2) := mul_nonneg (by omega) (by positivity)
  have hs := twice_mbox W
  change 2 * (P64Surf.Mbox W : ℤ) = ((J : ℤ) + 1) * (2 * W + 2 - 1048575 * J) at hs
  rw [he] at hs ⊢
  nlinarith only [hs, hp]

theorem con_term (μ : ℕ) :
    (((4 * μ - 1) * (4 * μ - 1 + 1) / 2 : ℕ) : ℤ) = 8 * (μ : ℤ) ^ 2 - 2 * μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hsub : 1 ≤ 4 * μ := by omega
  have he : (4 * μ - 1) * (4 * μ - 1 + 1) / 2 = 2 * μ * (4 * μ - 1) := by
    rw [Nat.sub_add_cancel hsub]
    calc _ = (2 * μ * (4 * μ - 1)) * 2 / 2 := by congr 1; ring
      _ = _ := Nat.mul_div_cancel _ (by norm_num)
  rw [he]
  push_cast
  rw [Nat.cast_sub hsub]
  push_cast
  ring

theorem count_slack (h j c m : ℕ) (hj : j ≤ 2097152) (hc : c ≤ 8 * h ^ 2 * 2097152)
    (hcrit : 234354625592 * m ≤ (234354625592 + j) * c) : m ≤ c + 256 * h ^ 2 := by
  have hjc := Nat.mul_le_mul hj hc
  by_contra hn
  have hm : c + 256 * h ^ 2 + 1 ≤ m := by omega
  have hm' := Nat.mul_le_mul_left 234354625592 hm
  nlinarith only [hcrit, hjc, hm', sq_nonneg (h : ℤ)]

theorem profile_algebra (h w S₁ S₂ : ℤ) (hh : 4 ≤ h)
    (hS₁ : h * 1481911 ≤ S₁)
    (hcount : (4 * w - 1482911) ^ 2 + 1048577 * (4 * w - 1482911) ≤
      2097150 * (8 * S₂ - 2 * S₁ + 256 * h ^ 2)) :
    2 * h * w - h ^ 2 * 1048575 - S₂ ≤ 65536 * h ^ 2 := by
  have hs := sq_nonneg (8 * (w - h * 1048575) - 1917245)
  have hh1 : 0 ≤ h * (h - 4) := mul_nonneg (by omega) (by omega)
  have hh2 : 16 ≤ h ^ 2 := by nlinarith
  nlinarith only [hcount, hS₁, hs, hh1, hh2]

end P64C7ProfileArithmetic
end ProximityPrize.SubmissionBinaryLower
