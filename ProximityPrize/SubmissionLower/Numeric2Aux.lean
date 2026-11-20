import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast022
set_option Elab.async false

section PackSource_K1_13_2_3_2Aux
set_option autoImplicit true
namespace K1_13_2_3_2

open K1_13_2 Finset
open scoped BigOperators

private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]

private def denPolynomial (q r : ℤ) : ℤ :=
  2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)

private theorem twice_den (u : ℤ) (h : 0 ≤ u) :
    2 * denominator u = denPolynomial (u / 6) (u % 6) := by
  let q := u / 6
  let r := u % 6
  simp only [denominator, not_lt.mpr h, ite_false, denPolynomial]
  change 2 * (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) = _
  have hr := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at hr
  change _ = denPolynomial q r
  unfold denPolynomial
  linear_combination hr + q * twice_half r + (57 + 6 * r) * twice_half q

/-- The first four terms sum the complete groups of six denominator coefficients.
The other terms sum the first `r` coefficients of the next group. -/
private def denPrefixPolynomial (q r : ℤ) : ℤ :=
  984 * q + 3084 * q * (q - 1) + 1728 * q * (q - 1) * (q - 2) +
    216 * q * (q - 1) * (q - 2) * (q - 3) + (24 * r + 4 * (r - 1) * r * (r + 1)) +
    q * (528 * r + 84 * (r - 1) * r + 4 * (r - 2) * (r - 1) * r) +
    (684 * r + 36 * (r - 1) * r) * q * (q - 1) + 144 * r * q * (q - 1) * (q - 2)

private def denPrefix (n : ℤ) : ℤ := denPrefixPolynomial (n / 6) (n % 6)

private theorem denPrefix_step (n : ℤ) (hn : 0 ≤ n) :
    denPrefix (n + 1) = denPrefix n + 24 * denominator n := by
  have hden := twice_den n hn
  have hq : (n + 1) / 6 = n / 6 + (n % 6 + 1) / 6 := by omega
  have hr : (n + 1) % 6 = (n % 6 + 1) % 6 := by omega
  have hlo : 0 ≤ n % 6 := by omega
  have hhi : n % 6 < 6 := by omega
  rw [denPrefix, denPrefix, hq, hr]
  generalize n % 6 = r at hden hlo hhi ⊢
  interval_cases r <;> norm_num [denPrefixPolynomial, denPolynomial] at hden ⊢ <;>
    linear_combination (norm := ring_nf) -12 * hden

private theorem denPrefix_eq (n : ℕ) :
    24 * (∑ u ∈ range n, denominator (u : ℤ)) = denPrefix n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ, denPrefix_step _ (by omega)]

private theorem sum_shift (f : ℤ → ℤ) (hz : ∀ x < 0, f x = 0) (n a : ℕ) :
    (∑ u ∈ range n, f ((u : ℤ) - a)) = ∑ u ∈ range (n - a), f (u : ℤ) := by
  have hzero (b : ℕ) (hb : b ≤ a) : (∑ u ∈ range b, f ((u : ℤ) - a)) = 0 := by
    exact sum_eq_zero fun u hu => hz _ (by have := mem_range.mp hu; omega)
  by_cases h : a ≤ n
  · conv_lhs => rw [← Nat.add_sub_of_le h, sum_range_add]
    rw [hzero a le_rfl, zero_add]
    apply sum_congr rfl
    intro u _
    congr 1
    push_cast
    ring
  · rw [hzero n (by omega), show n - a = 0 by omega, sum_range_zero]

theorem sum_shift_cumulative (d n a : ℕ) :
    (∑ u ∈ range n, cumulative (d : ℤ) ((u : ℤ) - a)) =
      ∑ u ∈ range (n - a), cumulative (d : ℤ) (u : ℤ) :=
  sum_shift _ (fun x hx => by simp [cumulative, hx]) n a

/-- The cumulative numerator applied to the scaled denominator prefix. -/
def cumulativePrefix (d n : ℕ) : ℤ :=
  denPrefix n - denPrefix (n - (d + 1) : ℕ) - denPrefix (n - (d + 2) : ℕ) -
    denPrefix (n - (d + 3) : ℕ) + denPrefix (n - (2 * d + 3) : ℕ) +
    denPrefix (n - (2 * d + 4) : ℕ) + denPrefix (n - (2 * d + 5) : ℕ) -
    denPrefix (n - (3 * d + 6) : ℕ)

private theorem cumulative_expand (d u : ℕ) (hu : u ≤ 3 * d) :
    cumulative (d : ℤ) (u : ℤ) =
      denominator u - denominator ((u : ℤ) - (d + 1 : ℕ)) -
        denominator ((u : ℤ) - (d + 2 : ℕ)) - denominator ((u : ℤ) - (d + 3 : ℕ)) +
        denominator ((u : ℤ) - (2 * d + 3 : ℕ)) + denominator ((u : ℤ) - (2 * d + 4 : ℕ)) +
        denominator ((u : ℤ) - (2 * d + 5 : ℕ)) - denominator ((u : ℤ) - (3 * d + 6 : ℕ)) := by
  have hd : ¬ (d : ℤ) < 0 := by omega
  have hu₀ : ¬ (u : ℤ) < 0 := by omega
  simp [cumulative, hd, hu₀, min_eq_left (show (u : ℤ) ≤ 3 * (d : ℤ) by omega)]
  ring_nf

theorem prefix_eq (d n : ℕ) (hn : n ≤ 3 * d + 1) :
    24 * (∑ u ∈ range n, cumulative (d : ℤ) (u : ℤ)) = cumulativePrefix d n := by
  have hs (a : ℕ) : 24 * (∑ u ∈ range n, denominator ((u : ℤ) - a)) =
      denPrefix (n - a : ℕ) := by
    rw [sum_shift _ (fun x hx => by simp [denominator, hx]), denPrefix_eq]
  rw [sum_congr rfl (fun u hu => cumulative_expand d u (by have := mem_range.mp hu; omega))]
  simp only [cumulativePrefix, sum_sub_distrib, sum_add_distrib, mul_sub, mul_add, hs, denPrefix_eq]

end K1_13_2_3_2
end PackSource_K1_13_2_3_2Aux
