import ProximityPrize.SubmissionBinaryLower.P64C6Weights
import ProximityPrize.SubmissionBinaryLower.P64AffineSum

/-!
# Closed counts for the flat interpolation equations

All sums are proved symbolically. No finite box is enumerated by the kernel.
Multiplying by six keeps the exact formula and its upper bound integral.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Counts

open P64C6Boxes

theorem six_card_conditions (s q e : ℕ) (he : q * s ≤ e) :
    6 * ((conditions s q e).card : ℤ) =
      3 * s * (s + 1) * (e + 1) - q * s * (s - 1) * (s + 1) := by
  rw [card_conditions, Nat.cast_sum]
  have ht : ∀ b ∈ Finset.range s,
      (((s - b) * (e + 1 - q * b) : ℕ) : ℤ) =
        ((s : ℤ) - 1 * b) * ((e : ℤ) + 1 - q * b) := by
    intro b hb
    have hbs : b ≤ s := Nat.le_of_lt (Finset.mem_range.mp hb)
    have hqb : q * b ≤ e + 1 := (Nat.mul_le_mul_left q hbs).trans (by omega)
    rw [Nat.cast_mul, Nat.cast_sub hbs, Nat.cast_sub hqb]
    push_cast
    ring
  rw [Finset.sum_congr rfl ht, P64Interp.six_mul_sum_range]
  ring

/-- Six times the upper bound for the number of conditions after local cofactors. -/
def netUpper6 (s q d μ e : ℕ) : ℤ :=
  6 * μ * s * e + 3 * ((d : ℤ) - q * μ) * s ^ 2 +
    6 * μ * s + 3 * d * s + 3 * d * μ ^ 2 + 3 * q * s * μ ^ 2

theorem net_count_le (s q d μ e : ℕ) (hμ : μ ≤ s) (he : q * s + d ≤ e) :
    6 * ((conditions s q e).card : ℤ) -
      6 * ((conditions (s - μ) q (e - d)).card : ℤ) ≤ netUpper6 s q d μ e := by
  have hd : d ≤ e := by omega
  have he' : q * (s - μ) ≤ e - d := by
    have hmul := Nat.mul_le_mul_left q (Nat.sub_le s μ)
    omega
  rw [six_card_conditions s q e (by omega), six_card_conditions (s - μ) q (e - d) he']
  rw [Nat.cast_sub hμ, Nat.cast_sub hd]
  have hm : (0 : ℤ) ≤ (μ : ℤ) * (μ - 1) := by
    cases μ with
    | zero => norm_num
    | succ μ =>
        rw [Nat.cast_succ, add_sub_cancel_right]
        positivity
  have hp : (0 : ℤ) ≤ (μ : ℤ) * (μ - 1) * (3 * (e + 1) + q * (μ + 1)) :=
    mul_nonneg hm (by positivity)
  have hn : (0 : ℤ) ≤ 6 * (d : ℤ) * s * μ + 3 * d * μ +
      (μ : ℤ) * (μ - 1) * (3 * (e + 1) + q * (μ + 1)) := by positivity
  apply le_of_sub_nonneg
  convert hn using 1 <;> unfold netUpper6 <;> ring

end P64C6Counts
end ProximityPrize.SubmissionBinaryLower
