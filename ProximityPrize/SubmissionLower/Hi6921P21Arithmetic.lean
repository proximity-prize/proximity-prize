import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_2_1Arithmetic
set_option autoImplicit true
namespace H21_2_1

open K21 H21 H21_2 Finset

open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

open private nodeRow from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

open private nodeRow_eq from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

open private nodeCost from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

open private poleSlope from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

open private debit_eq from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

/-- Twice the signed volume minus the whole last-cutoff allowance is affine in height. -/
private def widthBase (s : Shape) : ℤ :=
  ∑ q ∈ range (s.B + 1), (((min q s.J : ℕ) : ℤ) + 1) *
    (2 * ((s.m : ℤ) * 180169 - (q : ℤ) * 131071) + min q s.J)

open private widthSlope from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

private theorem width_cast (h r : ℕ) (s : Shape) (q j : ℕ)
    (hh : h ≤ 131071) (hq : q ≤ s.B)
    (hw : s.B * (131071 - h) < cutoffCount h r s) :
    (rawWidth h r s q j : ℤ) =
      (s.m : ℤ) * 180169 - 2 * (h : ℤ) * r + j - (q : ℤ) * (131071 - h) := by
  have hq' := (Nat.mul_le_mul_right (131071 - h) hq).trans hw.le
  have hbuf : 2 * h * r ≤ s.m * 180169 := by unfold cutoffCount at hw; omega
  unfold rawWidth cutoffCount at *
  rw [Nat.cast_sub (by omega : q * (131071 - h) ≤ s.m * 180169 - 2 * h * r + j)]
  push_cast [Nat.cast_sub hh, Nat.cast_sub hbuf]
  rfl

private theorem volume_eq (h r mode : ℕ) (s : Shape) (hh : h ≤ 131071)
    (hw : s.B * (131071 - h) < cutoffCount h r s) :
    2 * ((rawVolume h r s : ℤ) - mode * (movingCeiling h s : ℤ)) =
      (triangle s.U : ℤ) * (widthBase s + h * widthSlope s r mode) := by
  calc
    _ = (triangle s.U : ℤ) * ∑ q ∈ range (s.B + 1), 2 *
          ∑ j ∈ range (min q s.J + 1), ((rawWidth h r s q j : ℤ) - mode * (2 * h * j)) := by
      unfold rawVolume movingCeiling shapeSum
      push_cast [Nat.cast_sum]
      simp only [sum_sub_distrib, ← mul_sum, mul_sub]
      ring
    _ = (triangle s.U : ℤ) * (widthBase s + h * widthSlope s r mode) := by
      unfold widthBase widthSlope
      congr 1
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro q hqr
      have hq : q ≤ s.B := Nat.le_of_lt_succ (mem_range.mp hqr)
      simp_rw [width_cast h r s q _ hh hq hw]
      let a : ℤ := (s.m : ℤ) * 180169 - 2 * (h : ℤ) * r - (q : ℤ) * (131071 - h)
      let b : ℤ := 1 - 2 * (h : ℤ) * mode
      have hrow : ∀ j : ℕ,
          (s.m : ℤ) * 180169 - 2 * (h : ℤ) * r + j - (q : ℤ) * (131071 - h) -
            mode * (2 * (h : ℤ) * j) = a + b * j := by
        intro j
        dsimp [a, b]
        ring
      simp_rw [hrow]
      rw [twice_sum_linear]
      push_cast
      dsimp [a, b]
      ring

private def worstBase (s : Shape) : ℤ := (s.m : ℤ) * 180169 - (s.B : ℤ) * 131071
open private worstSlope from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

private def surplusBase (s : Shape) : ℤ := (triangle s.U : ℤ) * widthBase s - 2 * nodeCost s
open private surplusSlope from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

end H21_2_1
end High_K1_14_2_1Arithmetic
