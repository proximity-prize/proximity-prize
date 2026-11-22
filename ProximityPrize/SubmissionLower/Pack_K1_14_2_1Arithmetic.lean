import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Numeric6AuxCert
set_option autoImplicit true
section
namespace K1_14_2_1
open K1 K1_14 K1_14_2 Finset
private theorem twice_sum_linear (a b : ℤ) (n : ℕ) :
    2 * (∑ j ∈ range n, (a + b * (j : ℤ))) =
      n * (2 * a + b * ((n : ℤ) - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring
private def nodeRow (k d : ℕ) : ℕ :=
  let n := min k ((d + 1) / 2)
  n * (d + 1 - n)
private theorem nodeRow_eq (k d : ℕ) :
    (∑ i ∈ range k, (d - 2 * i)) = nodeRow k d := by
  let n := min k ((d + 1) / 2)
  have hnk : n ≤ k := Nat.min_le_left _ _
  have hnd : n ≤ (d + 1) / 2 := Nat.min_le_right _ _
  have htrim : (∑ i ∈ range k, (d - 2 * i)) = ∑ i ∈ range n, (d - 2 * i) := by
    symm
    apply sum_subset (range_mono hnk)
    intro i hik hi
    have hik' := mem_range.mp hik
    have hi' : n ≤ i := Nat.le_of_not_gt (fun h => hi (mem_range.mpr h))
    dsimp [n] at hi'
    omega
  have hcast : ((∑ i ∈ range n, (d - 2 * i) : ℕ) : ℤ) =
      ∑ i ∈ range n, ((d : ℤ) - 2 * (i : ℤ)) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro i hi
    have hil := mem_range.mp hi
    rw [Nat.cast_sub (by omega : 2 * i ≤ d)]
    push_cast
    rfl
  have hlin := twice_sum_linear (d : ℤ) (-2) n
  simp only [neg_mul, ← sub_eq_add_neg] at hlin
  apply Int.ofNat_inj.mp
  rw [htrim, hcast]
  change _ = (↑(n * (d + 1 - n)) : ℤ)
  push_cast [Nat.cast_sub (show n ≤ d + 1 by omega)]
  nlinarith only [hlin]
private def nodeCost (s : Shape) : ℕ :=
  triangle s.U * 262144 *
    ∑ q ∈ range (s.B + 1), nodeRow (min q s.J + 1) (s.m + min q s.J - q)
private def poleSlope (s : Shape) : ℕ :=
  2 * (s.U + 1) * ∑ q ∈ range (s.B + 1), (min q s.J + 1) * ((s.B + s.J - q) * (s.B - q))
private theorem debit_eq (s : Shape) (h : ℕ) : sourceDebit h s = nodeCost s + h * poleSlope s := by
  unfold sourceDebit nodeCost poleSlope shapeSum
  simp_rw [← Nat.sub_sub, nodeRow_eq, sum_const, card_range, Nat.nsmul_eq_mul]
  ring
private def widthBase (s : Shape) : ℤ :=
  ∑ q ∈ range (s.B + 1), (((min q s.J : ℕ) : ℤ) + 1) *
    (2 * ((s.m : ℤ) * 180265 - (q : ℤ) * 131071) + min q s.J)
private def widthSlope (s : Shape) (r mode : ℕ) : ℤ :=
  ∑ q ∈ range (s.B + 1), (((min q s.J : ℕ) : ℤ) + 1) *
    (2 * ((q : ℤ) - 2 * r) - 2 * mode * min q s.J)
private theorem width_cast (h r : ℕ) (s : Shape) (q j : ℕ)
    (hh : h ≤ 131071) (hq : q ≤ s.B)
    (hw : s.B * (131071 - h) < cutoffCount h r s) :
    (rawWidth h r s q j : ℤ) =
      (s.m : ℤ) * 180265 - 2 * (h : ℤ) * r + j - (q : ℤ) * (131071 - h) := by
  have hq' := (Nat.mul_le_mul_right (131071 - h) hq).trans hw.le
  have hbuf : 2 * h * r ≤ s.m * 180265 := by unfold cutoffCount at hw; omega
  unfold rawWidth cutoffCount at *
  rw [Nat.cast_sub (by omega : q * (131071 - h) ≤ s.m * 180265 - 2 * h * r + j)]
  push_cast [Nat.cast_sub hh, Nat.cast_sub hbuf]
  rfl
private theorem volume_eq (h r mode : ℕ) (s : Shape) (hh : h ≤ 131071)
    (hw : s.B * (131071 - h) < cutoffCount h r s) :
    2 * ((rawVolume h r s : ℤ) - mode * (movingCeiling h s : ℤ)) =
      (triangle s.U : ℤ) * (widthBase s + h * widthSlope s r mode) := by
  calc
    _ = (triangle s.U : ℤ) * ∑ q ∈ range (s.B + 1),2 *
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
      let a : ℤ := (s.m : ℤ) * 180265 - 2 * (h : ℤ) * r - (q : ℤ) * (131071 - h)
      let b : ℤ := 1 - 2 * (h : ℤ) * mode
      have hrow : ∀ j : ℕ,
          (s.m : ℤ) * 180265 - 2 * (h : ℤ) * r + j - (q : ℤ) * (131071 - h) -
            mode * (2 * (h : ℤ) * j) = a + b * j := by
        intro j
        dsimp [a, b]
        ring
      simp_rw [hrow]
      rw [twice_sum_linear]
      push_cast
      dsimp [a, b]
      ring
private def worstBase (s : Shape) : ℤ := (s.m : ℤ) * 180265 - (s.B : ℤ) * 131071
private def worstSlope (s : Shape) (r : ℕ) : ℤ := (s.B : ℤ) - 2 * r
private def surplusBase (s : Shape) : ℤ := (triangle s.U : ℤ) * widthBase s - 2 * nodeCost s
private def surplusSlope (s : Shape) (r mode : ℕ) : ℤ :=
  (triangle s.U : ℤ) * widthSlope s r mode - 2 * poleSlope s
private def Certificate (s : Shape) (r mode : ℕ) : Prop :=
  0 < worstBase s + 2601 * worstSlope s r ∧
  0 < worstBase s + 3554 * worstSlope s r ∧
  0 < surplusBase s + 2601 * surplusSlope s r mode ∧
  0 < surplusBase s + 3554 * surplusSlope s r mode
private def GoodStage (s : Stage) : Prop :=
  Certificate s.cheap s.reserve 0 ∧ Certificate s.layered s.reserve 1 ∧ s.cheap.U < p
private instance (s : Stage) : Decidable (GoodStage s) := by
  unfold GoodStage Certificate
  infer_instance
section
set_option maxHeartbeats 0
set_option maxRecDepth 16000
end
end K1_14_2_1
end
