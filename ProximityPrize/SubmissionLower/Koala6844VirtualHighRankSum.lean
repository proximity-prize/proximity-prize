import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators

theorem sum_virtual_blocks (l : ℕ) (hl : 0 < l) (m : ℕ) (f : ℕ → ℤ) :
    (∑ i ∈ Finset.range (l*m), f (i/l)) = (l : ℤ) * ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    calc
      _ = ∑ _i ∈ Finset.range l, f m := by
        apply Finset.sum_congr rfl
        intro i hi
        have hdiv : (l*m+i)/l = m := by
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl,
            Nat.div_eq_of_lt (Finset.mem_range.mp hi), zero_add]
        rw [hdiv]
      _ = _ := by simp [Finset.sum_const]

def lostMonomials (y b : ℤ) (k : ℕ) : ℤ :=
  (k : ℤ) * (y+b+2-k)

private theorem sum_ascending_lostMonomials (y b : ℤ) (m : ℕ) :
    6 * (∑ j ∈ Finset.range m, lostMonomials y b (j+1)) =
      (m : ℤ) * (m+1) * (3*(y+b+1)-2*((m : ℤ)-1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Nat.cast_succ]
    simp only [lostMonomials, Nat.cast_add, Nat.cast_one]
    ring

private theorem sum_descending_lostMonomials (y b : ℤ) (m : ℕ) :
    (∑ j ∈ Finset.range m, lostMonomials y b (m-j)) =
      ∑ j ∈ Finset.range m, lostMonomials y b (j+1) := by
  rw [← Finset.sum_range_reflect (fun j => lostMonomials y b (j+1)) m]
  apply Finset.sum_congr rfl
  intro j hj
  have h : m - j = m - 1 - j + 1 := by
    have hlt := Finset.mem_range.mp hj
    omega
  rw [h]

theorem sharp_rank_sum (l : ℕ) (hl : 0 < l) (m : ℕ) (y b : ℤ) :
    6 * (∑ i ∈ Finset.range (l*m), (b+1) * lostMonomials y b (m-i/l)) =
      (l : ℤ) * (b+1) * m * (m+1) * (3*(y+b+1)-2*((m : ℤ)-1)) := by
  rw [sum_virtual_blocks l hl m (fun i => (b+1) * lostMonomials y b (m-i)), ← Finset.mul_sum,
    sum_descending_lostMonomials]
  calc
    _ = (l : ℤ) * (b+1) * (6 * ∑ j ∈ Finset.range m, lostMonomials y b (j+1)) := by ring
    _ = _ := by rw [sum_ascending_lostMonomials]; ring

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
