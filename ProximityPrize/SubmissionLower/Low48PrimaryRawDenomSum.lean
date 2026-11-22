import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Low48PrimaryPivot.RawClosed
open K1_13_2 Finset
open scoped BigOperators

private theorem twice_dvd (z : ℤ) : (2 : ℤ) ∣ z*(z-1) := by
  obtain h | h : z=2*(z/2) ∨ z=2*(z/2)+1 := by omega
  · exact ⟨(z/2)*(z-1), by linear_combination (z-1)*h⟩
  · exact ⟨z*(z/2), by linear_combination z*h⟩

private def cubic (q r : ℤ) := 12*q^3+(21+6*r)*q^2+(r^2+7*r+11)*q+(r^2+r+2)

private theorem double_den {u : ℤ} (hu : 0≤u) : 2*denominator u = cubic (u/6) (u%6) := by
  simp only [denominator, show ¬ u<0 by omega, ↓reduceIte]
  set q:=u/6
  set r:=u%6
  have hp : (2:ℤ) ∣ r*(r+1) := by
    convert twice_dvd (r+1) using 1 <;> ring
  unfold cubic
  linear_combination Int.ediv_mul_cancel hp + q * Int.ediv_mul_cancel (twice_dvd r) +
    (57+6*r)* Int.ediv_mul_cancel (twice_dvd q)

/-- Twenty-four times the sum of n values of the denominator polynomial for one residue. -/
private def primitive (q r d n : ℤ) : ℤ :=
  let p1 := -d*(36*q^2+2*(21+6*r)*q+(r^2+7*r+11))
  let p2 := d^2*(36*q+21+6*r)
  let p3 := -12*d^3
  12*n*cubic q r+6*n*(n-1)*p1+2*n*(n-1)*(2*n-1)*p2+3*n^2*(n-1)^2*p3

private theorem primitive_sum (q r d : ℤ) (n : ℕ) :
    primitive q r d n = 12 * ∑ i ∈ range n, cubic (q-d*(i:ℤ)) r := by
  induction n with
  | zero => simp [primitive]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ← ih, Nat.cast_succ]
    unfold primitive cubic
    ring

def denomRun (x : ℤ) (d n : ℕ) : ℤ :=
  let len := min n (x/(6*(d:ℤ))+1).toNat
  primitive (x/6) (x%6) d len / 24

private theorem run_spec (x : ℤ) (d n : ℕ) (hd : d=1 ∨ d=4) :
    denomRun x d n = ∑ i ∈ range n, denominator (x-6*(d:ℤ)*(i:ℤ)) := by
  let len := min n (x/(6*(d:ℤ))+1).toNat
  have hn : len≤n := min_le_left _ _
  have pos (i : ℕ) (hi : i<len) : 0≤x-6*(d:ℤ)*(i:ℤ) := by
    dsimp [len] at hi; rcases hd with rfl|rfl <;> norm_num at * <;> omega
  have neg (i : ℕ) (hi : i<n-len) : x-6*(d:ℤ)*(↑(len+i):ℤ)<0 := by
    dsimp [len] at *; rcases hd with rfl|rfl <;> norm_num at * <;> omega
  have core : primitive (x/6) (x%6) d len = 24 * ∑ i ∈ range len, denominator (x-6*(d:ℤ)*(i:ℤ)) := by
    rw [primitive_sum]
    have eq : ∑ i ∈ range len, cubic (x/6-(d:ℤ)*(i:ℤ)) (x%6) =
        ∑ i ∈ range len, 2*denominator (x-6*(d:ℤ)*(i:ℤ)) := by
      apply sum_congr rfl; intro i hi
      rw [double_den (pos i (mem_range.mp hi))]
      have ha : x-6*(d:ℤ)*(i:ℤ) = x+6*(-((d:ℤ)*(i:ℤ))) := by ring
      rw [ha, Int.add_mul_ediv_left _ _ (by decide), Int.add_mul_emod_self_left]; rfl
    rw [eq, ← mul_sum]; ring
  have tail : ∑ i ∈ range (n-len), denominator (x-6*(d:ℤ)*(↑(len+i):ℤ)) = 0 := by
    apply sum_eq_zero; intro i hi; rw [denominator, if_pos (neg i (mem_range.mp hi))]
  change primitive (x/6) (x%6) d len / 24 = _
  rw [core, Int.mul_ediv_cancel_left _ (by decide)]
  conv_rhs => rw [show n=len+(n-len) by omega, sum_range_add]
  rw [tail, add_zero]

theorem run1 (x : ℤ) (n : ℕ) : denomRun x 1 n = ∑ i ∈ range n, denominator (x-6*(i:ℤ)) := by
  simpa using run_spec x 1 n (Or.inl rfl)

theorem run4 (x : ℤ) (n : ℕ) : denomRun x 4 n = ∑ i ∈ range n, denominator (x-24*(i:ℤ)) := by
  simpa using run_spec x 4 n (Or.inr rfl)

end Low48PrimaryPivot.RawClosed
