import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1

set_option autoImplicit false

namespace PoleSteps6970

open Finset P1_7_1
open Research6966.HelperWindowMoments (cutOffset offset_le)

/-- The low bit records whether the next cutoff is one larger. -/
def stepMass (B J : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | n+1, t, k, steps =>
    cutOffset B J t (min B k) + stepMass B J n (t+1) (k + steps%2) (steps/2)

def interval (B J t n : ℕ) : ℕ := ∑ i ∈ range n, offsetMoment B J (t+i)

theorem step_bound (B J n t k steps : ℕ) : interval B J t n ≤ stepMass B J n t k steps := by
  induction n generalizing t k steps with
  | zero => simp [interval, stepMass]
  | succ n ih =>
    unfold interval
    rw [sum_range_succ', stepMass, Nat.add_zero, Nat.add_comm (cutOffset B J t _)]
    apply Nat.add_le_add ?_ (offset_le B J t _ (min_le_left _ _))
    simpa only [interval, Nat.add_assoc, Nat.add_comm 1] using ih (t+1) (k+steps%2) (steps/2)

theorem steps {B J n t k bits amount : ℕ} (h : stepMass B J n t k bits = amount) :
    interval B J t n ≤ amount := (step_bound ..).trans_eq h

theorem append {B J t n m v w : ℕ} (a : interval B J t n ≤ v)
    (b : interval B J (t+n) m ≤ w) : interval B J t (n+m) ≤ v+w := by
  unfold interval at *
  rw [sum_range_add]
  exact Nat.add_le_add a (by simpa only [Nat.add_assoc] using b)

theorem whole (B J total : ℕ) (h : interval B J J (B+J) ≤ total) : groupedPoleMoment B J ≤ total := by
  rw [groupedPoleMoment, show B+2*J = J+(B+J) by omega, sum_range_add]
  have early (t : ℕ) (ht : t ∈ range J) : offsetMoment B J t = 0 := by
    have ht' := mem_range.mp ht
    have same (q : ℕ) (hq : q ∈ range (B+1)) : pivotCount B J t q = columnCount B J t q := by
      have hq' := mem_range.mp hq
      unfold pivotCount
      apply min_eq_left
      dsimp [columnCount]
      omega
    unfold offsetMoment
    apply Nat.sub_eq_zero_of_le
    apply (inf'_le _ (mem_range.mpr (Nat.zero_lt_succ B))).trans
    simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_zero]
    exact le_of_eq (sum_congr rfl fun q hq => congrArg (q * ·) (same q hq).symm)
  rw [sum_eq_zero early, Nat.zero_add]
  exact h

end PoleSteps6970
