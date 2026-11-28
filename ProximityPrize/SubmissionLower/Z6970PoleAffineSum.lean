import ProximityPrize.SubmissionLower.KoalaRectPoleBalance
import ProximityPrize.SubmissionLower.Z6970PolePrices

set_option autoImplicit false

namespace PoleAffine6970
open Finset

private theorem cubic_step {N n : ℕ} (hn : n ≤ N) :
    cubicSum N (n+1) = cubicSum N n + (N-n)*tri n := by
  simp only [cubicSum, tri, ← Nat.choose_eq_fast_choose]
  rw [show N+1-(n+1) = N-n by omega, show N+1-n = (N-n)+1 by omega,
    Nat.choose_succ_succ (n+1) 2, Nat.choose_succ_succ (n+1) 3]
  ring

theorem cubic_sum (N n : ℕ) (hn : n ≤ N+1) :
    (∑ k ∈ range n, (N-k)*tri k) = cubicSum N n := by
  induction n with
  | zero =>
    rw [sum_range_zero]
    change 0 = (N+1-0)*0+0
    simp
  | succ n ih => rw [sum_range_succ, ih (by omega), cubic_step (by omega)]

theorem charge_sum (N H n : ℕ) (hn : n ≤ N+1) :
    (∑ k ∈ range n, charge N H k) = chargePrefix N H n := by
  have shifted : (∑ k ∈ range n, (N-k)*tri (k-H)) = cubicSum (N-H) (n-H) := by
    rw [P1_7_1_3.sum_after (fun k => (N-k)*tri (k-H)) n H (by
      intro q hq
      simp [Nat.sub_eq_zero_of_le hq.le, tri])]
    simpa only [Nat.add_sub_cancel_left, Nat.sub_add_eq] using cubic_sum (N-H) (n-H) (by omega)
  have sum : (∑ k ∈ range n, charge N H k) + (∑ k ∈ range n, (N-k)*tri (k-H)) =
      ∑ k ∈ range n, (N-k)*tri k := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    unfold charge
    have hle : tri (k-H) ≤ tri k := Nat.choose_le_choose 2 (by omega : k-H+1 ≤ k+1)
    rw [← Nat.mul_add, Nat.sub_add_cancel hle]
  rw [shifted, cubic_sum N n hn] at sum
  unfold chargePrefix
  omega

theorem span_sum (N H start n : ℕ) (hn : start+n ≤ N+1) :
    (∑ i ∈ range n, charge N H (start+i)) = chargePrefix N H (start+n) - chargePrefix N H start := by
  have sum := sum_range_add (charge N H) start n
  rw [charge_sum _ _ _ hn, charge_sum _ _ _ (by omega)] at sum
  omega

end PoleAffine6970
