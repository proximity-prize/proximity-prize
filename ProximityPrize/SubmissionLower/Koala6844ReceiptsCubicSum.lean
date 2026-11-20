import ProximityPrize.SubmissionLower.Koala6844ReceiptsSchedule
import ProximityPrize.SubmissionLower.Koala6844ReceiptsBridge
import Mathlib.Data.Nat.Factorial.Cast

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

private theorem chooseTwo_eq_binom (n : Nat) : chooseTwo n = n.choose 2 :=
  (Nat.choose_two_right n).symm

private theorem chooseThree_eq_binom (n : Nat) : chooseThree n = n.choose 3 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp only [chooseThree, show 3=2+1 by decide, Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.factorial_succ, Nat.factorial_zero]
  simp only [Nat.sub_zero, Nat.mul_one]
  norm_num
  ac_rfl

private theorem chooseFour_eq_binom (n : Nat) : chooseFour n = n.choose 4 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp only [chooseFour, show 4=3+1 by decide, show 3=2+1 by decide, Nat.descFactorial_succ,
    Nat.descFactorial_zero, Nat.factorial_succ, Nat.factorial_zero]
  simp only [Nat.sub_zero, Nat.mul_one]
  norm_num
  ac_rfl

private theorem binomTwo_int (n : Nat) : 2*(n.choose 2 : Int) = (n : Int)*((n : Int)-1) := by
  have h := Nat.cast_descFactorial_two (S := Int) (a := n)
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  simpa only [Nat.cast_mul, Nat.factorial_two, Nat.cast_ofNat] using h

private theorem binomThree_int (n : Nat) :
    6*(n.choose 3 : Int) = (n : Int)*((n : Int)-1)*((n : Int)-2) := by
  by_cases hn : 2 ≤ n
  · have h : (n.descFactorial 3 : Int) = 6*(n.choose 3 : Int) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      norm_num [Nat.factorial]
    rw [← h, show 3 = 2+1 by decide, Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_sub hn, Nat.cast_descFactorial_two]
    push_cast
    ring
  · interval_cases n <;> decide +kernel

private theorem hockeyStick_int (n k : Nat) :
    (∑ i ∈ Finset.range n, (i.choose k : Int)) = (n.choose (k+1) : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,Nat.choose_succ_succ',Nat.cast_add,add_comm]

private theorem cubic_point (f : Nat → Int) (low n scale : Nat) (hs : 0 < scale) (hn : 4 ≤ n)
    (a b c d : Int)
    (hp : ∀ i < n, (scale : Int)*f (low+i) = a+b*i+c*(i : Int)^2+d*(i : Int)^3)
    (i : Nat) (hi : i < n) :
    f (low+i) = f low+(i : Int)*(f (low+1)-f low)+
      (i.choose 2 : Int)*(f (low+2)-2*f (low+1)+f low)+
      (i.choose 3 : Int)*(f (low+3)-3*f (low+2)+3*f (low+1)-f low) := by
  have h0 := hp 0 (by omega)
  have h1 := hp 1 (by omega)
  have h2 := hp 2 (by omega)
  have h3 := hp 3 (by omega)
  norm_num at h0 h1 h2 h3
  have hd1 : (scale : Int)*(f (low+1)-f low) = b+c+d := by
    linear_combination h1-h0
  have hd2 : (scale : Int)*(f (low+2)-2*f (low+1)+f low) = 2*c+6*d := by
    linear_combination h2-2*h1+h0
  have hd3 : (scale : Int)*(f (low+3)-3*f (low+2)+3*f (low+1)-f low) = 6*d := by
    linear_combination h3-3*h2+3*h1-h0
  apply mul_left_cancel₀ (show (6 : Int)*(scale : Int) ≠ 0 by positivity)
  calc
    _ = 6*(a+b*i+c*(i : Int)^2+d*(i : Int)^3) := by rw [mul_assoc,hp i hi]
    _ = 6*a+6*i*(b+c+d)+3*(i : Int)*((i : Int)-1)*(2*c+6*d)+
          (i : Int)*((i : Int)-1)*((i : Int)-2)*(6*d) := by ring
    _ = _ := by
      rw [← binomThree_int, mul_assoc (3 : Int) (i : Int) ((i : Int)-1), ← binomTwo_int]
      rw [← h0,← hd1,← hd2,← hd3]
      ring

theorem cubicIntervalSum_eq_sum (f : Nat → Int) (low high scale : Nat) (hs : 0 < scale)
    (hc : ∃ a b c d : Int, ∀ i < high-low,
      (scale : Int)*f (low+i) = a+b*i+c*(i : Int)^2+d*(i : Int)^3) :
    cubicIntervalSum f low high = ∑ i ∈ Finset.range (high-low), f (low+i) := by
  unfold cubicIntervalSum
  generalize hlen : high-low = n at hc ⊢
  dsimp only
  rcases hc with ⟨a,b,c,d,hc⟩
  by_cases hn : 4 ≤ n
  · have hn₀ : n ≠ 0 := by omega
    have hn₂ : 2 ≤ n := by omega
    have hn₃ : 3 ≤ n := by omega
    simp only [ite_eq_right hn₀, ite_eq_left hn₂, ite_eq_left hn₃, ite_eq_left hn,
      chooseTwo_eq_binom,chooseThree_eq_binom,chooseFour_eq_binom]
    have hsum : (∑ i ∈ Finset.range n, f (low+i)) = ∑ i ∈ Finset.range n,
        (f low+(i : Int)*(f (low+1)-f low)+
          (i.choose 2 : Int)*(f (low+2)-2*f (low+1)+f low)+
          (i.choose 3 : Int)*(f (low+3)-3*f (low+2)+3*f (low+1)-f low)) :=
      Finset.sum_congr rfl (fun i hi => cubic_point f low n scale hs hn a b c d hc i
        (Finset.mem_range.mp hi))
    rw [hsum]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_mul]
    rw [hockeyStick_int n 2, hockeyStick_int n 3]
    have hlin : (∑ i ∈ Finset.range n, (i : Int)) = (n.choose 2 : Int) := by
      simpa only [Nat.choose_one_right] using hockeyStick_int n 1
    rw [hlin]
  · have he : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases he with h | h | h | h <;> rw [h]
    · simp
    · norm_num [Finset.sum_range_succ,chooseTwo,chooseThree,chooseFour]
    · norm_num [Finset.sum_range_succ,chooseTwo,chooseThree,chooseFour] <;> ring
    · norm_num [Finset.sum_range_succ,chooseTwo,chooseThree,chooseFour] <;> ring

end ProximityPrize.SubmissionLower.Koala6844Receipts
