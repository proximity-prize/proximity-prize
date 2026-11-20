import ProximityPrize.SubmissionLower.Koala6844ReceiptsCubicSum

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def firstJetAffineRow (cut u : Nat) (constant : Bool) (j : Nat) : Int :=
  let first := chooseTwo (u+1)-chooseTwo j
  let second := squares (u+1)-squares j
  let count := ((u-j+1) : Int)*(cut+j : Nat)-(degree : Int)*first
  let moment := (cut+j : Nat)*(first : Int)-(degree : Int)*second
  if constant then count-moment else count

theorem chooseTwo_eq_sum_range (n : Nat) : chooseTwo n = ∑ i ∈ Finset.range n, i :=
  (Finset.sum_range_id n).symm

theorem squares_eq_sum_range (n : Nat) : squares n = ∑ i ∈ Finset.range n, i^2 := by
  unfold squares
  rw [← SecondJetGlobalCounts.sum_range_square_mul_six]
  exact Nat.mul_div_cancel _ (by decide : 0 < 6)

private theorem chooseTwo_scaled (n : Nat) :
    6*(chooseTwo n : Int) = 3*(n : Int)*((n : Int)-1) := by
  rw [chooseTwo_eq_sum_range]
  cases n with
  | zero => simp
  | succ n =>
    have h := congrArg Int.ofNat (Finset.sum_range_id_mul_two (n+1))
    change (((∑ i ∈ Finset.range (n+1), i)*2 : Nat) : Int) = (((n+1)*n : Nat) : Int) at h
    push_cast [Nat.add_sub_cancel] at h ⊢
    linear_combination 3*h

private theorem squares_scaled (n : Nat) :
    6*(squares n : Int) = (n : Int)*((n : Int)-1)*(2*(n : Int)-1) := by
  rw [squares_eq_sum_range]
  cases n with
  | zero => simp
  | succ n =>
    have h := congrArg Int.ofNat (SecondJetGlobalCounts.sum_range_square_mul_six (n+1))
    have hpos : 1 ≤ 2*(n+1) := by omega
    change (((∑ i ∈ Finset.range (n+1), i^2)*6 : Nat) : Int) =
      (((n+1)*n*(2*(n+1)-1) : Nat) : Int) at h
    push_cast [Nat.add_sub_cancel, Nat.cast_sub hpos] at h ⊢
    linear_combination h

private theorem affineRow_cubic (cut u : Nat) (constant : Bool) :
    ∃ a b c d : Int, ∀ j ≤ u, 6*firstJetAffineRow cut u constant j =
      a+b*j+c*(j : Int)^2+d*(j : Int)^3 := by
  let a := (u : Int)+1
  let w := (degree : Int)
  let D := (cut : Int)
  let C₂ := 6*(chooseTwo (u+1) : Int)
  let C₃ := 6*(squares (u+1) : Int)
  let v : Int := if constant then 1 else 0
  refine ⟨6*a*D-w*C₂-v*(D*C₂-w*C₃),
    6*(a-D)-3*w-v*(C₂+3*D+w),
    3*w-6-v*(3-3*D-3*w), -v*(2*w-3),?_⟩
  intro j hj
  have hj' : j ≤ u+1 := by omega
  have htwo : chooseTwo j ≤ chooseTwo (u+1) := by
    simp only [chooseTwo_eq_sum_range]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hj')
  have hthree : squares j ≤ squares (u+1) := by
    simp only [squares_eq_sum_range]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hj')
  have hC₂ : 6*((chooseTwo (u+1)-chooseTwo j : Nat) : Int) = C₂-3*(j : Int)*((j : Int)-1) := by
    rw [Nat.cast_sub htwo,mul_sub,chooseTwo_scaled j]
  have hC₃ : 6*((squares (u+1)-squares j : Nat) : Int) = C₃-(j : Int)*((j : Int)-1)*(2*(j : Int)-1) := by
    rw [Nat.cast_sub hthree,mul_sub,squares_scaled j]
  unfold firstJetAffineRow
  cases constant <;> simp [v]
  · push_cast [Nat.cast_sub hj]
    dsimp only [a,D,w]
    linear_combination -(degree : Int)*hC₂
  · push_cast [Nat.cast_sub hj]
    dsimp only [a,D,w]
    linear_combination (-(degree : Int)-(cut : Int)-j)*hC₂ + (degree : Int)*hC₃

private theorem affineRow_cubic_shift (cut u : Nat) (constant : Bool) (low high : Nat)
    (h : ∀ i < high-low, low+i ≤ u) :
    ∃ a b c d : Int, ∀ i < high-low, 6*firstJetAffineRow cut u constant (low+i) =
      a+b*i+c*(i : Int)^2+d*(i : Int)^3 := by
  obtain ⟨a,b,c,d,hp⟩ := affineRow_cubic cut u constant
  refine ⟨a+b*low+c*(low : Int)^2+d*(low : Int)^3,
    b+2*c*low+3*d*(low : Int)^2,c+3*d*low,d,?_⟩
  intro i hi
  rw [hp _ (h i hi)]
  push_cast
  ring

theorem firstJetAffineColumns_eq_interval_sum (cut slope : Nat) (constant : Bool) (hcut : cut ≠ 0) :
    let cap := (cut-1)/degree
    let turn := degree-(cut-1)%degree
    let begin := min turn (min (slope+1) (cap+1))
    let finish := min slope (cap+1)+1
    firstJetAffineColumns cut slope constant =
      (∑ i ∈ Finset.range begin, firstJetAffineRow cut cap constant i) +
      (∑ i ∈ Finset.range (finish-turn), firstJetAffineRow cut (cap+1) constant (turn+i)) := by
  dsimp only
  unfold firstJetAffineColumns
  rw [ite_eq_right hcut]
  let cap := (cut-1)/degree
  let turn := degree-(cut-1)%degree
  let begin := min turn (min (slope+1) (cap+1))
  let finish := min slope (cap+1)+1
  change cubicIntervalSum (firstJetAffineRow cut cap constant) 0 begin +
      cubicIntervalSum (firstJetAffineRow cut (cap+1) constant) turn finish = _
  have h₀ := cubicIntervalSum_eq_sum (firstJetAffineRow cut cap constant) 0 begin 6 (by decide)
    (affineRow_cubic_shift cut cap constant 0 begin (by
      intro i hi
      have hb : begin ≤ cap+1 := (min_le_right _ _).trans (min_le_right _ _)
      omega))
  have h₁ := cubicIntervalSum_eq_sum (firstJetAffineRow cut (cap+1) constant) turn finish 6 (by decide)
    (affineRow_cubic_shift cut (cap+1) constant turn finish (by
      intro i hi
      have hf : finish ≤ cap+2 := Nat.add_le_add_right (min_le_right _ _) 1
      omega))
  rw [h₀,h₁]
  simp only [Nat.sub_zero,Nat.zero_add]
  rfl


theorem firstJetAffineRow_eq_sum (cut u r : Nat) (constant : Bool) (hr : r ≤ u) :
    firstJetAffineRow cut u constant r =
      ∑ y ∈ Finset.range (u+1-r), (((cut : Int)+r-(degree : Int)*((r : Int)+y)) *
        (if constant then 1-((r : Int)+y) else 1)) := by
  let len := u+1-r
  have hlen : r+len=u+1 := by dsimp only [len]; omega
  have hfirst : chooseTwo (u+1)-chooseTwo r = ∑ y ∈ Finset.range len, (r+y) := by
    rw [chooseTwo_eq_sum_range,chooseTwo_eq_sum_range,← hlen,Finset.sum_range_add]
    exact Nat.add_sub_cancel_left _ _
  have hsecond : squares (u+1)-squares r = ∑ y ∈ Finset.range len, (r+y)^2 := by
    rw [squares_eq_sum_range,squares_eq_sum_range,← hlen,Finset.sum_range_add]
    exact Nat.add_sub_cancel_left _ _
  let coeff := fun y : Nat => (cut : Int)+r-(degree : Int)*((r : Int)+y)
  have hcount : ((u-r+1) : Int)*(cut+r : Nat) - (degree : Int)*(chooseTwo (u+1)-chooseTwo r : Nat) =
      ∑ y ∈ Finset.range len, coeff y := by
    unfold coeff
    rw [hfirst]
    push_cast [Nat.cast_sub hr]
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,← Finset.mul_sum]
    have hlen' : (len : Int) = (u : Int)-r+1 := by
      dsimp only [len]
      rw [Nat.cast_sub (by omega : r ≤ u+1)]
      push_cast
      ring
    rw [hlen']
  have hmoment : (cut+r : Nat)*((chooseTwo (u+1)-chooseTwo r : Nat) : Int) -
      (degree : Int)*(squares (u+1)-squares r : Nat) =
      ∑ y ∈ Finset.range len, (coeff y*((r : Int)+y)) := by
    rw [hfirst,hsecond]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    unfold coeff
    ring
  unfold firstJetAffineRow
  change (if constant then _ else _) = ∑ y ∈ Finset.range len, coeff y * (if constant then _ else _)
  rw [hcount,hmoment]
  cases constant <;> simp only [Bool.false_eq_true, ite_false, mul_one, ite_true]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

end ProximityPrize.SubmissionLower.Koala6844Receipts
