import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.Koala6844ReceiptsSchedule

open scoped BigOperators

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false
set_option maxHeartbeats 4000000

open LocatorLowQuotient LocatorArbitraryPowerAvoidance

private theorem chooseThree_eq (n : ℕ) : chooseThree n = n.choose 3 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp only [chooseThree, Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.mul_one, Nat.sub_zero]
  congr 1 <;> ring

private theorem sum_inc_choose (n k : ℕ) (hk : 1 ≤ k) :
    (∑ j ∈ Finset.range n, (j+1).choose k) = (n+1).choose (k+1) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.zero_add]
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [Nat.add_comm ((n+1).choose (k+1))]
    exact (Nat.choose_succ_succ' (n+1) k).symm

private theorem twice_chooseTwo (k : ℕ) : (k+1)*k = chooseTwo (k+1)*2 := by
  have h := Nat.add_one_mul_choose_eq k 1
  rw [Nat.choose_one_right] at h
  change (k+1)*k = (k+1).choose 2*2 at h
  simpa only [chooseTwo, Nat.choose_two_right] using h

private def channelCell (T YS S y : ℕ) : ℕ :=
  let R := min S (min (T-y) (YS-y))
  (R+1)*(T+1-y)-chooseTwo (R+1)

private theorem early_cell (T YS S y : ℕ) (hy : y ≤ (min T YS)-min S (min T YS)) :
    channelCell T YS S y =
      (min S (min T YS)+1)*(T+1-y)-chooseTwo (min S (min T YS)+1) := by
  have hmin : min S (min (T-y) (YS-y)) = min S (min T YS) := by omega
  unfold channelCell
  rw [hmin]

private theorem late_cell (T YS S k : ℕ) (hk : k < min S (min T YS)) :
    channelCell T YS S ((min T YS)-k) =
      (k+1)*(T+1-min T YS)+chooseTwo (k+1) := by
  let M := min T YS
  have hc : min S (min (T-(M-k)) (YS-(M-k))) = k := by dsimp only [M]; omega
  have hd : T+1-(M-k) = (T+1-M)+k := by dsimp only [M]; omega
  unfold channelCell
  change (min S (min (T-(M-k)) (YS-(M-k)))+1)*(T+1-(M-k)) -
    chooseTwo (min S (min (T-(M-k)) (YS-(M-k)))+1) = (k+1)*(T+1-M)+chooseTwo (k+1)
  rw [hc, hd, Nat.mul_add, twice_chooseTwo]
  omega

theorem fastChannelCount_eq (T YS S : ℕ) : fastChannelCount T YS S = channelCount T YS S := by
  let M := min T YS
  let B := min S M
  let E := M-B
  have hBT : B ≤ M := Nat.min_le_right _ _
  have hMT : M ≤ T := Nat.min_le_left _ _
  have hET : E ≤ T+1 := by dsimp only [E]; omega
  have hEB : E+1+B = M+1 := by dsimp only [E]; omega
  have hchoose : chooseTwo (B+1) ≤ (B+1)*B := by
    unfold chooseTwo
    simpa using Nat.div_le_self ((B+1)*B) 2
  change (B+1)*((E+1)*(T+1)-chooseTwo (E+1))-(E+1)*chooseTwo (B+1) +
    (T+1-M)*chooseTwo (B+1)+chooseThree (B+1) =
    kernelSumRange (channelCell T YS S) (M+1)
  rw [kernelSumRange_eq, ← hEB, Finset.sum_range_add]
  have hEarly :
      (∑ y ∈ Finset.range (E+1), channelCell T YS S y) =
        (B+1)*((E+1)*(T+1)-chooseTwo (E+1))-(E+1)*chooseTwo (B+1) := by
    calc
      _ = ∑ y ∈ Finset.range (E+1), ((B+1)*(T+1-y)-chooseTwo (B+1)) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact early_cell T YS S y (by have h := Finset.mem_range.mp hy; change y≤E; omega)
      _ = _ := by
        rw [Finset.sum_tsub_distrib, ← Finset.mul_sum, finset_sum_range_sub _ _ hET]
        · simp [chooseTwo]
        · intro y hy
          have hY := Finset.mem_range.mp hy
          exact Nat.le_trans hchoose (Nat.mul_le_mul_left _ (by dsimp only [E] at hY; omega))
  have hLate :
      (∑ j ∈ Finset.range B, channelCell T YS S ((E+1)+j)) =
        (T+1-M)*chooseTwo (B+1)+chooseThree (B+1) := by
    calc
      _ = ∑ j ∈ Finset.range B, channelCell T YS S ((E+1)+(B-1-j)) :=
        (Finset.sum_range_reflect (fun i => channelCell T YS S ((E+1)+i)) B).symm
      _ = ∑ j ∈ Finset.range B, channelCell T YS S (M-j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have h := Finset.mem_range.mp hj
        rw [show (E+1)+(B-1-j)=M-j by dsimp only [E]; omega]
      _ = ∑ j ∈ Finset.range B, ((j+1)*(T+1-M)+chooseTwo (j+1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact late_cell T YS S j (Finset.mem_range.mp hj)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        have h2 : (∑ j ∈ Finset.range B, (j+1)) = chooseTwo (B+1) := by
          have h := sum_inc_choose B 1 (by decide)
          simp only [Nat.choose_one_right] at h
          change (∑ j ∈ Finset.range B, (j+1)) = (B+1).choose 2 at h
          simpa only [chooseTwo, Nat.choose_two_right] using h
        have h3 : (∑ j ∈ Finset.range B, chooseTwo (j+1)) = chooseThree (B+1) := by
          simpa only [chooseThree_eq, ← Nat.choose_two_right, chooseTwo] using
            sum_inc_choose B 2 (by decide)
        rw [h2, Nat.mul_comm (chooseTwo (B+1)), h3]
  rw [hEarly,hLate]
  omega

theorem fastPowerBandBudget_eq (width dt dy dr T YS R fuel : ℕ) :
    fastPowerBandBudget width dt dy dr T YS R fuel = powerBandBudget width dt dy dr T YS R fuel := by
  induction fuel generalizing T YS R with
  | zero => rfl
  | succ k ih =>
    simp only [fastPowerBandBudget,powerBandBudget,fastChannelCount_eq,ih]

end ProximityPrize.SubmissionLower.Koala6844Receipts
