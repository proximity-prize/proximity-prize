import ProximityPrize.SubmissionLower.PartG006


section Compact_ClosedRank
/-! Symbolic rank arithmetic for large first-jet interpolation profiles.
The purpose is to replace long finite evaluations by polynomial identities. -/
namespace ProximityPrize.SubmissionLower.ClosedRank
open scoped BigOperators
open LocatorFastKernelArithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem rectangularCount_twice (a b h L : ℕ)
    (hb : h + (a - 1) + (b - 1) ≤ L) :
    2 * (rectangularCount a b h L : ℤ) =
      (a : ℤ) * b * (2 * (L + 1 - (h : ℤ)) - a - b + 2) := by
  by_cases ha : a = 0
  · simp [ha, rectangularCount]
  by_cases hzero : b = 0
  · simp [hzero, rectangularCount]
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have htA : a * (a - 1) / 2 * 2 = a * (a - 1) :=
    Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one a)
  have htB : b * (b - 1) / 2 * 2 = b * (b - 1) :=
    Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one b)
  have hmass : b * (a * (a - 1) / 2) + a * (b * (b - 1) / 2) ≤
      a * b * (L + 1 - h) := by
    have hx := Nat.mul_le_mul_left (a * b)
      (show (a - 1) + (b - 1) ≤ 2 * (L + 1 - h) by omega)
    have hi := congrArg (fun x => b*x) htA
    have hj := congrArg (fun x => a*x) htB
    nlinarith only [hx, hi, hj]
  have htAi : (a * (a - 1) / 2 : ℕ) * (2 : ℤ) = (a : ℤ) * (a - 1) := by
    exact_mod_cast htA
  have htBi : (b * (b - 1) / 2 : ℕ) * (2 : ℤ) = (b : ℤ) * (b - 1) := by
    exact_mod_cast htB
  unfold rectangularCount
  simp only [Nat.cast_sub hmass, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (show h ≤ L + 1 by omega), Nat.cast_one]
  nlinarith only [congrArg (fun x : ℤ => b*x) htAi, congrArg (fun x : ℤ => a*x) htBi]

theorem rectangularCount_shift_le (a b h L : ℕ)
    (hb : (a - 1) + (b - 1) ≤ L) :
    rectangularCount (a-h) (b-h) h L ≤ rectangularCount a b 0 L := by
  by_cases ha : a ≤ h
  · simp [Nat.sub_eq_zero_of_le ha, rectangularCount]
  by_cases hb' : b ≤ h
  · simp [Nat.sub_eq_zero_of_le hb', rectangularCount]
  have hshape : h + (a-h-1) + (b-h-1) ≤ L := by omega
  rw [← rectangularSum_eq_rectangularCount _ _ _ _ hshape,
    ← rectangularSum_eq_rectangularCount a b 0 L (by omega)]
  calc
    _ ≤ ∑ i ∈ Finset.range (a-h), ∑ j ∈ Finset.range (b-h), (L+1-0-i-j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      omega
    _ ≤ ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, (L+1-0-i-j) := by
      apply le_trans (Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le b h))
          (fun _ _ _ => Nat.zero_le _)))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le a h))
        (fun _ _ _ => Nat.zero_le _)

def rankRow (m L s r : ℕ) : ℕ :=
  let h := min (r+1) (m-r)
  rectangularCount (r+1) (s+1) 0 L - rectangularCount (r+1-h) (s+1-h) h L

theorem rankRow_twice (m L s r : ℕ) (hr : r < m)
    (hshape : m+s ≤ L+1) (hs : 2*s ≤ m) :
    2 * (rankRow m L s r : ℤ) =
      (r+1 : ℤ)*(s+1)*(2*L+2-r-s) -
      if r < m-s then 0 else
        (2*r+1-m : ℤ)*(s+1-m+r)*(2*L+2-r-s) := by
  let h := min (r+1) (m-r)
  have hl : r+s ≤ L := by omega
  have hle := rectangularCount_shift_le (r+1) (s+1) h L (by omega)
  have hsource := rectangularCount_twice (r+1) (s+1) 0 L (by omega)
  have hsource' : 2 * (rectangularCount (r+1) (s+1) 0 L : ℤ) =
      (r+1 : ℤ)*(s+1)*(2*L+2-r-s) := by
    push_cast at hsource
    nlinarith only [hsource]
  unfold rankRow
  change 2 * ((rectangularCount (r+1) (s+1) 0 L -
    rectangularCount (r+1-h) (s+1-h) h L : ℕ) : ℤ) = _
  rw [Nat.cast_sub hle, mul_sub, hsource']
  by_cases hearly : r < m-s
  · rw [if_pos hearly]
    have hzero : r+1-h = 0 ∨ s+1-h = 0 := by
      dsimp [h]
      omega
    rcases hzero with hzero | hzero <;> simp [hzero, rectangularCount]
  · rw [if_neg hearly]
    have heqh : h = m-r := by dsimp [h]; omega
    have hhr : h ≤ r+1 := by omega
    have hhs : h ≤ s+1 := by omega
    have hkernel := rectangularCount_twice (r+1-h) (s+1-h) h L (by omega)
    simp only [Nat.cast_sub hhr, Nat.cast_sub hhs, Nat.cast_add, Nat.cast_one] at hkernel
    have hhcast : (h : ℤ) = m-r := by rw [heqh, Nat.cast_sub (by omega : r ≤ m)]
    rw [hhcast] at hkernel
    nlinarith only [hkernel]

def sourceTwice (L s r : ℤ) : ℤ := (r+1)*(s+1)*(2*L+2-r-s)
def removedTwice (m L s j : ℤ) : ℤ := (m+1-2*j)*(s+1-j)*(2*L+2-m-s+j)

def sourceTwelve (m L s : ℤ) : ℤ :=
  (s+1)*m*(m+1)*(6*(L+1)-2*(m-1)-3*s)

def removedPartialTwelve (m L s k : ℤ) : ℤ :=
  let c := 2*L+2-m-s
  let p0 := (m+1)*(s+1)
  let p1 := -(m+2*s+3)
  6*p0*c*k + 3*(p0+p1*c)*k*(k+1) +
    (p1+2*c)*k*(k+1)*(2*k+1) + 3*k*k*(k+1)*(k+1)

theorem sum_sourceTwice (m : ℕ) (L s : ℤ) :
    6 * (∑ r ∈ Finset.range m, sourceTwice L s r) = sourceTwelve m L s := by
  induction m with
  | zero => simp [sourceTwelve]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    unfold sourceTwice sourceTwelve
    ring

theorem sum_removedTwice (k : ℕ) (m L s : ℤ) :
    6 * (∑ j ∈ Finset.range k, removedTwice m L s (j+1)) =
      removedPartialTwelve m L s k := by
  induction k with
  | zero => simp [removedPartialTwelve]
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    unfold removedTwice removedPartialTwelve
    ring

theorem sum_removed_rows (m L s : ℕ) (hs : s ≤ m) :
    (∑ r ∈ Finset.range m, if r < m-s then (0 : ℤ) else
      removedTwice m L s ((m : ℤ)-r)) =
      ∑ j ∈ Finset.range s, removedTwice m L s (j+1) := by
  let f : ℕ → ℤ := fun r => if r < m-s then 0 else removedTwice m L s ((m : ℤ)-r)
  change (∑ r ∈ Finset.range m, f r) = _
  have hsplit := Finset.sum_range_add f (m-s) s
  rw [Nat.sub_add_cancel hs] at hsplit
  rw [hsplit]
  have hzero : (∑ r ∈ Finset.range (m-s), f r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [f, Finset.mem_range.mp hr]
  rw [hzero, zero_add]
  calc
    _ = ∑ j ∈ Finset.range s, f (m-s+(s-1-j)) :=
      (Finset.sum_range_reflect (fun r => f (m-s+r)) s).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hlate : ¬ m-s+(s-1-j) < m-s := by omega
      have hindex : (m : ℤ) - (m-s+(s-1-j) : ℕ) = (j : ℤ)+1 := by
        have heq : m-s+(s-1-j)+j+1 = m := by omega
        have heqi : ((m-s+(s-1-j) : ℕ) : ℤ) + j + 1 = m := by exact_mod_cast heq
        omega
      simp only [f, if_neg hlate, hindex]

theorem fastLocalRankBound_twelve (m L s : ℕ)
    (hshape : m+s ≤ L+1) (hs : 2*s ≤ m) :
    12 * (fastLocalRankBound m L s : ℤ) =
      sourceTwelve m L s - removedPartialTwelve m L s s := by
  have hfast : fastLocalRankBound m L s = ∑ r ∈ Finset.range m, rankRow m L s r := by
    unfold fastLocalRankBound
    rw [LocatorLowQuotient.kernelSumRange_eq]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hmin : min r L = r := min_eq_left (by omega)
    simp only [hmin, rankRow]
  have hrow (r : ℕ) (hr : r ∈ Finset.range m) :
      2*(rankRow m L s r : ℤ) = sourceTwice L s r -
        (if r < m-s then 0 else removedTwice m L s ((m : ℤ)-r)) := by
    rw [rankRow_twice m L s r (Finset.mem_range.mp hr) hshape hs]
    split_ifs <;> simp only [sourceTwice, removedTwice] <;> ring
  have hsum : 2*(fastLocalRankBound m L s : ℤ) =
      (∑ r ∈ Finset.range m, sourceTwice L s r) -
        ∑ j ∈ Finset.range s, removedTwice m L s (j+1) := by
    rw [hfast, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib,
      sum_removed_rows m L s (by omega)]
  have hscaled := congrArg (fun z : ℤ => 6*z) hsum
  rw [mul_sub, sum_sourceTwice, sum_removedTwice] at hscaled
  nlinarith only [hscaled]

def closedLocalRankBound (m L s : ℕ) : ℕ :=
  ((sourceTwelve m L s - removedPartialTwelve m L s s) / 12).toNat

theorem fastLocalRankBound_eq_closed (m L s : ℕ)
    (hshape : m+s ≤ L+1) (hs : 2*s ≤ m) :
    fastLocalRankBound m L s = closedLocalRankBound m L s := by
  unfold closedLocalRankBound
  rw [← fastLocalRankBound_twelve m L s hshape hs]
  simp

theorem localRankBound_eq_closed (m L s : ℕ)
    (hshape : m+s ≤ L+1) (hs : 2*s ≤ m) :
    RCN119.localRankBound m L s = closedLocalRankBound m L s := by
  rw [localRankBound_eq_fastLocalRankBound m L s hshape,
    fastLocalRankBound_eq_closed m L s hshape hs]

end ProximityPrize.SubmissionLower.ClosedRank

end Compact_ClosedRank
