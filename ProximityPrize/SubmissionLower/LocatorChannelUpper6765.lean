import ProximityPrize.SubmissionLower.LocatorLowQuotient

namespace ProximityPrize.SubmissionLower.LocatorChannelUpper6765

open scoped BigOperators
open LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def slotCount (M S : Nat) : Nat :=
  let q := min M S
  (q + 2).choose 2 + (M - q) * (q + 1)

theorem slotCount_succ (M S : Nat) :
    slotCount (M + 1) S = slotCount M S + (min S (M + 1) + 1) := by
  by_cases h : M < S
  · have hM : min M S = M := Nat.min_eq_left h.le
    have hMS : min (M + 1) S = M + 1 := Nat.min_eq_left (by omega)
    have hSM : min S (M + 1) = M + 1 := Nat.min_eq_right (by omega)
    have hchoose : (M + 3).choose 2 = (M + 2).choose 2 + (M + 2) := by
      calc
        (M + 3).choose 2 = ((M + 2) + 1).choose (1 + 1) := by congr 2 <;> omega
        _ = (M + 2).choose 1 + (M + 2).choose (1 + 1) :=
          Nat.choose_succ_succ' (M + 2) 1
        _ = (M + 2).choose 2 + (M + 2) := by
          rw [Nat.choose_one_right, show 1 + 1 = 2 by omega, Nat.add_comm]
    simp only [slotCount, hM, hMS, hSM, Nat.sub_self, zero_mul, add_zero]
    simpa only [Nat.add_assoc] using hchoose
  · have hSM : S ≤ M := by omega
    have hM : min M S = S := Nat.min_eq_right hSM
    have hMS : min (M + 1) S = S := Nat.min_eq_right (by omega)
    have hSM' : min S (M + 1) = S := Nat.min_eq_left (by omega)
    simp only [slotCount, hM, hMS, hSM']
    have hsub : M + 1 - S = (M - S) + 1 := by omega
    rw [hsub]
    ring

theorem sum_min_add_one (M S : Nat) :
    (∑ u ∈ Finset.range (M + 1), (min S u + 1)) = slotCount M S := by
  induction M with
  | zero => simp [slotCount]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      simpa only [Nat.succ_eq_add_one] using (slotCount_succ M S).symm

def channelUpper (T Ycap S : Nat) : Nat :=
  slotCount (min T Ycap) S * (T + 1)

theorem channelCount_le_channelUpper (T Ycap S : Nat) :
    channelCount T Ycap S ≤ channelUpper T Ycap S := by
  unfold channelCount channelUpper
  let M := min T Ycap
  have hinner (y : Nat) (hy : y ∈ Finset.range (M + 1)) :
      (∑ r ∈ Finset.range (min S (min (T - y) (Ycap - y)) + 1),
          (T + 1 - y - r)) ≤
        (min S (M - y) + 1) * (T + 1) := by
    have hyM : y ≤ M := by
      have := Finset.mem_range.mp hy
      omega
    have hmin : min (T - y) (Ycap - y) = M - y := by
      dsimp only [M]
      omega
    rw [hmin]
    calc
      _ ≤ ∑ _r ∈ Finset.range (min S (M - y) + 1), (T + 1) := by
        exact Finset.sum_le_sum (fun r _ ↦ by omega)
      _ = (min S (M - y) + 1) * (T + 1) := by simp
  calc
    (∑ y ∈ Finset.range (min T Ycap + 1),
      ∑ r ∈ Finset.range (min S (min (T - y) (Ycap - y)) + 1),
        (T + 1 - y - r)) ≤
        ∑ y ∈ Finset.range (M + 1),
          (min S (M - y) + 1) * (T + 1) := by
      exact Finset.sum_le_sum (fun y hy ↦ hinner y hy)
    _ = (∑ u ∈ Finset.range (M + 1), (min S u + 1)) * (T + 1) := by
      have href := Finset.sum_range_reflect
        (fun u ↦ (min S u + 1) * (T + 1)) (M + 1)
      rw [show (∑ y ∈ Finset.range (M + 1),
          (min S (M - y) + 1) * (T + 1)) =
          ∑ u ∈ Finset.range (M + 1), (min S u + 1) * (T + 1) by
        simpa only [Nat.add_sub_cancel] using href,
        Finset.sum_mul]
    _ = slotCount M S * (T + 1) := by rw [sum_min_add_one]

end ProximityPrize.SubmissionLower.LocatorChannelUpper6765

#print axioms ProximityPrize.SubmissionLower.LocatorChannelUpper6765.channelCount_le_channelUpper
