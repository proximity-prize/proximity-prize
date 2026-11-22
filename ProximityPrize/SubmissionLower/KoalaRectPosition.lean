import ProximityPrize.SubmissionLower.KoalaRectCharge
import ProximityPrize.SubmissionLower.UpperBranch5


namespace KoalaRect
open Finset
open K1_14 (Shape shapeSum)
open K1_14_4 (gradeWidth)
open scoped BigOperators
open private sum_slot_drops sum_interval power_threshold shapeSum_swap
  from ProximityPrize.SubmissionLower.Fast072

def rectPower (A h : ℕ) (s : Shape) (W : ℕ) : ℕ := 1 + (s.m*A-1-W)/(2*h)

def rectKept (U d : Fin 2 → ℕ) (g r : ℕ) : ℕ := if r ≤ g then rectSlots U d r else 0

def rectCapacity (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) (W : ℕ) : ℕ :=
  shapeSum s fun q j =>
    if q*(131071-h) ≤ W+j then rectKept U d ((q-j)/E) (rectPower A h s W-j) else 0

def rectGrade (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) (W j : ℕ) : ℕ :=
  let r := rectPower A h s W-j
  (gradeWidth (131071-h) s.B W j-r*E)*rectSlots U d r

theorem rectGrade_sum (k B W j r E : ℕ) (U d : Fin 2 → ℕ) (hk : 0 < k) (he : 0 < E) :
    (gradeWidth k B W j-r*E)*rectSlots U d r =
      ∑ q ∈ Ico j (B+1), if q*k ≤ W+j then rectKept U d ((q-j)/E) r else 0 := by
  have hq (q : ℕ) : q*k ≤ W+j ↔ q < (W+j)/k + 1 := by
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hk]
  have hr (q : ℕ) : r ≤ (q-j)/E ↔ r*E ≤ q-j := Nat.le_div_iff_mul_le he
  have hI : (Ico j (B+1)).filter (fun q => q*k ≤ W+j ∧ r ≤ (q-j)/E) =
      Ico (j+r*E) (min (B+1) ((W+j)/k+1)) := by
    ext q
    simp only [mem_filter, mem_Ico, hq, hr, lt_min_iff]
    omega
  simp_rw [rectKept, ← ite_and]
  rw [← sum_filter, hI, sum_const, Nat.nsmul_eq_mul, Nat.card_Ico, gradeWidth, Nat.sub_sub]

theorem rectCapacity_eq (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) (W : ℕ)
    (hk : 0 < 131071-h) (he : 0 < E) :
    (∑ j ∈ range (s.J+1), rectGrade A h s E U d W j) = rectCapacity A h s E U d W := by
  rw [rectCapacity, ← shapeSum_swap]
  exact sum_congr rfl fun j _ => rectGrade_sum _ _ _ _ _ _ _ _ hk he

theorem rectPosition_sum (top step t j g : ℕ) (U d : Fin 2 → ℕ)
    (hj : j ≤ t) (hs : 0 < step) :
    (∑ W ∈ range top, if t ≤ W+j then rectKept U d g (1+(top-1-W)/step-j) else 0) +
    ((∑ a ∈ range g, (rectSlots U d a - rectSlots U d (a+1)) * (top+j-t-step*(j+a))) +
      rectSlots U d g * (top+j-t-step*(j+g))) =
    area U * (top+j-t) := by
  let C := rectKept U d g
  let L W := 1+(top-1-W)/step-j
  have hmono : Antitone C := by
    intro a b hab
    by_cases hb : b ≤ g
    · simpa only [C, rectKept, ite_eq_left hb, ite_eq_left (hab.trans hb)] using
        rectSlots_antitone U d hab
    · simp [C, rectKept, hb]
  have hmin (l : ℕ) : C (min (g+1) l) = C l := by
    by_cases hl : l ≤ g+1
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega)]
      simp [C, rectKept, show ¬ g+1 ≤ g by omega, show ¬ l ≤ g by omega]
  have hsplit :
      (∑ a ∈ range (g+1), (C a - C (a+1)) * (top+j-t-step*(j+a))) =
        (∑ a ∈ range g, (rectSlots U d a - rectSlots U d (a+1)) * (top+j-t-step*(j+a))) +
        rectSlots U d g * (top+j-t-step*(j+g)) := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro a ha
      simp [C, rectKept, (mem_range.mp ha).le, Nat.succ_le_of_lt (mem_range.mp ha)]
    · simp [C, rectKept, show ¬ g+1 ≤ g by omega]
  rw [← hsplit]
  change (∑ W ∈ range top, if t ≤ W+j then C (L W) else 0) + _ = _
  have hzero : C 0 = area U := by simp [C, rectKept, rectSlots_zero]
  rw [← hzero]
  simp_rw [← sum_interval top j t _ _ hj]
  rw [sum_comm (s := range (g+1)), ← sum_add_distrib]
  have hbase := sum_interval top j t 0 (C 0) hj
  rw [Nat.sub_zero] at hbase
  rw [← hbase]
  apply sum_congr rfl
  intro W hW
  have hWt := mem_range.mp hW
  by_cases h : t ≤ W+j
  · simp only [h, true_and, Nat.add_zero, hWt, ite_true]
    have hsum := sum_slot_drops C hmono (g+1) (L W)
    rw [hmin, add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [show a < L W ↔ W+step*(j+a) < top from power_threshold _ _ _ _ _ hWt hs]
  · simp [h]

theorem rectCapacity_total (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ)
    (hh : 0 < 2*h) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range (s.m*A), rectCapacity A h s E U d W) + rectGain A h s E U d =
      area U * shapeSum s (fun q j => s.m*A+j-q*(131071-h)) := by
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range (s.m*A), shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range (s.m*A), F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [rectCapacity, rectGain]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact rectPosition_sum (s.m*A) (2*h) (q*(131071-h)) j ((q-j)/E) U d (hjq.trans hq) hh

end KoalaRect
