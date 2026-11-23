import ProximityPrize.SubmissionLower.GoldBranch6N4
import ProximityPrize.SubmissionLower.UpperBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_5
open K1_14 (Shape slots shapeSum)
def kept (U v g r : ℕ) : ℕ :=
  if r ≤ g then slots U (r*v) else 0
end P1_7_5
end
section
namespace P1_7_5
noncomputable section
open Polynomial Finset MvPolynomial
open K1_14 (FX Jet Equation Shape SeedBound shapeSum slots triangle)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth seedDegree seedDegree_le_iff seedDegree_mul seedDegree_pow)
open private flatten  from ProximityPrize.SubmissionLower.Fast069
open private gradeMap mem_filtered finrank_le_grades from ProximityPrize.SubmissionLower.Fast069
open private shapeSum_swap from ProximityPrize.SubmissionLower.Fast072
end
end P1_7_5
end
section
namespace P1_7_5
open Finset
open K1_14 (Shape shapeSum slots triangle)
open P1 (agreement)
open private slots_antitone sum_slot_drops sum_interval power_threshold from ProximityPrize.SubmissionLower.Fast072
private theorem position_sum (top step t j U v g : ℕ) (hj : j ≤ t) (hs : 0 < step) :
    (∑ W ∈ range top, if t ≤ W+j then
      kept U v g (1+(top-1-W)/step-j) else 0) +
    ((∑ a ∈ range g, (slots U (a*v) - slots U ((a+1)*v)) * (top+j-t-step*(j+a))) +
      slots U (g*v) * (top+j-t-step*(j+g))) =
    triangle U * (top+j-t) := by
  let A := kept U v g
  let L W := 1+(top-1-W)/step-j
  have hmono : Antitone A := by
    intro a b hab
    by_cases hb : b ≤ g
    · simpa only [A, kept, ite_eq_left hb, ite_eq_left (hab.trans hb)] using
        slots_antitone U (Nat.mul_le_mul_right v hab)
    · simp [A, kept, hb]
  have hmin (l : ℕ) : A (min (g+1) l) = A l := by
    by_cases hl : l ≤ g+1
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega)]
      simp [A, kept, show ¬ g+1 ≤ g by omega, show ¬ l ≤ g by omega]
  have hsplit :
      (∑ a ∈ range (g+1), (A a - A (a+1)) * (top+j-t-step*(j+a))) =
        (∑ a ∈ range g, (slots U (a*v) - slots U ((a+1)*v)) * (top+j-t-step*(j+a))) +
        slots U (g*v) * (top+j-t-step*(j+g)) := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro a ha
      simp [A, kept, (mem_range.mp ha).le, Nat.succ_le_of_lt (mem_range.mp ha)]
    · simp [A, kept, show ¬ g+1 ≤ g by omega]
  rw [← hsplit]
  change (∑ W ∈ range top, if t ≤ W+j then A (L W) else 0) + _ = _
  have hzero : A 0 = triangle U := by simp [A, kept, slots]
  rw [← hzero]
  simp_rw [← sum_interval top j t _ _ hj]
  rw [sum_comm (s := range (g+1)), ← sum_add_distrib]
  have hbase := sum_interval top j t 0 (A 0) hj
  rw [Nat.sub_zero] at hbase
  rw [← hbase]
  apply sum_congr rfl
  intro W hW
  have hWt := mem_range.mp hW
  by_cases h : t ≤ W+j
  · simp only [h, true_and, Nat.add_zero, hWt, ite_true]
    have hsum := sum_slot_drops A hmono (g+1) (L W)
    rw [hmin, add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [show a < L W ↔ W+step*(j+a) < top from power_threshold _ _ _ _ _ hWt hs]
  · simp [h]
end P1_7_5
end
