import ProximityPrize.SubmissionLower.Z6970H2307OrderEval
import ProximityPrize.SubmissionLower.Z6970H2307SlopeShape
import ProximityPrize.SubmissionLower.Z6970ExpandedCappedArithmetic
import ProximityPrize.SubmissionLower.FadicChunk

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307WidePrefix
open K1_13_2 Finset
open scoped BigOperators

def tailSum (j start span : ℕ) : ℤ :=
  ∑ q ∈ range span, cappedCount (ExpandedColumns6970.gradeCap (start+q)) j 500

private theorem tail_split (j start a b : ℕ) :
    tailSum j start (a+b) = tailSum j start a + tailSum j (start+a) b := by
  unfold tailSum
  rw [sum_range_add]
  simp only [Nat.add_assoc]

private theorem upperTail_empty (w j fuel start : ℕ) : upperTail w j fuel start 0 = 0 := by
  cases fuel <;> simp [upperTail]

theorem tail_le (w j fuel start span : ℕ) (hw : 0<w) (hspan : span≤fuel) :
    tailSum j start span ≤ upperTail w j fuel start span := by
  induction fuel generalizing start span with
  | zero =>
    have hz : span=0 := by omega
    simp [hz,upperTail,tailSum]
  | succ fuel ih =>
    by_cases hz : span=0
    · simp [hz,upperTail,tailSum]
    let take := min w span
    have ht0 : 0<take := by dsimp [take]; omega
    have ht : take≤span := min_le_right _ _
    have hleft : span-take≤fuel := by omega
    have hsplit : span=take+(span-take) := by omega
    calc
      tailSum j start span =
          tailSum j start take + tailSum j (start+take) (span-take) := by
            conv_lhs => rw [hsplit]
            exact tail_split j start take (span-take)
      _ ≤ (take : ℤ) * Low6969GateCell.cappedN (ExpandedTaper6970.cap start) j 500 +
          upperTail w j fuel (start+take) (span-take) := by
            apply add_le_add _ (ih (start+take) (span-take) hleft)
            unfold tailSum
            rw [← Low6969GateCell.capped_eq]
            calc
              _ ≤ ∑ q ∈ range take, cappedCount (ExpandedTaper6970.cap start) j 500 := by
                apply sum_le_sum
                intro q _
                apply FadicGate.cappedCount_mono
                exact (min_le_right _ _).trans
                  (ExpandedShape6970.cap_antitone (Nat.le_add_right _ _))
              _ = _ := by simp [nsmul_eq_mul]
      _ = upperTail w j (fuel+1) start span := by simp only [upperTail,if_neg hz,take]

theorem count_le_upper (b j w : ℕ) (hb : b≤4024) (hj : j≤1679) (hw : 0<w) :
    (∑ q ∈ range (b+1), cappedCount (ExpandedColumns6970.gradeCap q) j 500) ≤
      countUpper b j w := by
  by_cases h : b≤3513
  · rw [exact_prefix b j h hj]
    simp [countUpper,min_eq_left h,Nat.sub_eq_zero_of_le h,upperTail_empty]
  · have hB : b+1=3514+(b-3513) := by omega
    rw [hB,sum_range_add]
    change (∑ q ∈ range (3513+1), cappedCount (ExpandedColumns6970.gradeCap q) j 500) +
      tailSum j 3514 (b-3513) ≤ countUpper b j w
    rw [exact_prefix 3513 j le_rfl hj, countUpper, min_eq_right (by omega : 3513≤b)]
    have hspan : b-3513 ≤ 512 := by omega
    exact add_le_add_right (tail_le w j 512 3514 (b-3513) hw hspan) _

end Height2307WidePrefix
