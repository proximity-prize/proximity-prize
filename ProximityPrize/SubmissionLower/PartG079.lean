import ProximityPrize.SubmissionLower.PartG078


section Compact_SecondJetRelaxedGlobalCounts
/-! Closed coefficient sums for the relaxed global monomial family. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts
open scoped BigOperators
open SecondJetRelaxedGlobalIndex
open SecondJetGlobalCounts (weightedCell sum_weighted_cell)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem y_weight_le (D : ℕ → ℕ) (w U h r : ℕ) (y : Fin (yCount D w U h r)) :
    w*y.val ≤ budget D w h r := by
  have hy : y.val ≤ (budget D w h r-1)/w := by
    have hh := y.isLt
    unfold yCount at hh
    omega
  calc
    w*y.val ≤ w*((budget D w h r-1)/w) := Nat.mul_le_mul_left w hy
    _ ≤ budget D w h r-1 := by
      simpa only [mul_comm] using Nat.div_mul_le_self (budget D w h r-1) w
    _ ≤ budget D w h r := Nat.sub_le _ _

def coefficientCount (D : ℕ → ℕ) (w L B s U : ℕ) : ℕ :=
  ∑ h : Fin (s+1), ∑ r : Fin (B-2*h.val+1),
    weightedCell (budget D w h.val r.val) w (L+1-h.val-r.val) (yCount D w U h.val r.val)

theorem card_index_closed (D : ℕ → ℕ) (w L B s U : ℕ) (hUL : U ≤ L) :
    Fintype.card (Index D w L B s U) = coefficientCount D w L B s U := by
  rw [card_index]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro r _
  apply sum_weighted_cell
  · exact y_weight_le D w U h.val r.val
  · intro y
    have hy := y.isLt
    unfold yCount at hy
    omega

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts

end Compact_SecondJetRelaxedGlobalCounts
