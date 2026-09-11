import ProximityPrize.SubmissionLower.Part.G027


section Compact_SecondJetGlobalCounts
/-! Closed coefficient counts for the weighted global second-jet space. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalCounts
open scoped BigOperators
open SecondJetGlobalIndex
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem sum_range_square_mul_six (n : ℕ) :
    (∑ i ∈ Finset.range n, i^2)*6 = n*(n-1)*(2*n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    cases n with
    | zero => simp
    | succ n =>
      have h1 : 2*(n+1)-1 = 2*n+1 := by omega
      have h2 : 2*(n+1+1)-1 = 2*n+3 := by omega
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, h1] at ih
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, h2]
      nlinarith [ih]

theorem sum_fin_square (n : ℕ) :
    (∑ i : Fin n, i.val^2) = n*(n-1)*(2*n-1)/6 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i^2), ← sum_range_square_mul_six]
  exact (Nat.mul_div_cancel _ (by decide : 0 < 6)).symm

def weightedCell (q w C n : ℕ) : ℕ :=
  n*q*C+w*(n*(n-1)*(2*n-1)/6)-(q+w*C)*(n*(n-1)/2)

theorem sum_weighted_cell (q w C n : ℕ)
    (hq : ∀ y : Fin n, w*y.val ≤ q) (hC : ∀ y : Fin n, y.val ≤ C) :
    (∑ y : Fin n, (q-w*y.val)*(C-y.val)) = weightedCell q w C n := by
  have hcell : ∀ y : Fin n,
      (q-w*y.val)*(C-y.val)+(q+w*C)*y.val = q*C+w*y.val^2 := by
    intro y
    have hqy : q = q-w*y.val+w*y.val := (Nat.sub_add_cancel (hq y)).symm
    have hCy : C = C-y.val+y.val := (Nat.sub_add_cancel (hC y)).symm
    calc
      _ = (q-w*y.val)*(C-y.val)+((q-w*y.val+w*y.val)+w*(C-y.val+y.val))*y.val := by
        conv_lhs => arg 2; arg 1; rw [hqy, hCy]
      _ = (q-w*y.val+w*y.val)*(C-y.val+y.val)+w*y.val^2 := by ring
      _ = _ := by rw [← hqy, ← hCy]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun y _ => hcell y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, SecondJetCounts.sum_fin_val, sum_fin_square] at hs
  unfold weightedCell
  rw [mul_comm n q, mul_assoc]
  omega

theorem y_weight_le (D w h r : ℕ) (y : Fin (yCount D w h r)) :
    w*y.val ≤ budget D w h r := by
  have hy : y.val ≤ (budget D w h r-1)/w := Nat.le_of_lt_succ y.isLt
  calc
    w*y.val ≤ w*((budget D w h r-1)/w) := Nat.mul_le_mul_left w hy
    _ ≤ budget D w h r-1 := by
      simpa only [mul_comm] using Nat.div_mul_le_self (budget D w h r-1) w
    _ ≤ budget D w h r := Nat.sub_le _ _

def coefficientCount (D w L B s : ℕ) : ℕ :=
  ∑ h : Fin (s+1), ∑ r : Fin (B-h.val+1),
    weightedCell (budget D w h.val r.val) w (L+1-h.val-r.val) (yCount D w h.val r.val)

theorem card_index_closed (D w L B s : ℕ)
    (hcut : ∀ h : Fin (s+1), ∀ r : Fin (B-h.val+1),
      yCount D w h.val r.val ≤ L+1-h.val-r.val) :
    Fintype.card (Index D w L B s) = coefficientCount D w L B s := by
  rw [card_index]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro r _
  apply sum_weighted_cell
  · exact y_weight_le D w h.val r.val
  · intro y
    exact (Nat.le_of_lt y.isLt).trans (hcut h r)

end
end ProximityPrize.SubmissionLower.SecondJetGlobalCounts

end Compact_SecondJetGlobalCounts
