import ProximityPrize.SubmissionLower.UpperBranch6
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_2
noncomputable section
open K1_14 (Shape Jet Seeds Equation FX Banks triangle shapeSum)
open K1_14_3 (RowCaps LeadingFilter)
open Polynomial Finset
open K1_14_2_1_2 (seed_finrank)
def eligible (h N W q j : ℕ) : Prop :=
  q * (131071 - h) ≤ W + j ∧ N ≤ W + 2 * h * j
private instance (h N W q j : ℕ) : Decidable (eligible h N W q j) := by
  unfold eligible
  infer_instance
private theorem cutoff_interval_card (N j t d : ℕ) (hj : j ≤ t) :
    (∑ W ∈ range N, if t ≤ W+j ∧ W+d < N then 1 else 0) = N+j-t-d := by
  rw [← card_filter]
  have hr : (range N).filter (fun W => t ≤ W+j ∧ W+d < N) =
      Ico (t-j) (N-d) := by
    ext W
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hr, Nat.card_Ico]
  omega
private theorem position_sum (h N q j : ℕ) (hj : j ≤ q * (131071-h)) :
    (∑ W ∈ range N, if eligible h N W q j then 1 else 0) +
      (N+j-q*(131071-h)-2*h*j) = N+j-q*(131071-h) := by
  let t := q * (131071-h)
  let d := 2*h*j
  change (∑ W ∈ range N, if eligible h N W q j then 1 else 0) +
    (N+j-t-d) = N+j-t
  rw [← cutoff_interval_card N j t d hj, ← sum_add_distrib]
  have hraw := cutoff_interval_card N j t 0 hj
  rw [Nat.sub_zero] at hraw
  rw [← hraw]
  apply sum_congr rfl
  intro W hW
  have hw := mem_range.mp hW
  by_cases ht : t ≤ W+j
  · by_cases hd : W+d < N
    · have he : ¬ eligible h N W q j := fun he => (Nat.not_le_of_lt hd) he.2
      simp [he, ht, hd, hw]
    · have he : eligible h N W q j := ⟨ht, Nat.le_of_not_gt hd⟩
      simp [he, ht, hd, hw]
  · have he : ¬ eligible h N W q j := fun he => ht he.1
    simp [he, ht]
theorem cutoff_total (s : Shape) (h N : ℕ) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range N, shapeSum s (fun q j => if eligible h N W q j then 1 else 0)) +
      shapeSum s (fun q j => N+j-q*(131071-h)-2*h*j) =
      shapeSum s (fun q j => N+j-q*(131071-h)) := by
  have hswap :
      (∑ W ∈ range N, shapeSum s (fun q j => if eligible h N W q j then 1 else 0)) =
      shapeSum s (fun q j => ∑ W ∈ range N, if eligible h N W q j then 1 else 0) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact position_sum h N q j (hjq.trans hq)
end
end P1_7_2
end
