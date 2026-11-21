import ProximityPrize.SubmissionLower.Low48ReceiptBase
import ProximityPrize.SubmissionLower.Low48AnchorSpace
import Mathlib.Algebra.BigOperators.Intervals
import ProximityPrize.SubmissionLower.Low48ReceiptGroup0

set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Low48Receipt
open Low48AnchorSpace (cap cap_le_index)
open Finset
open scoped BigOperators

private theorem triangle_succ (n : ℕ) :
    triangle (n+1) = triangle n + (n+1) := by
  unfold triangle
  have h : (n+1)*(n+1+1) = n*(n+1) + 2*(n+1) := by ring
  rw [h]
  omega

private theorem triangle_diff (x n : ℕ) :
    ∑ j ∈ range n, (x-j) = triangle x - triangle (x-n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases h : x ≤ n
    · have h' : x ≤ n+1 := by omega
      simp [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le h']
    · have hx : x-n = (x-(n+1))+1 := by omega
      have hle : triangle (x-n) ≤ triangle x := by
        apply Nat.div_le_div_right
        exact Nat.mul_le_mul (Nat.sub_le ..) (by omega)
      rw [hx, triangle_succ] at hle
      rw [hx, triangle_succ]
      omega

private theorem fee_plateau (r : Row) :
    ∑ j ∈ range 54, fee (50+j) r = triangle (fee 50 r) - triangle (fee 104 r) := by
  have heq (j : ℕ) : fee (50+j) r = fee 50 r - j := by unfold fee; omega
  simp_rw [heq]
  rw [triangle_diff, ← heq]

private def plateau : Finset ℕ := (range 54).image (fun j => 50+j)
private def stages (d : ℕ) : Finset ℕ :=
  if d = 49 then insert d plateau
  else if extra d < 122 then {d, extra d, extra d + 1} else {d}

private def inStage (d s : ℕ) : Prop :=
  s = d ∨ (if d = 49 then 50 ≤ s ∧ s < 104
    else extra d < 122 ∧ (s = extra d ∨ s = extra d + 1))

private instance (d s : ℕ) : Decidable (inStage d s) := by
  unfold inStage
  split <;> infer_instance

private theorem in_plateau (s : ℕ) : s ∈ plateau ↔ 50 ≤ s ∧ s < 104 := by
  unfold plateau
  rw [mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [mem_range] at hj
    omega
  · intro hs
    exact ⟨s-50, mem_range.mpr (by omega), by omega⟩

private theorem in_stages (d s : ℕ) : s ∈ stages d ↔ inStage d s := by
  unfold stages inStage
  split_ifs with h he
  · rw [mem_insert, in_plateau]
  · simp [he]
  · simp [he]

private theorem stages_eq (d : ℕ) (hd : d < 50) :
    (range 122).filter (fun s => cap s = d) = stages d := by
  have h : (List.range 50).all (fun j =>
      (List.range 122).all (fun s => decide (cap s = j ↔ inStage j s))) = true := by
    decide +kernel
  ext s
  rw [mem_filter, mem_range, in_stages]
  by_cases hs : s < 122
  · refine ⟨fun hc => ?_, fun hc => ?_⟩
    · exact (of_decide_eq_true
        (List.all_eq_true.mp (List.all_eq_true.mp h d (List.mem_range.mpr hd)) s
          (List.mem_range.mpr hs))).mp hc.2
    · exact ⟨hs, (of_decide_eq_true
        (List.all_eq_true.mp (List.all_eq_true.mp h d (List.mem_range.mpr hd)) s
          (List.mem_range.mpr hs))).mpr hc⟩
  · have hx : extra d < 122 → extra d + 1 < 122 := by
      have hv : (List.range 50).all
          (fun j => decide (extra j < 122 → extra j + 1 < 122)) = true := by
        decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp hv d (List.mem_range.mpr hd))
    simp [hs, inStage]
    split_ifs <;> omega

private theorem extra_lt_gt (d : ℕ) (hd : d < 50) (he : extra d < 122) : d < extra d := by
  have h : (List.range 50).all (fun j => decide (extra j < 122 → j < extra j)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h d (List.mem_range.mpr hd)) he

private theorem sum_stage_fee (d : ℕ) (hd : d < 50) (r : Row) :
    ∑ s ∈ stages d, fee s r = price d r := by
  unfold stages price
  split_ifs with h he
  · subst d
    rw [sum_insert (by rw [in_plateau]; omega : 49 ∉ plateau)]
    unfold plateau
    have hf : Set.InjOn (fun j : ℕ => 50+j) (↑(range 54)) := by
      intro a _ b _ hab
      exact Nat.add_left_cancel hab
    rw [sum_image hf, fee_plateau]
  · have hx := extra_lt_gt d hd he
    have hleft : d ∉ ({extra d, extra d + 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      omega
    have hright : extra d ∉ ({extra d + 1} : Finset ℕ) := by simp
    rw [sum_insert hleft, sum_insert hright, sum_singleton]
  · rw [sum_singleton, Nat.add_zero]

private theorem exchange (st : Finset ℕ) (rows : List Row) :
    (∑ s ∈ st, ((rows.map (fee s)).sum)) =
      (rows.map (fun r => ∑ s ∈ st, fee s r)).sum := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem sum_fees (rows : ℕ → List Row) :
    (∑ s : Fin 122, ((rows (cap s)).map (fee s)).sum) =
      ∑ d : Fin 50, ((rows d).map (price d)).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun s => ((rows (cap s)).map (fee s)).sum) 122,
    Fin.sum_univ_eq_sum_range (fun d => ((rows d).map (price d)).sum) 50]
  calc
    _ = ∑ s ∈ range 122, ∑ d ∈ range 50,
          if cap s = d then ((rows d).map (fee s)).sum else 0 := by
        apply sum_congr rfl
        intro s hs
        rw [sum_eq_single (cap s)]
        · simp
        · intro d hd hne
          simp [Ne.symm hne]
        · intro he
          exact (he (mem_range.mpr (Nat.lt_succ_of_le (cap_le_index s)))).elim
    _ = ∑ d ∈ range 50, ((rows d).map (price d)).sum := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d hd
        rw [← sum_filter, stages_eq d (mem_range.mp hd), exchange]
        simp_rw [sum_stage_fee d (mem_range.mp hd)]

end Low48Receipt
