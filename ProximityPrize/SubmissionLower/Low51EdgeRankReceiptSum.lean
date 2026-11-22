import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptBase
import ProximityPrize.SubmissionLower.Low51EdgeAnchorSpace
import Mathlib.Algebra.BigOperators.Intervals

set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Low51EdgeRankReceipt
open Low51EdgeAnchorSpace (cap cap_le_index)
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

theorem fee_plateau (r : Row) :
    ∑ j ∈ range 52, fee (53+j) r = triangle (fee 53 r) - triangle (fee 105 r) := by
  have heq (j : ℕ) : fee (53+j) r = fee 53 r - j := by unfold fee; omega
  simp_rw [heq]
  rw [triangle_diff, ← heq]

def plateau : Finset ℕ := (range 52).image (fun j => 53+j)
private def stages (d : ℕ) : Finset ℕ :=
  if d = 53 then plateau
  else if extra d < 127 then
    if d ≤ 45 then {d, extra d, extra d + 1} else {d, extra d}
    else {d}

def inStage (d s : ℕ) : Prop :=
  if d = 53 then 53 ≤ s ∧ s < 105
  else s = d ∨ extra d < 127 ∧ (s = extra d ∨ d ≤ 45 ∧ s = extra d + 1)

private instance (d s : ℕ) : Decidable (inStage d s) := by
  unfold inStage
  split <;> infer_instance

theorem in_plateau (s : ℕ) : s ∈ plateau ↔ 53 ≤ s ∧ s < 105 := by
  unfold plateau
  rw [mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [mem_range] at hj
    omega
  · intro hs
    exact ⟨s-53, mem_range.mpr (by omega), by omega⟩

theorem in_stages (d s : ℕ) : s ∈ stages d ↔ inStage d s := by
  unfold stages inStage
  split_ifs with h he hd
  · exact in_plateau s
  · simp [he,hd]
  · simp [he,hd]
  · simp [he]

private theorem stages_eq (d : ℕ) (hd : d < 54) :
    (range 127).filter (fun s => cap s = d) = stages d := by
  have h : (List.range 54).all (fun j =>
      (List.range 127).all (fun s => decide (cap s = j ↔ inStage j s))) = true := by
    decide +kernel
  ext s
  rw [mem_filter, mem_range, in_stages]
  by_cases hs : s < 127
  · refine ⟨fun hc => ?_, fun hc => ?_⟩
    · exact (of_decide_eq_true
        (List.all_eq_true.mp (List.all_eq_true.mp h d (List.mem_range.mpr hd)) s
          (List.mem_range.mpr hs))).mp hc.2
    · exact ⟨hs, (of_decide_eq_true
        (List.all_eq_true.mp (List.all_eq_true.mp h d (List.mem_range.mpr hd)) s
          (List.mem_range.mpr hs))).mpr hc⟩
  · have hx : extra d < 127 → extra d + 1 < 127 := by
      have hv : (List.range 54).all
          (fun j => decide (extra j < 127 → extra j + 1 < 127)) = true := by
        decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp hv d (List.mem_range.mpr hd))
    simp [hs, inStage]
    split_ifs <;> omega

theorem extra_lt_gt (d : ℕ) (hd : d < 54) (he : extra d < 127) : d < extra d := by
  have h : (List.range 54).all (fun j => decide (extra j < 127 → j < extra j)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h d (List.mem_range.mpr hd)) he

private theorem sum_stage_fee (d : ℕ) (hd : d < 54) (r : Row) :
    ∑ s ∈ stages d, fee s r = price d r := by
  unfold stages price
  split_ifs with h he hc
  · subst d
    unfold plateau
    have hf : Set.InjOn (fun j : ℕ => 53+j) (↑(range 52)) := by
      intro a _ b _ hab
      exact Nat.add_left_cancel hab
    rw [sum_image hf, fee_plateau]
  · have hx := extra_lt_gt d hd he
    have hleft : d ∉ ({extra d, extra d + 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      omega
    have hright : extra d ∉ ({extra d + 1} : Finset ℕ) := by simp
    rw [sum_insert hleft, sum_insert hright, sum_singleton]
  · have hx := extra_lt_gt d hd he
    rw [sum_insert (by simpa using (Nat.ne_of_lt hx) : d ∉ ({extra d} : Finset ℕ))]
    simp
  · rw [sum_singleton, Nat.add_zero]

private theorem exchange (st : Finset ℕ) (rows : List Row) :
    (∑ s ∈ st, ((rows.map (fee s)).sum)) =
      (rows.map (fun r => ∑ s ∈ st, fee s r)).sum := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem sum_fees (rows : ℕ → List Row) :
    (∑ s : Fin 127, ((rows (cap s)).map (fee s)).sum) =
      ∑ d : Fin 54, ((rows d).map (price d)).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun s => ((rows (cap s)).map (fee s)).sum) 127,
    Fin.sum_univ_eq_sum_range (fun d => ((rows d).map (price d)).sum) 54]
  calc
    _ = ∑ s ∈ range 127, ∑ d ∈ range 54,
          if cap s = d then ((rows d).map (fee s)).sum else 0 := by
        apply sum_congr rfl
        intro s hs
        rw [sum_eq_single (cap s)]
        · simp
        · intro d hd hne
          simp [Ne.symm hne]
        · intro he
          exact (he (mem_range.mpr (Nat.lt_succ_of_le (cap_le_index s)))).elim
    _ = ∑ d ∈ range 54, ((rows d).map (price d)).sum := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d hd
        rw [← sum_filter, stages_eq d (mem_range.mp hd), exchange]
        simp_rw [sum_stage_fee d (mem_range.mp hd)]

end Low51EdgeRankReceipt
