import ProximityPrize.SubmissionLower.Low48ReceiptBase
import ProximityPrize.SubmissionLower.Low48AnchorSpace
import Mathlib.Algebra.BigOperators.Intervals

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

private def stages (d : ℕ) : Finset ℕ :=
  insert d ((range (copies d)).image fun j => extra d + j)

private def inStage (d s : ℕ) : Prop :=
  s = d ∨ (extra d ≤ s ∧ s < extra d + copies d)

private instance (d s : ℕ) : Decidable (inStage d s) := by
  unfold inStage
  infer_instance

private theorem in_stages (d s : ℕ) : s ∈ stages d ↔ inStage d s := by
  unfold stages inStage
  rw [mem_insert, mem_image]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨j, hj, rfl⟩
    rw [mem_range] at hj
    omega
  · intro h
    exact ⟨s - extra d, mem_range.mpr (by omega), by omega⟩

private theorem stages_eq (d : ℕ) (hd : d < 51) :
    (range 124).filter (fun s => cap s = d) = stages d := by
  have checked : (List.range 51).all (fun j =>
      (List.range 124).all (fun s => decide (cap s = j ↔ inStage j s))) = true := by
    decide +kernel
  have room : (List.range 51).all (fun j => decide (extra j + copies j ≤ 124)) = true := by
    decide +kernel
  have hl := of_decide_eq_true (List.all_eq_true.mp room d (List.mem_range.mpr hd))
  ext s
  rw [mem_filter, mem_range, in_stages]
  by_cases hs : s < 124
  · have he := of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp checked d (List.mem_range.mpr hd)) s (List.mem_range.mpr hs))
    simp only [hs, true_and]
    exact he
  · unfold inStage
    simp only [hs, false_and, false_iff]
    omega

private theorem sum_stage_fee (d : ℕ) (hd : d < 51) (r : Row) :
    ∑ s ∈ stages d, fee s r = price d r := by
  have checked : (List.range 51).all (fun j => decide (j < extra j)) = true := by decide +kernel
  have hlt := of_decide_eq_true (List.all_eq_true.mp checked d (List.mem_range.mpr hd))
  have hnot : d ∉ (range (copies d)).image (fun j => extra d + j) := by
    rw [mem_image]
    rintro ⟨j, _, hj⟩
    omega
  have hf : Set.InjOn (fun j : ℕ => extra d+j) (↑(range (copies d))) := by
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  have heq (j : ℕ) : fee (extra d+j) r = fee (extra d) r - j := by unfold fee; omega
  unfold stages price
  rw [sum_insert hnot, sum_image hf]
  simp_rw [heq]
  rw [triangle_diff]

private theorem exchange (st : Finset ℕ) (rows : List Row) :
    (∑ s ∈ st, ((rows.map (fee s)).sum)) =
      (rows.map (fun r => ∑ s ∈ st, fee s r)).sum := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem sum_fees (rows : ℕ → List Row) :
    (∑ s : Fin 124, ((rows (cap s)).map (fee s)).sum) =
      ∑ d : Fin 51, ((rows d).map (price d)).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun s => ((rows (cap s)).map (fee s)).sum) 124,
    Fin.sum_univ_eq_sum_range (fun d => ((rows d).map (price d)).sum) 51]
  calc
    _ = ∑ s ∈ range 124, ∑ d ∈ range 51,
          if cap s = d then ((rows d).map (fee s)).sum else 0 := by
        apply sum_congr rfl
        intro s hs
        rw [sum_eq_single (cap s)]
        · simp
        · intro d hd hne
          simp [Ne.symm hne]
        · intro he
          exact (he (mem_range.mpr (Nat.lt_succ_of_le (cap_le_index s)))).elim
    _ = ∑ d ∈ range 51, ((rows d).map (price d)).sum := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d hd
        rw [← sum_filter, stages_eq d (mem_range.mp hd), exchange]
        simp_rw [sum_stage_fee d (mem_range.mp hd)]

end Low48Receipt
