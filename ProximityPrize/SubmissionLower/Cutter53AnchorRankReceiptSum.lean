import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptBase
import ProximityPrize.SubmissionLower.Cutter53AnchorSpace
import Mathlib.Algebra.BigOperators.Intervals

set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Cutter53AnchorRankReceipt
open Cutter53AnchorSpace (cap cap_le_index)
open Finset
open scoped BigOperators

open Low51EdgeRankReceipt (Row triangle)

def fee (s : ℕ) (r : Row) : ℕ := 96 + r.index - (s + r.ord)

def extra : ℕ → ℕ × ℕ
  | 32 => (128, 2)
  | 34 => (126, 2)
  | 36 => (124, 2)
  | 39 => (122, 2)
  | 41 => (120, 2)
  | 43 => (118, 2)
  | 45 => (116, 2)
  | 47 => (114, 2)
  | 49 => (112, 2)
  | 51 => (110, 2)
  | 53 => (54, 56)
  | _ => (130, 0)

def price (d : ℕ) (r : Row) : ℕ :=
  fee d r + (triangle (fee (extra d).1 r) - triangle (fee ((extra d).1 + (extra d).2) r))

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

def extraGrades (d : ℕ) : Finset ℕ :=
  (range (extra d).2).image (fun j => (extra d).1+j)

private def stages (d : ℕ) : Finset ℕ := insert d (extraGrades d)

theorem in_extra (d s : ℕ) : s ∈ extraGrades d ↔
    (extra d).1 ≤ s ∧ s < (extra d).1+(extra d).2 := by
  unfold extraGrades
  rw [mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [mem_range] at hj
    omega
  · intro hs
    exact ⟨s-(extra d).1, mem_range.mpr (by omega), by omega⟩

private theorem stages_eq (d : ℕ) (hd : d < 54) :
    (range 130).filter (fun s => cap s = d) = stages d := by
  have h : (List.range 54).all (fun j => (List.range 130).all (fun s =>
      decide (cap s = j ↔ s = j ∨ ((extra j).1 ≤ s ∧ s < (extra j).1+(extra j).2)))) = true := by
    decide +kernel
  have hbound : (extra d).1+(extra d).2 ≤ 130 := by interval_cases d <;> decide
  ext s
  rw [mem_filter, mem_range, stages, mem_insert, in_extra]
  by_cases hs : s < 130
  · exact (and_iff_right hs).trans (of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp h d (List.mem_range.mpr hd)) s (List.mem_range.mpr hs)))
  · constructor
    · exact fun hab => (hs hab.1).elim
    · intro hs'
      rcases hs' with h0 | h0 <;> omega

private theorem sum_stage_fee (d : ℕ) (hd : d < 54) (r : Row) :
    ∑ s ∈ stages d, fee s r = price d r := by
  have hstart : 54 ≤ (extra d).1 := by interval_cases d <;> decide
  have hnot : d ∉ extraGrades d := by rw [in_extra]; omega
  unfold stages price
  rw [sum_insert hnot]
  congr 1
  unfold extraGrades
  have hinj : Set.InjOn (fun j : ℕ => (extra d).1+j) (↑(range (extra d).2)) := by
    intro a _ b _ h
    exact Nat.add_left_cancel h
  rw [sum_image hinj]
  have heq (j : ℕ) : fee ((extra d).1+j) r = fee (extra d).1 r - j := by unfold fee; omega
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
    (∑ s : Fin 130, ((rows (cap s)).map (fee s)).sum) =
      ∑ d : Fin 54, ((rows d).map (price d)).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun s => ((rows (cap s)).map (fee s)).sum) 130,
    Fin.sum_univ_eq_sum_range (fun d => ((rows d).map (price d)).sum) 54]
  calc
    _ = ∑ s ∈ range 130, ∑ d ∈ range 54,
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

end Cutter53AnchorRankReceipt
