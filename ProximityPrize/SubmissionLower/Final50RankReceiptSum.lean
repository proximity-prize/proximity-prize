import ProximityPrize.SubmissionLower.Final50RankReceiptBase
import ProximityPrize.SubmissionLower.Final50AnchorSpace
import Mathlib.Algebra.BigOperators.Intervals

set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Final50RankReceipt
open Final50AnchorSpace (cap cap_le_index)
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

private def late (d : ℕ) : Finset ℕ :=
  (range (lateHi d - lateLo d)).image (fun s => lateLo d + s)

private def stages (d : ℕ) : Finset ℕ := insert d (late d)

private def inStage (d s : ℕ) : Prop := s = d ∨ lateLo d ≤ s ∧ s < lateHi d
private instance (d s : ℕ) : Decidable (inStage d s) := by unfold inStage; infer_instance

private theorem in_late (d s : ℕ) : s ∈ late d ↔ lateLo d ≤ s ∧ s < lateHi d := by
  unfold late
  rw [mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [mem_range] at hi
    omega
  · intro hs
    exact ⟨s - lateLo d, mem_range.mpr (by omega), by omega⟩

private theorem stage_bounds (d : ℕ) (hd : d < 56) :
    d < lateLo d ∧ lateLo d ≤ lateHi d ∧ lateHi d ≤ 133 := by
  have checks : (List.range 56).all (fun i => decide
      (i < lateLo i ∧ lateLo i ≤ lateHi i ∧ lateHi i ≤ 133)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checks d (List.mem_range.mpr hd))

private theorem stages_eq (d : ℕ) (hd : d < 56) :
    (range 133).filter (fun s => cap s = d) = stages d := by
  have checks : (List.range 56).all (fun j =>
      (List.range 133).all (fun s => decide (cap s = j ↔ inStage j s))) = true := by decide +kernel
  ext s
  rw [mem_filter, mem_range, stages, mem_insert, in_late]
  by_cases hs : s < 133
  · have hh := of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp checks d (List.mem_range.mpr hd)) s (List.mem_range.mpr hs))
    simpa only [hs, true_and, inStage] using hh
  · obtain ⟨_, _, hhi⟩ := stage_bounds d hd
    simp [hs]
    omega

private theorem fee_add (s i : ℕ) (r : Row) : fee (s+i) r = fee s r - i := by
  unfold fee
  omega

private theorem sum_stage_fee (d : ℕ) (hd : d < 56) (r : Row) :
    ∑ s ∈ stages d, fee s r = price d r := by
  obtain ⟨hlo, hlen, _⟩ := stage_bounds d hd
  have hmiss : d ∉ late d := fun h => (Nat.not_le_of_gt hlo) ((in_late d d).mp h).1
  have hinj : Set.InjOn (fun s : ℕ => lateLo d+s) (↑(range (lateHi d-lateLo d))) := by
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  rw [stages, sum_insert hmiss, late, sum_image hinj, price]
  simp_rw [fee_add (lateLo d)]
  rw [triangle_diff, ← fee_add, Nat.add_sub_of_le hlen]

private theorem exchange (st : Finset ℕ) (rows : List Row) :
    (∑ s ∈ st, ((rows.map (fee s)).sum)) =
      (rows.map (fun r => ∑ s ∈ st, fee s r)).sum := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem sum_fees (rows : ℕ → List Row) :
    (∑ s : Fin 133, ((rows (cap s)).map (fee s)).sum) =
      ∑ d : Fin 56, ((rows d).map (price d)).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun s => ((rows (cap s)).map (fee s)).sum) 133,
    Fin.sum_univ_eq_sum_range (fun d => ((rows d).map (price d)).sum) 56]
  calc
    _ = ∑ s ∈ range 133, ∑ d ∈ range 56,
          if cap s = d then ((rows d).map (fee s)).sum else 0 := by
        apply sum_congr rfl
        intro s hs
        rw [sum_eq_single (cap s)]
        · simp
        · intro d hd hne
          simp [Ne.symm hne]
        · intro he
          exact (he (mem_range.mpr (Nat.lt_succ_of_le (cap_le_index s)))).elim
    _ = ∑ d ∈ range 56, ((rows d).map (price d)).sum := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d hd
        rw [← sum_filter, stages_eq d (mem_range.mp hd), exchange]
        simp_rw [sum_stage_fee d (mem_range.mp hd)]

end Final50RankReceipt
