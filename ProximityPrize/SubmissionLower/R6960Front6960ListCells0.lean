import ProximityPrize.SubmissionLower.R6960Front6960ListBank

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def allowance_0 (u : ℕ) : ℕ :=
  nominal 0 u

private theorem bound_0 (u : ℕ) :
    (CJ0.blockMatrix source 0 ((u : ℤ)-23)).rank ≤ allowance_0 u := by
  unfold allowance_0
  exact (block_rank_le 0 _).trans (rank_le_nominal 0 _)

theorem grade_0 : (∑ u ∈ Finset.range (81-0), (CJ0.blockMatrix source 0 ((u : ℤ)-23)).rank) ≤ 58 := by
  refine (Finset.sum_le_sum fun u _ => bound_0 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_0)]
  decide +kernel

private def allowance_1 (u : ℕ) : ℕ :=
  nominal 1 u

private theorem bound_1 (u : ℕ) :
    (CJ0.blockMatrix source 1 ((u : ℤ)-23)).rank ≤ allowance_1 u := by
  unfold allowance_1
  exact (block_rank_le 1 _).trans (rank_le_nominal 1 _)

theorem grade_1 : (∑ u ∈ Finset.range (81-1), (CJ0.blockMatrix source 1 ((u : ℤ)-23)).rank) ≤ 171 := by
  refine (Finset.sum_le_sum fun u _ => bound_1 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_1)]
  decide +kernel

private def allowance_2 (u : ℕ) : ℕ :=
  nominal 2 u

private theorem bound_2 (u : ℕ) :
    (CJ0.blockMatrix source 2 ((u : ℤ)-23)).rank ≤ allowance_2 u := by
  unfold allowance_2
  exact (block_rank_le 2 _).trans (rank_le_nominal 2 _)

theorem grade_2 : (∑ u ∈ Finset.range (81-2), (CJ0.blockMatrix source 2 ((u : ℤ)-23)).rank) ≤ 336 := by
  refine (Finset.sum_le_sum fun u _ => bound_2 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_2)]
  decide +kernel

private def allowance_3 (u : ℕ) : ℕ :=
  nominal 3 u

private theorem bound_3 (u : ℕ) :
    (CJ0.blockMatrix source 3 ((u : ℤ)-23)).rank ≤ allowance_3 u := by
  unfold allowance_3
  exact (block_rank_le 3 _).trans (rank_le_nominal 3 _)

theorem grade_3 : (∑ u ∈ Finset.range (81-3), (CJ0.blockMatrix source 3 ((u : ℤ)-23)).rank) ≤ 550 := by
  refine (Finset.sum_le_sum fun u _ => bound_3 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_3)]
  decide +kernel

private def allowance_4 (u : ℕ) : ℕ :=
  nominal 4 u

private theorem bound_4 (u : ℕ) :
    (CJ0.blockMatrix source 4 ((u : ℤ)-23)).rank ≤ allowance_4 u := by
  unfold allowance_4
  exact (block_rank_le 4 _).trans (rank_le_nominal 4 _)

theorem grade_4 : (∑ u ∈ Finset.range (81-4), (CJ0.blockMatrix source 4 ((u : ℤ)-23)).rank) ≤ 810 := by
  refine (Finset.sum_le_sum fun u _ => bound_4 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_4)]
  decide +kernel

private def allowance_5 (u : ℕ) : ℕ :=
  nominal 5 u

private theorem bound_5 (u : ℕ) :
    (CJ0.blockMatrix source 5 ((u : ℤ)-23)).rank ≤ allowance_5 u := by
  unfold allowance_5
  exact (block_rank_le 5 _).trans (rank_le_nominal 5 _)

theorem grade_5 : (∑ u ∈ Finset.range (81-5), (CJ0.blockMatrix source 5 ((u : ℤ)-23)).rank) ≤ 1113 := by
  refine (Finset.sum_le_sum fun u _ => bound_5 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_5)]
  decide +kernel

private def allowance_6 (u : ℕ) : ℕ :=
  nominal 6 u

private theorem bound_6 (u : ℕ) :
    (CJ0.blockMatrix source 6 ((u : ℤ)-23)).rank ≤ allowance_6 u := by
  unfold allowance_6
  exact (block_rank_le 6 _).trans (rank_le_nominal 6 _)

theorem grade_6 : (∑ u ∈ Finset.range (81-6), (CJ0.blockMatrix source 6 ((u : ℤ)-23)).rank) ≤ 1456 := by
  refine (Finset.sum_le_sum fun u _ => bound_6 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_6)]
  decide +kernel

private def allowance_7 (u : ℕ) : ℕ :=
  nominal 7 u

private theorem bound_7 (u : ℕ) :
    (CJ0.blockMatrix source 7 ((u : ℤ)-23)).rank ≤ allowance_7 u := by
  unfold allowance_7
  exact (block_rank_le 7 _).trans (rank_le_nominal 7 _)

theorem grade_7 : (∑ u ∈ Finset.range (81-7), (CJ0.blockMatrix source 7 ((u : ℤ)-23)).rank) ≤ 1836 := by
  refine (Finset.sum_le_sum fun u _ => bound_7 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_7)]
  decide +kernel

private def allowance_8 (u : ℕ) : ℕ :=
  nominal 8 u

private theorem bound_8 (u : ℕ) :
    (CJ0.blockMatrix source 8 ((u : ℤ)-23)).rank ≤ allowance_8 u := by
  unfold allowance_8
  exact (block_rank_le 8 _).trans (rank_le_nominal 8 _)

theorem grade_8 : (∑ u ∈ Finset.range (81-8), (CJ0.blockMatrix source 8 ((u : ℤ)-23)).rank) ≤ 2250 := by
  refine (Finset.sum_le_sum fun u _ => bound_8 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_8)]
  decide +kernel

private def allowance_9 (u : ℕ) : ℕ :=
  nominal 9 u

private theorem bound_9 (u : ℕ) :
    (CJ0.blockMatrix source 9 ((u : ℤ)-23)).rank ≤ allowance_9 u := by
  unfold allowance_9
  exact (block_rank_le 9 _).trans (rank_le_nominal 9 _)

theorem grade_9 : (∑ u ∈ Finset.range (81-9), (CJ0.blockMatrix source 9 ((u : ℤ)-23)).rank) ≤ 2695 := by
  refine (Finset.sum_le_sum fun u _ => bound_9 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_9)]
  decide +kernel

end Front6960ListBank
