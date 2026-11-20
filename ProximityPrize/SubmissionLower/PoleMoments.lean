import ProximityPrize.SubmissionLower.PoleGrid

namespace PoleMoments

open PoleGrid
open scoped BigOperators

private theorem sum_succ (t : ℕ) :
    (∑ k ∈ Finset.range t, (k+1)) = t*(t+1)/2 := by
  have h := Finset.sum_range_succ' (fun k : ℕ ↦ k) t
  simp only [Nat.add_zero] at h
  rw [← h, Finset.sum_range_id]
  simp [Nat.mul_comm]

/-- The closed count of a prefix of the capped derivative-index stock. -/
def colPrefix (J n : ℕ) : ℕ :=
  let t := min n (J+1)
  t*(t+1)/2 + (n-t)*(J+1)

theorem prefix_eq_sum (J n : ℕ) :
    colPrefix J n = ∑ k ∈ Finset.range n, (min J k+1) := by
  let t := min n (J+1)
  have ht : t ≤ n := min_le_left _ _
  have hJ : t ≤ J+1 := min_le_right _ _
  change t*(t+1)/2 + (n-t)*(J+1) = _
  conv_rhs => rw [← Nat.add_sub_of_le ht, Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range t, (min J k+1)) = t*(t+1)/2 := by
    rw [← sum_succ]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    rw [min_eq_right (by omega)]
  have hlast : (∑ k ∈ Finset.range (n-t), (min J (t+k)+1)) = (n-t)*(J+1) := by
    calc
      _ = ∑ _k ∈ Finset.range (n-t), (J+1) := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk' := Finset.mem_range.mp hk
        have he : t = J+1 := by dsimp [t]; omega
        rw [min_eq_left (by omega)]
      _ = _ := by simp
  rw [hfirst, hlast]

theorem colSum_eq (B J ell : ℕ) :
    colSum B J ell = colPrefix J (B+1) - colPrefix J (min ell (B+1)) := by
  rw [prefix_eq_sum, prefix_eq_sum, colSum]
  let t := min ell (B+1)
  have hsets : Finset.range t ∪ Finset.Icc ell B = Finset.range (B+1) := by
    ext q
    simp [t]
    omega
  have hdisj : Disjoint (Finset.range t) (Finset.Icc ell B) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp [t] at hq hq'
    omega
  rw [← hsets, Finset.sum_union hdisj]
  dsimp [t]

  omega

private theorem sum_range_indicator (n lo hi : ℕ) :
    (∑ s ∈ Finset.range n, if lo ≤ s ∧ s < hi then (1 : ℕ) else 0) =
      min n hi - lo := by
  rw [← Finset.sum_filter]
  have hh : (Finset.range n).filter (fun s ↦ lo ≤ s ∧ s < hi) =
      Finset.Ico lo (min n hi) := by
    ext s
    simp
    omega
  rw [hh]
  simp

private theorem sum_triangle (N h : ℕ) (hh : h ≤ (N+1)/2) :
    (∑ k ∈ Finset.range h, (N-2*k)) = h*(N-h+1) := by
  have he : (∑ k ∈ Finset.range h, (N-2*k)) + ∑ k ∈ Finset.range h, 2*k = h*N := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _k ∈ Finset.range h, N := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk' := Finset.mem_range.mp hk
        exact Nat.sub_add_cancel (by omega)
      _ = _ := by simp
  rw [← Finset.mul_sum, Nat.mul_comm 2, Finset.sum_range_id_mul_two] at he
  by_cases hzero : h = 0
  · simp [hzero]
  · have hx : h-1 ≤ N := by omega
    have hy : N-h+1 = N-(h-1) := by omega
    rw [hy, Nat.mul_sub]
    omega

private theorem sum_tail (E h : ℕ) :
    (∑ k ∈ Finset.range h, (E-k)) =
      (min h E)*E - (min h E)*((min h E)-1)/2 := by
  let v := min h E
  have hcut : (∑ k ∈ Finset.range h, (E-k)) = ∑ k ∈ Finset.range v, (E-k) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (min_le_left _ _))
    intro k hk hq
    simp only [Finset.mem_range] at hk hq
    try dsimp [v] at hq
    omega
  rw [hcut]
  change _ = v*E-v*(v-1)/2
  have he : (∑ k ∈ Finset.range v, (E-k)) + ∑ k ∈ Finset.range v, k = v*E := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _k ∈ Finset.range v, E := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk' := Finset.mem_range.mp hk
        have hv : v ≤ E := min_le_right _ _
        exact Nat.sub_add_cancel (by omega)
      _ = _ := by simp
  rw [Finset.sum_range_id] at he
  omega

/-- Closed row stock, with the triangular layers past s=B removed. -/
def rowClosed (B J g : ℕ) : ℕ :=
  let N := B+J-g
  let h := min (J+1) ((N+1)/2)
  let E := N-(B+1)
  let v := min h E
  h*(N-h+1) - (v*E-v*(v-1)/2)

theorem rowSum_eq (B J g : ℕ) (hJ : J ≤ B) :
    rowSum B J g = rowClosed B J g := by
  let N := B+J-g
  let h := min (J+1) ((N+1)/2)
  let E := N-(B+1)
  let v := min h E
  change (∑ s : Fin (B+1), min (min J s.val+1) (N-s.val)) =
    h*(N-h+1) - (v*E-v*(v-1)/2)
  rw [Fin.sum_univ_eq_sum_range (fun s ↦ min (min J s+1) (N-s))]
  have hrow (s : ℕ) :
      min (min J s+1) (N-s) =
        ∑ k ∈ Finset.range h, if k ≤ s ∧ s+k < N then (1 : ℕ) else 0 := by
    rw [← Finset.sum_filter]
    have hh : (Finset.range h).filter (fun k ↦ k ≤ s ∧ s+k < N) =
        Finset.range (min (min J s+1) (N-s)) := by
      ext k
      simp [h]
      omega
    rw [hh]
    simp
  simp_rw [hrow]
  rw [Finset.sum_comm]
  have hpred (k s : ℕ) : k ≤ s ∧ s+k < N ↔ k ≤ s ∧ s < N-k := by omega
  simp_rw [hpred, sum_range_indicator]
  have he : (∑ k ∈ Finset.range h, (min (B+1) (N-k)-k)) +
      (∑ k ∈ Finset.range h, (E-k)) = ∑ k ∈ Finset.range h, (N-2*k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    dsimp [E,h] at *
    omega
  have hh : h ≤ (N+1)/2 := min_le_right _ _
  rw [sum_triangle N h hh, sum_tail E h] at he
  exact Nat.eq_sub_of_add_eq he

end PoleMoments
