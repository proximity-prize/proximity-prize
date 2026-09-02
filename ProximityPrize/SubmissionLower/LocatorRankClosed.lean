/-
Closed form for the block input count.

Provenance.  This file is adapted from the public submission of `BitWonka`
(PR #465 in `proximity-prize/proximity-prize`), which builds on an earlier
revision of this tree, so the `RCN119` names it refers to are unchanged here.

`blockInputCount M L s` is a nested sum over `(M+1) * (s+1)` terms, so
`localRankBound m L s` costs `O(m^2 * s)` kernel steps.  At the multiplicities
this certificate needs that is several million reductions, which exhausts
memory before it finishes.

Whenever `M + s ≤ L` no truncation happens in `L + 1 - i - j`, and the sum is a
pair of Gauss sums.  This file proves the resulting closed form, so the count
becomes a constant-time expression and `localRankBound` becomes `O(m)`.

The public `RCN119.localRankBound` definition is left untouched; the fast form
is exposed through the equality lemma `localRankBound_eq_fast`, so nothing
downstream has to trust it.
-/

import ProximityPrize.SubmissionLower.BC

namespace ProximityPrize.SubmissionLower.LocatorRankClosed

open scoped BigOperators
open RCN119

/-- Gauss sum for a descending run, doubled to stay inside `ℕ`. -/
theorem two_sum_range_sub (c : ℕ) :
    ∀ n : ℕ, n ≤ c →
      2 * (∑ j ∈ Finset.range (n + 1), (c - j)) + n * (n + 1)
        = 2 * ((n + 1) * c) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have e1 : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      have e2 : (n + 1 + 1) * c = (n + 1) * c + c := by ring
      rw [Finset.sum_range_succ]
      omega

/-- The nested block input count in closed form, doubled to stay inside `ℕ`. -/
theorem two_blockInputCount (L s : ℕ) :
    ∀ M : ℕ, M + s ≤ L →
      2 * blockInputCount M L s + (s + 1) * (M * (M + 1))
          + (M + 1) * (s * (s + 1))
        = 2 * ((M + 1) * ((s + 1) * (L + 1))) := by
  intro M
  induction M with
  | zero =>
      intro h
      have hb : blockInputCount 0 L s
          = ∑ j ∈ Finset.range (s + 1), (L + 1 - 0 - j) := by
        simp [blockInputCount]
      have hc := two_sum_range_sub (L + 1) s (by omega)
      simp only [Nat.sub_zero] at hb
      rw [hb]
      simp only [Nat.zero_add, Nat.zero_mul, Nat.mul_zero, Nat.add_zero,
        Nat.one_mul]
      omega
  | succ M ih =>
      intro h
      have hIH := ih (by omega)
      have hsplit : blockInputCount (M + 1) L s
          = blockInputCount M L s
            + ∑ j ∈ Finset.range (s + 1), (L - M - j) := by
        unfold blockInputCount
        rw [Finset.sum_range_succ]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        omega
      have hinner := two_sum_range_sub (L - M) s (by omega)
      have f1 : (s + 1) * ((M + 1) * (M + 1 + 1))
          = (s + 1) * (M * (M + 1)) + 2 * ((s + 1) * (M + 1)) := by ring
      have f2 : (M + 1 + 1) * (s * (s + 1))
          = (M + 1) * (s * (s + 1)) + s * (s + 1) := by ring
      have f3 : (M + 1 + 1) * ((s + 1) * (L + 1))
          = (M + 1) * ((s + 1) * (L + 1)) + (s + 1) * (L + 1) := by ring
      have hML : (L - M) + (M + 1) = L + 1 := by omega
      have f4 : (s + 1) * (L - M) + (s + 1) * (M + 1) = (s + 1) * (L + 1) := by
        rw [← Nat.mul_add, hML]
      rw [hsplit]
      omega

/-- The block input count, as a constant-time expression. -/
def fastBlock (M L s : ℕ) : ℕ :=
  (M + 1) * ((s + 1) * (L + 1))
    - ((s + 1) * (M * (M + 1) / 2) + (M + 1) * (s * (s + 1) / 2))

theorem blockInputCount_eq_fastBlock (M L s : ℕ) (h : M + s ≤ L) :
    blockInputCount M L s = fastBlock M L s := by
  have hdouble := two_blockInputCount L s M h
  obtain ⟨tM, htM⟩ := Nat.even_mul_succ_self M
  obtain ⟨ts, hts⟩ := Nat.even_mul_succ_self s
  have hM2 : M * (M + 1) / 2 = tM := by omega
  have hs2 : s * (s + 1) / 2 = ts := by omega
  have e1 : (s + 1) * (M * (M + 1)) = 2 * ((s + 1) * tM) := by rw [htM]; ring
  have e2 : (M + 1) * (s * (s + 1)) = 2 * ((M + 1) * ts) := by rw [hts]; ring
  unfold fastBlock
  rw [hM2, hs2]
  omega

theorem blockKernelLowerBound_eq (M L s h : ℕ)
    (hM : h ≤ M) (hs : h ≤ s) (hL : h ≤ L) :
    blockKernelLowerBound M L s h = blockInputCount (M - h) (L - h) (s - h) := by
  unfold blockKernelLowerBound blockInputCount
  have e1 : M + 1 - h = (M - h) + 1 := by omega
  have e2 : s + 1 - h = (s - h) + 1 := by omega
  rw [e1, e2]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  congr 1
  omega

theorem blockKernelLowerBound_eq_zero (M L s h : ℕ) (h' : ¬ (h ≤ M ∧ h ≤ s)) :
    blockKernelLowerBound M L s h = 0 := by
  unfold blockKernelLowerBound
  rcases Nat.lt_or_ge M h with hM | hM
  · have e : M + 1 - h = 0 := by omega
    rw [e]
    simp
  · have e : s + 1 - h = 0 := by omega
    rw [e]
    simp

/-- One stage of the rank bound, as a constant-time expression. -/
def fastContact (M L s h : ℕ) : ℕ :=
  fastBlock M L s
    - (if h ≤ M ∧ h ≤ s then fastBlock (M - h) (L - h) (s - h) else 0)

theorem contactRankBound_eq_fast (M L s h : ℕ) (hML : M + s ≤ L) :
    contactRankBound M L s h = fastContact M L s h := by
  unfold contactRankBound fastContact
  rw [blockInputCount_eq_fastBlock M L s hML]
  by_cases hc : h ≤ M ∧ h ≤ s
  · rw [if_pos hc, blockKernelLowerBound_eq M L s h hc.1 hc.2 (by omega),
      blockInputCount_eq_fastBlock (M - h) (L - h) (s - h) (by omega)]
  · rw [if_neg hc, blockKernelLowerBound_eq_zero M L s h hc]

/-- `localRankBound` as an `O(m)` computation. -/
def fastLocalRank (m L s : ℕ) : ℕ :=
  ∑ r ∈ Finset.range m, fastContact (min r L) L s (min (r + 1) (m - r))

theorem localRankBound_eq_fast (m L s : ℕ) (h : m + s ≤ L) :
    localRankBound m L s = fastLocalRank m L s := by
  unfold localRankBound fastLocalRank
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hrm : r < m := Finset.mem_range.mp hr
  exact contactRankBound_eq_fast (min r L) L s _ (by omega)

end ProximityPrize.SubmissionLower.LocatorRankClosed
