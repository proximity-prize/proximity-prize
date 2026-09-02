/-
Proof-preserving kernel evaluation helpers for the locator arithmetic.

The primitive-recursion pattern is adapted from the benchmark maintainer's
`submission-helpers/KernelEval.lean` (protected-main PR #437).  The two
domain-specific evaluators below keep the public `coefficientCount` and
`localRankBound` definitions unchanged and expose equality lemmas back to
those definitions.
-/

import ProximityPrize.SubmissionLower.L1

namespace ProximityPrize.SubmissionLower.LocatorKernelEval

open scoped BigOperators

/-- `Finset.range` summation represented by primitive recursion on `Nat`. -/
def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n

@[simp] theorem sumRange_zero (f : ℕ → ℕ) : sumRange f 0 = 0 := rfl

@[simp] theorem sumRange_succ (f : ℕ → ℕ) (n : ℕ) :
    sumRange f (n + 1) = sumRange f n + f n := rfl

theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => rw [sumRange_succ, ih, Finset.sum_range_succ]

/-- Division-free form of the descending affine sum. -/
theorem sum_range_sub_add (a m : ℕ) (h : m ≤ a) :
    (∑ r ∈ Finset.range (m + 1), (a - r)) +
        (∑ r ∈ Finset.range (m + 1), r) = (m + 1) * a := by
  rw [← Finset.sum_add_distrib]
  have hpt : ∀ r ∈ Finset.range (m + 1), (a - r) + r = a := by
    intro r hr
    have : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    omega
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range,
    Nat.nsmul_eq_mul]

/-- Closed form of a descending affine sum in `Nat`. -/
theorem sum_range_sub (a m : ℕ) (h : m ≤ a) :
    ∑ r ∈ Finset.range (m + 1), (a - r) =
      (m + 1) * a - (m + 1) * m / 2 := by
  have hadd := sum_range_sub_add a m h
  have hgauss : (∑ r ∈ Finset.range (m + 1), r) * 2 = (m + 1) * m :=
    Finset.sum_range_id_mul_two (m + 1)
  omega

/-- Kernel-cheap form of the weighted-cutoff coefficient sum. -/
def coefficientCountCutoff (D w L s t : ℕ) : ℕ :=
  sumRange (fun i =>
    sumRange (fun j => (L + 1 - i - j) * (D - w * i - (w - 1) * j))
      (s + 1)) t

theorem coefficientCount_eq_cutoff
    (D w L s t : ℕ) (ht : t ≤ L + 1) (hD : D ≤ w * t) :
    RCN100.coefficientCount D w L s = coefficientCountCutoff D w L s t := by
  rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
    D w L s t ht hD, coefficientCountCutoff, sumRange_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [sumRange_eq]

/-- Kernel-cheap form of the rectangular block-input count, with the affine
inner sum closed before evaluation. -/
def blockInputCount (M L s : ℕ) : ℕ :=
  sumRange (fun i =>
    (s + 1) * (L + 1 - i) - (s + 1) * s / 2) (M + 1)

theorem blockInputCount_eq (M L s : ℕ) (hML : M + s ≤ L + 1) :
    blockInputCount M L s = RCN119.blockInputCount M L s := by
  rw [blockInputCount, sumRange_eq]
  unfold RCN119.blockInputCount
  apply Finset.sum_congr rfl
  intro i hi
  have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hs : s ≤ L + 1 - i := by omega
  exact (sum_range_sub (L + 1 - i) s hs).symm

/-- Kernel-cheap form of the rectangular block-kernel lower bound, again with
the affine inner sum closed before evaluation. -/
def blockKernelLowerBound (M L s h : ℕ) : ℕ :=
  if h ≤ s then
    sumRange (fun i =>
      let sh := s - h
      (sh + 1) * (L + 1 - h - i) - (sh + 1) * sh / 2) (M + 1 - h)
  else 0

theorem blockKernelLowerBound_eq (M L s h : ℕ) (hML : M + s ≤ L + 1) :
    blockKernelLowerBound M L s h = RCN119.blockKernelLowerBound M L s h := by
  by_cases hh : h ≤ s
  · rw [blockKernelLowerBound, if_pos hh, sumRange_eq]
    unfold RCN119.blockKernelLowerBound
    apply Finset.sum_congr rfl
    intro i hi
    have hiM : i < M + 1 - h := Finset.mem_range.mp hi
    have hs : s - h ≤ L + 1 - h - i := by omega
    have hlen : s + 1 - h = s - h + 1 := by omega
    rw [hlen]
    exact (sum_range_sub (L + 1 - h - i) (s - h) hs).symm
  · rw [blockKernelLowerBound, if_neg hh]
    unfold RCN119.blockKernelLowerBound
    have hzero : s + 1 - h = 0 := by omega
    simp only [hzero, Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero]

def contactRankBound (M L s h : ℕ) : ℕ :=
  blockInputCount M L s - blockKernelLowerBound M L s h

theorem contactRankBound_eq (M L s h : ℕ) (hML : M + s ≤ L + 1) :
    contactRankBound M L s h = RCN119.contactRankBound M L s h := by
  rw [contactRankBound, RCN119.contactRankBound, blockInputCount_eq M L s hML,
    blockKernelLowerBound_eq M L s h hML]

/-- Kernel-cheap evaluator for the locator's local-rank definition. -/
def localRankBound (m L s : ℕ) : ℕ :=
  sumRange (fun r =>
    contactRankBound (min r L) L s (min (r + 1) (m - r))) m

theorem localRankBound_eq (m L s : ℕ) (hML : m + s ≤ L + 1) :
    localRankBound m L s = RCN119.localRankBound m L s := by
  rw [localRankBound, sumRange_eq]
  unfold RCN119.localRankBound
  apply Finset.sum_congr rfl
  intro r hr
  have hrm : r < m := Finset.mem_range.mp hr
  have hcell : min r L + s ≤ L + 1 := by
    have : min r L ≤ r := Nat.min_le_left _ _
    omega
  rw [contactRankBound_eq _ _ _ _ hcell]

end ProximityPrize.SubmissionLower.LocatorKernelEval
