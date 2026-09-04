import ProximityPrize.SubmissionLower.LocatorBatchPowerRoute

/-! Packed from ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic. -/
section PackedLocator_LocatorFastKernelArithmetic

/-!
# Kernel-cheap arithmetic for large locator sources

The contact-rank bound is definitionally a sum of nested `Finset.range` sums.
For the larger replacement sources, evaluating that definition directly would
expand hundreds of millions of summands.  This file closes each rectangular
block symbolically and leaves only one primitive recursion over the contact
rows.  It also provides a primitive-recursive evaluator for coefficient
counts after the weighted cutoff has removed the long zero tail.
-/

namespace ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 RCN302
open LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Number of entries in a rectangular block, weighted by the descending
affine function `L + 1 - offset - i - j`. -/
def rectangularCount (ni nj offset L : ℕ) : ℕ :=
  ni * nj * (L + 1 - offset) -
    (nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2))

private theorem pairIndexSum (ni nj : ℕ) :
    (∑ i ∈ Finset.range ni, ∑ j ∈ Finset.range nj, (i + j)) =
      nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2) := by
  calc
    (∑ i ∈ Finset.range ni, ∑ j ∈ Finset.range nj, (i + j)) =
        ∑ i ∈ Finset.range ni,
          (nj * i + nj * (nj - 1) / 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_add_distrib, Finset.sum_range_id]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
    _ = nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_id]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]

theorem rectangularSum_eq_rectangularCount (ni nj offset L : ℕ)
    (hbound : offset + (ni - 1) + (nj - 1) ≤ L) :
    (∑ i ∈ Finset.range ni,
      ∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) =
      rectangularCount ni nj offset L := by
  have hpoint : ∀ i ∈ Finset.range ni, ∀ j ∈ Finset.range nj,
      (L + 1 - offset - i - j) + (i + j) = L + 1 - offset := by
    intro i hi j hj
    have hil : i ≤ ni - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hjl : j ≤ nj - 1 := by
      have := Finset.mem_range.mp hj
      omega
    omega
  have hadd :
      (∑ i ∈ Finset.range ni,
        ∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) +
          (∑ i ∈ Finset.range ni,
            ∑ j ∈ Finset.range nj, (i + j)) =
        ni * nj * (L + 1 - offset) := by
    calc
      _ = ∑ i ∈ Finset.range ni,
          ((∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) +
            ∑ j ∈ Finset.range nj, (i + j)) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ i ∈ Finset.range ni,
          ∑ j ∈ Finset.range nj,
            ((L + 1 - offset - i - j) + (i + j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_add_distrib.symm
      _ = ∑ i ∈ Finset.range ni,
          ∑ _j ∈ Finset.range nj, (L + 1 - offset) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint i hi j hj
      _ = ni * nj * (L + 1 - offset) := by
          simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
          ring
  rw [pairIndexSum] at hadd
  unfold rectangularCount
  omega

theorem blockInputCount_eq_rectangularCount (M L s : ℕ)
    (hbound : M + s ≤ L) :
    blockInputCount M L s = rectangularCount (M + 1) (s + 1) 0 L := by
  simpa only [blockInputCount, Nat.zero_add, Nat.sub_zero] using
    rectangularSum_eq_rectangularCount (M + 1) (s + 1) 0 L (by omega)

theorem blockKernelLowerBound_eq_rectangularCount (M L s h : ℕ)
    (hbound : M + s ≤ L) :
    blockKernelLowerBound M L s h =
      rectangularCount (M + 1 - h) (s + 1 - h) h L := by
  by_cases hM : h ≤ M
  · by_cases hs : h ≤ s
    · have hL : h ≤ L := by omega
      have hshape : M - h + (s - h) ≤ L - h := by omega
      have heq : blockKernelLowerBound M L s h =
          blockInputCount (M - h) (L - h) (s - h) := by
        have hMr : M + 1 - h = M - h + 1 := by omega
        have hsr : s + 1 - h = s - h + 1 := by omega
        have hLr : L + 1 - h = L - h + 1 := by omega
        unfold blockKernelLowerBound blockInputCount
        rw [hMr, hsr, hLr]
      rw [heq, blockInputCount_eq_rectangularCount _ _ _ hshape]
      have hMr : M + 1 - h = M - h + 1 := by omega
      have hsr : s + 1 - h = s - h + 1 := by omega
      have hLr : L + 1 - h = L - h + 1 := by omega
      unfold rectangularCount
      rw [hMr, hsr, hLr]
      simp only [Nat.sub_zero]
    · have hz : s + 1 - h = 0 := by omega
      simp [blockKernelLowerBound, rectangularCount, hz]
  · have hz : M + 1 - h = 0 := by omega
    simp [blockKernelLowerBound, rectangularCount, hz]

theorem contactRankBound_eq_rectangularCount (M L s h : ℕ)
    (hbound : M + s ≤ L) :
    contactRankBound M L s h =
      rectangularCount (M + 1) (s + 1) 0 L -
        rectangularCount (M + 1 - h) (s + 1 - h) h L := by
  unfold contactRankBound
  rw [blockInputCount_eq_rectangularCount M L s hbound,
    blockKernelLowerBound_eq_rectangularCount M L s h hbound]

/-- The same local rank as `RCN119.localRankBound`, but every rectangular
block is closed and the sole remaining sum uses primitive recursion. -/
def fastLocalRankBound (m L s : ℕ) : ℕ :=
  kernelSumRange (fun r =>
    let M := min r L
    let h := min (r + 1) (m - r)
    rectangularCount (M + 1) (s + 1) 0 L -
      rectangularCount (M + 1 - h) (s + 1 - h) h L) m

theorem localRankBound_eq_fastLocalRankBound (m L s : ℕ)
    (hshape : m + s ≤ L + 1) :
    localRankBound m L s = fastLocalRankBound m L s := by
  unfold localRankBound fastLocalRankBound
  rw [kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro r hr
  have hrm : r < m := Finset.mem_range.mp hr
  have hb : min r L + s ≤ L := by
    have hm : min r L ≤ r := Nat.min_le_left _ _
    omega
  exact contactRankBound_eq_rectangularCount
    (min r L) L s (min (r + 1) (m - r)) hb

/-- Coefficient count with the weighted zero tail removed and both finite sums
represented by primitive recursion. -/
def fastCoefficientCount (D w L s cutoff : ℕ) : ℕ :=
  kernelSumRange (fun i =>
    kernelSumRange (fun j =>
      (L + 1 - i - j) * (D - w * i - (w - 1) * j)) (s + 1)) cutoff

theorem coefficientCount_eq_fastCoefficientCount
    (D w L s cutoff : ℕ) (hcutoff : cutoff ≤ L + 1)
    (hweight : D ≤ w * cutoff) :
    coefficientCount D w L s = fastCoefficientCount D w L s cutoff := by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    D w L s cutoff hcutoff hweight]
  unfold fastCoefficientCount
  rw [kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [kernelSumRange_eq]

/-! The primitive evaluator above is already much cheaper than the original
nested `Finset` computation, but it still performs `cutoff * (s + 1)` steps.
The inner summand is quadratic, so the following evaluator closes each row and
performs only `cutoff` primitive steps. -/

private def triangularCount (n : ℕ) : ℕ := n * (n - 1) / 2

private def squareCount (n : ℕ) : ℕ :=
  n * (n - 1) * (2 * n - 1) / 6

private theorem kernelSumRange_id (n : ℕ) :
    kernelSumRange (fun j => j) n = triangularCount n := by
  rw [kernelSumRange_eq, Finset.sum_range_id]
  rfl

private theorem kernelSumRange_square_mul_six (n : ℕ) :
    kernelSumRange (fun j => j * j) n * 6 =
      n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [kernelSumRange_succ, Nat.add_mul, ih]
      cases n with
      | zero => decide
      | succ k =>
          have h1 : k + 1 - 1 = k := by omega
          have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
          have h3 : k + 1 + 1 - 1 = k + 1 := by omega
          have h4 : 2 * (k + 1 + 1) - 1 = 2 * k + 3 := by omega
          rw [h1, h2, h3, h4]
          ring

private theorem kernelSumRange_square (n : ℕ) :
    kernelSumRange (fun j => j * j) n = squareCount n := by
  unfold squareCount
  rw [← kernelSumRange_square_mul_six n,
    Nat.mul_div_cancel _ (by decide : 0 < 6)]

private theorem finset_sum_range_square (n : ℕ) :
    (∑ j ∈ Finset.range n, j * j) = squareCount n := by
  rw [← kernelSumRange_eq, kernelSumRange_square]

/-- Closed value of `sum_{j<N} (A-j)*(B-c*j)` when neither subtraction
truncates on that range. -/
private def quadraticDescendingCount (A B c N : ℕ) : ℕ :=
  N * (A * B) + c * squareCount N -
    (A * c + B) * triangularCount N

private theorem descendingProduct_add_cross (A B c j : ℕ)
    (hjA : j ≤ A) (hjB : c * j ≤ B) :
    (A - j) * (B - c * j) + (A * c + B) * j =
      A * B + c * (j * j) := by
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hjA, Nat.cast_sub hjB]
  ring

private theorem descendingProductSum_eq_quadraticDescendingCount
    (A B c N : ℕ) (hA : N - 1 ≤ A) (hB : c * (N - 1) ≤ B) :
    (∑ j ∈ Finset.range N, (A - j) * (B - c * j)) =
      quadraticDescendingCount A B c N := by
  have hsum :
      (∑ j ∈ Finset.range N, (A - j) * (B - c * j)) +
          (∑ j ∈ Finset.range N, (A * c + B) * j) =
        ∑ j ∈ Finset.range N, (A * B + c * (j * j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j ≤ N - 1 := by
      have := Finset.mem_range.mp hj
      omega
    exact descendingProduct_add_cross A B c j (hjN.trans hA)
      ((Nat.mul_le_mul_left c hjN).trans hB)
  have hlinear :
      (∑ j ∈ Finset.range N, (A * c + B) * j) =
        (A * c + B) * triangularCount N := by
    rw [← Finset.mul_sum, Finset.sum_range_id]
    rfl
  have hright :
      (∑ j ∈ Finset.range N, (A * B + c * (j * j))) =
        N * (A * B) + c * squareCount N := by
    have hconstant :
        (∑ _j ∈ Finset.range N, A * B) = N * (A * B) := by
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
    have hsquare :
        (∑ j ∈ Finset.range N, c * (j * j)) = c * squareCount N := by
      rw [← Finset.mul_sum, finset_sum_range_square]
    rw [Finset.sum_add_distrib, hconstant, hsquare]
  rw [hlinear, hright] at hsum
  unfold quadraticDescendingCount
  omega

/-- Closed form for one coefficient-count row.  `J` is the last index before
either descending factor becomes truncated, so all later terms are zero. -/
def closedCoefficientRow (D w L s i : ℕ) : ℕ :=
  let A := L + 1 - i
  let B := D - w * i
  let c := w - 1
  let J := min s (min (L - i) (B / c))
  quadraticDescendingCount A B c (J + 1)

theorem coefficientRow_eq_closedCoefficientRow
    (D w L s i : ℕ) (hw : 2 ≤ w) :
    (∑ j ∈ Finset.range (s + 1),
      (L + 1 - i - j) * (D - w * i - (w - 1) * j)) =
      closedCoefficientRow D w L s i := by
  let A := L + 1 - i
  let B := D - w * i
  let c := w - 1
  let J := min s (min (L - i) (B / c))
  have hc : 0 < c := by simp only [c]; omega
  have hJs : J ≤ s := Nat.min_le_left _ _
  have hJL : J ≤ L - i :=
    (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have hJdiv : J ≤ B / c :=
    (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
  have hJB : c * J ≤ B := by
    have h := (Nat.le_div_iff_mul_le hc).mp hJdiv
    simpa only [Nat.mul_comm] using h
  have hsmall :
      (∑ j ∈ Finset.range (J + 1),
        (L + 1 - i - j) * (D - w * i - (w - 1) * j)) =
        quadraticDescendingCount A B c (J + 1) := by
    have hA : J + 1 - 1 ≤ A := by simp only [A]; omega
    have hB : c * (J + 1 - 1) ≤ B := by
      simpa only [Nat.add_sub_cancel] using hJB
    simpa only [A, B, c] using
      descendingProductSum_eq_quadraticDescendingCount A B c (J + 1) hA hB
  have hsubset : Finset.range (J + 1) ⊆ Finset.range (s + 1) :=
    Finset.range_mono (by omega)
  have htrim :
      (∑ j ∈ Finset.range (J + 1),
        (L + 1 - i - j) * (D - w * i - (w - 1) * j)) =
      ∑ j ∈ Finset.range (s + 1),
        (L + 1 - i - j) * (D - w * i - (w - 1) * j) := by
    apply Finset.sum_subset hsubset
    intro j hjfull hjnot
    have hjs : j ≤ s := by
      have := Finset.mem_range.mp hjfull
      omega
    by_cases hjL : j ≤ L - i
    · by_cases hjB : c * j ≤ B
      · have hjdiv : j ≤ B / c :=
          (Nat.le_div_iff_mul_le hc).mpr (by
            simpa only [Nat.mul_comm] using hjB)
        have hjJ : j ≤ J := by
          simp only [J]
          exact le_min hjs (le_min hjL hjdiv)
        exact (hjnot (Finset.mem_range.mpr (by omega))).elim
      · have hz : D - w * i - (w - 1) * j = 0 := by
          simp only [B, c] at hjB
          omega
        simp only [hz, Nat.mul_zero]
    · have hz : L + 1 - i - j = 0 := by omega
      simp only [hz, Nat.zero_mul]
  calc
    (∑ j ∈ Finset.range (s + 1),
      (L + 1 - i - j) * (D - w * i - (w - 1) * j)) =
        ∑ j ∈ Finset.range (J + 1),
          (L + 1 - i - j) * (D - w * i - (w - 1) * j) := htrim.symm
    _ = quadraticDescendingCount A B c (J + 1) := hsmall
    _ = closedCoefficientRow D w L s i := by
      rfl

/-- Coefficient count with a closed inner row and one primitive outer sum. -/
def fastClosedCoefficientCount (D w L s cutoff : ℕ) : ℕ :=
  kernelSumRange (closedCoefficientRow D w L s) cutoff

theorem coefficientCount_eq_fastClosedCoefficientCount
    (D w L s cutoff : ℕ) (hw : 2 ≤ w)
    (hcutoff : cutoff ≤ L + 1) (hweight : D ≤ w * cutoff) :
    coefficientCount D w L s =
      fastClosedCoefficientCount D w L s cutoff := by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    D w L s cutoff hcutoff hweight]
  unfold fastClosedCoefficientCount
  rw [kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro i hi
  exact coefficientRow_eq_closedCoefficientRow D w L s i hw

/-! ## Constant-time coefficient count in the one-residue regime

For the large power sources used by the 6800 locator, write `D = q*w+r`.
Their entire slope range satisfies `r+s <= w`.  Hence, in slope row `j`,
the nonzero weighted columns are exactly `0,...,q-j`.  Reflecting those
columns and summing the resulting quadratic gives a linear combination of
`choose (q+1-j) 1`, `choose (q+1-j) 2`, and `choose (q+1-j) 3`.
The hockey-stick identity then closes the remaining slope sum.  Numerical
evaluation below uses descending factorials, so its cost depends only on the
fixed indices `2,3,4`, rather than on `q` or `s`.
-/

private theorem two_mul_choose_two_add (n : ℕ) :
    2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        2 * (n + n.choose 2) + (n + 1) =
            (2 * n.choose 2 + n) + (2 * n + 1) := by ring
        _ = n * n + (2 * n + 1) := by rw [ih]
        _ = (n + 1) * (n + 1) := by ring

private theorem kernelSumRange_square_eq_choose (n : ℕ) :
    kernelSumRange (fun i => i * i) n =
      2 * n.choose 3 + n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [kernelSumRange_succ, ih, Nat.choose_succ_succ,
        Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      rw [← two_mul_choose_two_add n]
      ring

private theorem finset_sum_range_square_eq_choose (n : ℕ) :
    (∑ i ∈ Finset.range n, i * i) =
      2 * n.choose 3 + n.choose 2 := by
  rw [← kernelSumRange_eq, kernelSumRange_square_eq_choose]

private theorem sum_increasingProduct_eq_choose (U C w N : ℕ) :
    (∑ h ∈ Finset.range N, (U + h) * (C + w * h)) =
      N * (U * C) + (U * w + C) * N.choose 2 +
        w * (2 * N.choose 3 + N.choose 2) := by
  calc
    (∑ h ∈ Finset.range N, (U + h) * (C + w * h)) =
        ∑ h ∈ Finset.range N,
          (U * C + (U * w + C) * h + w * (h * h)) := by
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = N * (U * C) + (U * w + C) * N.choose 2 +
          w * (2 * N.choose 3 + N.choose 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_id,
        finset_sum_range_square_eq_choose, ← Nat.choose_two_right]

private theorem three_mul_choose_three_add_two_mul_choose_two (n : ℕ) :
    3 * n.choose 3 + 2 * n.choose 2 = n * n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        3 * (n.choose 2 + n.choose 3) +
              2 * (n + n.choose 2) =
            (3 * n.choose 3 + 2 * n.choose 2) +
              (2 * n.choose 2 + n) + (n.choose 2 + n) := by ring
        _ = n * n.choose 2 + n * n + (n.choose 2 + n) := by
          rw [ih, two_mul_choose_two_add]
        _ = (n + 1) * (n + n.choose 2) := by ring

private theorem oneResidueRow_algebra
    (U C w r j q N wm T V : ℕ)
    (hC : C = r + j) (hN : N + j = q + 1) (hw : wm + 2 = w)
    (hsq : 2 * T + N = N * N)
    (hcub : 3 * V + 2 * T = N * T) :
    N * (U * C) + (U * w + C) * T + w * (2 * V + T) =
      U * (r + q) * N +
        (U * wm + r + q + (wm + 1)) * T +
          (2 * wm + 1) * V := by
  have hCz : (C : ℤ) = (r : ℤ) + j := by exact_mod_cast hC
  have hNz : (N : ℤ) + j = (q : ℤ) + 1 := by exact_mod_cast hN
  have hwz : (wm : ℤ) + 2 = w := by exact_mod_cast hw
  have hsqz : 2 * (T : ℤ) + N = N * N := by exact_mod_cast hsq
  have hcubz : 3 * (V : ℤ) + 2 * T = N * T := by exact_mod_cast hcub
  have hqz : (q : ℤ) = N + j - 1 := by linarith
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [hCz, ← hwz, hqz]
  linear_combination (U : ℤ) * hsqz + hcubz

/-- The three binomial coefficients of one slope row after reflecting its
weighted columns. -/
private def oneResidueCoefficientRow (q r w L j : ℕ) : ℕ :=
  let U := L + 1 - q
  let N := q + 1 - j
  U * (r + q) * N.choose 1 +
    (U * (w - 2) + r + q + ((w - 2) + 1)) * N.choose 2 +
      (2 * (w - 2) + 1) * N.choose 3

private theorem coefficientColumn_eq_oneResidueCoefficientRow
    (q r w L j : ℕ) (hw : 2 ≤ w) (hj : j ≤ q)
    (hL : q ≤ L) (hres : r + j ≤ w) :
    (∑ i ∈ Finset.range (q + 1),
      (L + 1 - i - j) *
        (q * w + r - w * i - (w - 1) * j)) =
      oneResidueCoefficientRow q r w L j := by
  let N := q + 1 - j
  let U := L + 1 - q
  let C := r + j
  have hNpos : 0 < N := by simp only [N]; omega
  have hNq : N ≤ q + 1 := by simp only [N]; omega
  have hsubset : Finset.range N ⊆ Finset.range (q + 1) :=
    Finset.range_mono hNq
  have htrim :
      (∑ i ∈ Finset.range N,
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j)) =
      ∑ i ∈ Finset.range (q + 1),
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j) := by
    apply Finset.sum_subset hsubset
    intro i hi hinot
    have hiq : i ≤ q := by
      have := Finset.mem_range.mp hi
      omega
    have hiN : N ≤ i := by
      by_contra hni
      exact hinot (Finset.mem_range.mpr (by omega))
    have hij : q + 1 ≤ i + j := by simp only [N] at hiN; omega
    have hr : r ≤ w - j := by omega
    have hmul : w * (q + 1) ≤ w * (i + j) :=
      Nat.mul_le_mul_left w hij
    have hwj : w * j - j = (w - 1) * j := by
      symm
      rw [Nat.sub_mul]
      simp only [Nat.one_mul]
    have hweight : q * w + r ≤ w * i + (w - 1) * j := by
      calc
        q * w + r ≤ q * w + (w - j) := Nat.add_le_add_left hr _
        _ = w * (q + 1) - j := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w q]
          omega
        _ ≤ w * (i + j) - j := Nat.sub_le_sub_right hmul j
        _ = w * i + (w - 1) * j := by
          have hjwj : j ≤ w * j :=
            Nat.le_mul_of_pos_left j (by omega)
          rw [Nat.mul_add, Nat.add_sub_assoc hjwj, hwj]
    have hz : q * w + r - w * i - (w - 1) * j = 0 := by
      rw [Nat.sub_sub]
      exact Nat.sub_eq_zero_of_le hweight
    simp only [hz, Nat.mul_zero]
  have hreflect :
      (∑ i ∈ Finset.range N,
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j)) =
      ∑ h ∈ Finset.range N, (U + h) * (C + w * h) := by
    rw [← Finset.sum_range_reflect (fun i =>
      (L + 1 - i - j) *
        (q * w + r - w * i - (w - 1) * j)) N]
    apply Finset.sum_congr rfl
    intro h hh
    have hhN : h < N := Finset.mem_range.mp hh
    have hidx : N - 1 - h = q - j - h := by
      simp only [N]
      omega
    have hqsplit : q = (q - j - h) + j + h := by omega
    have hwj : w * j = (w - 1) * j + j := by
      have hw' : w - 1 + 1 = w := by omega
      calc
        w * j = (w - 1 + 1) * j := by rw [hw']
        _ = (w - 1) * j + j := by ring
    have htotal :
        q * w + r = w * (q - j - h) + (w - 1) * j +
          (r + j + w * h) := by
      calc
        q * w + r = ((q - j - h) + j + h) * w + r := by rw [← hqsplit]
        _ = w * (q - j - h) + w * j + w * h + r := by ring
        _ = w * (q - j - h) + (w - 1) * j +
            (r + j + w * h) := by rw [hwj]; ring
    have hfirst : L + 1 - (N - 1 - h) - j = U + h := by
      simp only [N, U]
      omega
    have hsecond :
        q * w + r - w * (N - 1 - h) - (w - 1) * j =
          C + w * h := by
      rw [hidx]
      simp only [C]
      omega
    rw [hfirst, hsecond]
  have hsum := sum_increasingProduct_eq_choose U C w N
  have hNj : N + j = q + 1 := by simp only [N]; omega
  have hwsub : w - 2 + 2 = w := by omega
  have hsq := two_mul_choose_two_add N
  have hcub := three_mul_choose_three_add_two_mul_choose_two N
  rw [← htrim, hreflect, hsum]
  change N * (U * C) + (U * w + C) * N.choose 2 +
      w * (2 * N.choose 3 + N.choose 2) =
    U * (r + q) * N.choose 1 +
      (U * (w - 2) + r + q + ((w - 2) + 1)) * N.choose 2 +
        (2 * (w - 2) + 1) * N.choose 3
  simp only [Nat.choose_one_right]
  exact oneResidueRow_algebra
    (U := U) (C := C) (w := w) (r := r) (j := j) (q := q)
    (N := N) (wm := w - 2) (T := N.choose 2) (V := N.choose 3)
    (by rfl) hNj hwsub hsq hcub

private theorem sum_range_choose_descending_add (N s k : ℕ)
    (hs : s ≤ N) :
    (∑ j ∈ Finset.range (s + 1), (N - j).choose k) +
        (N - s).choose (k + 1) = (N + 1).choose (k + 1) := by
  induction s with
  | zero =>
      simp only [Nat.sub_zero, Finset.range_one, Finset.sum_singleton]
      exact (Nat.choose_succ_succ' N k).symm
  | succ s ih =>
      have hs' : s ≤ N := by omega
      rw [Finset.sum_range_succ]
      have hold := ih hs'
      have hpred : N - s = (N - (s + 1)) + 1 := by omega
      have hp := Nat.choose_succ_succ' (N - (s + 1)) k
      rw [← hpred] at hp
      omega

private theorem sum_range_choose_descending (N s k : ℕ)
    (hs : s ≤ N) :
    (∑ j ∈ Finset.range (s + 1), (N - j).choose k) =
      (N + 1).choose (k + 1) - (N - s).choose (k + 1) := by
  have h := sum_range_choose_descending_add N s k hs
  omega

/-- `Nat.choose` evaluated through a descending factorial.  In this file it
is used only at indices at most four, so closed source receipts do not recurse
through a thousand Pascal rows. -/
def smallChoose (n k : ℕ) : ℕ :=
  n.descFactorial k / Nat.factorial k

private theorem choose_eq_smallChoose (n k : ℕ) :
    n.choose k = smallChoose n k := by
  simpa only [smallChoose] using
    Nat.choose_eq_descFactorial_div_factorial n k

/-- Constant-time coefficient count for `D=q*w+r` when the complete slope
range remains in the first residue regime. -/
def oneResidueCoefficientCount (q r w L s : ℕ) : ℕ :=
  let U := L + 1 - q
  let c1 := U * (r + q)
  let c2 := U * (w - 2) + r + q + ((w - 2) + 1)
  let c3 := 2 * (w - 2) + 1
  c1 * (smallChoose (q + 2) 2 - smallChoose (q + 1 - s) 2) +
    c2 * (smallChoose (q + 2) 3 - smallChoose (q + 1 - s) 3) +
      c3 * (smallChoose (q + 2) 4 - smallChoose (q + 1 - s) 4)

theorem coefficientCount_eq_oneResidueCoefficientCount
    (q r w L s : ℕ) (hw : 2 ≤ w) (hsq : s ≤ q)
    (hL : q ≤ L) (hres : r + s ≤ w) :
    coefficientCount (q * w + r) w L s =
      oneResidueCoefficientCount q r w L s := by
  have hcutoff : q + 1 ≤ L + 1 := by omega
  have hweight : q * w + r ≤ w * (q + 1) := by
    have hrw : r ≤ w := by omega
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w q]
    omega
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (q * w + r) w L s (q + 1) hcutoff hweight]
  rw [Finset.sum_comm]
  have hrows :
      (∑ j ∈ Finset.range (s + 1),
        ∑ i ∈ Finset.range (q + 1),
          (L + 1 - i - j) *
            (q * w + r - w * i - (w - 1) * j)) =
      ∑ j ∈ Finset.range (s + 1),
        oneResidueCoefficientRow q r w L j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjs : j ≤ s := by
      have := Finset.mem_range.mp hj
      omega
    exact coefficientColumn_eq_oneResidueCoefficientRow q r w L j hw
      (hjs.trans hsq) hL ((Nat.add_le_add_left hjs r).trans hres)
  rw [hrows]
  let U := L + 1 - q
  let c1 := U * (r + q)
  let c2 := U * (w - 2) + r + q + ((w - 2) + 1)
  let c3 := 2 * (w - 2) + 1
  have h1 := sum_range_choose_descending (q + 1) s 1 (by omega)
  have h2 := sum_range_choose_descending (q + 1) s 2 (by omega)
  have h3 := sum_range_choose_descending (q + 1) s 3 (by omega)
  unfold oneResidueCoefficientRow
  change (∑ j ∈ Finset.range (s + 1),
      (c1 * (q + 1 - j).choose 1 +
        c2 * (q + 1 - j).choose 2 +
          c3 * (q + 1 - j).choose 3)) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2, h3]
  unfold oneResidueCoefficientCount
  rw [← choose_eq_smallChoose, ← choose_eq_smallChoose,
    ← choose_eq_smallChoose, ← choose_eq_smallChoose,
    ← choose_eq_smallChoose, ← choose_eq_smallChoose]

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

/-- A numerical nullity receipt for any source profile gives the dimension
needed by the arbitrary-power route, uniformly in the two received words. -/
theorem challengeConstraintKernel_finrank_lower_bound_of_numeric
    (D L s m gap : ℕ) (u0 u1 : I → K)
    (hnumeric : gap ≤ coefficientCount D 131071 L s -
      262144 * localRankBound m L s) :
    gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L s m
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    (K := K) D 131071 L s m IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact hnumeric.trans hlo'

end ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic
end PackedLocator_LocatorFastKernelArithmetic

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier19 : True := by trivial
end ProximityPrize.SubmissionLower

