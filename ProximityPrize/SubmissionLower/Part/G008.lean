import ProximityPrize.SubmissionLower.Part.G007


section Compact_OneResidueLower
/-! The closed one-residue expression is still a lower bound after residue
crossings: discard only the extra positive columns. This avoids a large finite
sum while giving a conservative source dimension. -/
namespace ProximityPrize.SubmissionLower.OneResidueLower
open scoped BigOperators
open RCN100 RCN302 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxHeartbeats 2000000
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

private theorem oneResidueCoefficientRow_le_column
    (q r w L j : ℕ) (hw : 2 ≤ w) (hj : j ≤ q)
    (hL : q ≤ L) :
    oneResidueCoefficientRow q r w L j ≤
    (∑ i ∈ Finset.range (q + 1),
      (L + 1 - i - j) *
        (q * w + r - w * i - (w - 1) * j)) := by
  let N := q + 1 - j
  let U := L + 1 - q
  let C := r + j
  have hNpos : 0 < N := by simp only [N]; omega
  have hNq : N ≤ q + 1 := by simp only [N]; omega
  have hsubset : Finset.range N ⊆ Finset.range (q + 1) :=
    Finset.range_mono hNq
  have htrim :
      (∑ i ∈ Finset.range N,
        (L + 1 - i - j) * (q*w+r-w*i-(w-1)*j)) ≤
      ∑ i ∈ Finset.range (q+1),
        (L + 1 - i - j) * (q*w+r-w*i-(w-1)*j) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
  apply le_trans (b := ∑ i ∈ Finset.range N,
    (L + 1 - i - j) * (q*w+r-w*i-(w-1)*j)) ?_ htrim
  apply le_of_eq
  symm
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
  rw [hreflect, hsum]
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
private theorem choose_eq_smallChoose (n k : ℕ) :
    n.choose k = smallChoose n k := by
  simpa only [smallChoose] using Nat.choose_eq_descFactorial_div_factorial n k

theorem oneResidue_le_coefficientCount
    (q r w L s : ℕ) (hw : 2 ≤ w) (hsq : s ≤ q)
    (hL : q ≤ L) (hres : r ≤ w) :
    oneResidueCoefficientCount q r w L s ≤ coefficientCount (q*w+r) w L s := by
  have hcutoff : q + 1 ≤ L + 1 := by omega
  have hweight : q * w + r ≤ w * (q + 1) := by
    have hrw : r ≤ w := by omega
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w q]
    omega
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (q * w + r) w L s (q + 1) hcutoff hweight]
  rw [Finset.sum_comm]
  have hrows :
      (∑ j ∈ Finset.range (s+1), oneResidueCoefficientRow q r w L j) ≤
      ∑ j ∈ Finset.range (s+1), ∑ i ∈ Finset.range (q+1),
        (L+1-i-j)*(q*w+r-w*i-(w-1)*j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact oneResidueCoefficientRow_le_column q r w L j hw
      (by have := Finset.mem_range.mp hj; omega) hL
  apply le_trans (b := ∑ j ∈ Finset.range (s+1),
    oneResidueCoefficientRow q r w L j) ?_ hrows
  apply le_of_eq
  symm
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


end ProximityPrize.SubmissionLower.OneResidueLower

end Compact_OneResidueLower
