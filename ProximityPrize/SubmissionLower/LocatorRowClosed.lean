/-
Closed form of one row of the weighted cutoff count.

`coefficientCountCutoff D w L s t` is `sumRange (fun i => sumRange (fun j => (L + 1 - i - j) *
(D - w * i - (w - 1) * j)) (s + 1)) t`.  Inside a row the second factor is a genuine product
until `(w - 1) * j` reaches `D - w * i` and zero afterwards, so a row is the sum of an affine
product over `j ≤ J` with `J = min s ((D - w * i - 1) / (w - 1))`, and that sum has the usual
polynomial closed form.  Evaluating a kernel's count then costs one constant-time term per row
instead of one per monomial.
-/
import ProximityPrize.SubmissionLower.LocatorKernelEval

namespace ProximityPrize.SubmissionLower.LocatorRowClosed

open scoped BigOperators

/-- The affine-product sum, without subtraction on the closed-form side. -/
theorem sum_affine_prod (A B c J : ℕ) (hA : J ≤ A) (hB : c * J ≤ B) :
    6 * (∑ j ∈ Finset.range (J + 1), (A - j) * (B - c * j)) +
        3 * (A * c + B) * J * (J + 1) =
      6 * (J + 1) * A * B + c * J * (J + 1) * (2 * J + 1) := by
  induction J with
  | zero => simp; ring
  | succ J ih =>
      have hA' : J ≤ A := Nat.le_of_succ_le hA
      have hB' : c * J ≤ B := le_trans (Nat.mul_le_mul_left c (Nat.le_succ J)) hB
      have ih' := ih hA' hB'
      rw [Finset.sum_range_succ]
      have h1 : (J + 1 : ℕ) ≤ A := hA
      have h2 : c * (J + 1) ≤ B := hB
      zify [h1, h2] at ih' ⊢
      linear_combination ih'

/-- Terms past the truncation index vanish. -/
theorem sum_range_trunc (f : ℕ → ℕ) (J s : ℕ) (hJ : J ≤ s)
    (hz : ∀ j, J < j → j ≤ s → f j = 0) :
    ∑ j ∈ Finset.range (s + 1), f j = ∑ j ∈ Finset.range (J + 1), f j := by
  have hsub : Finset.range (J + 1) ⊆ Finset.range (s + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hJ))
  symm
  apply Finset.sum_subset hsub
  intro j hj hnot
  have hjs : j < s + 1 := Finset.mem_range.mp hj
  have hjJ : ¬ j < J + 1 := fun h => hnot (Finset.mem_range.mpr h)
  exact hz j (by omega) (by omega)

/-- One row of the cutoff count in closed form. `A = L + 1 - i`, `B = D - w * i`,
`c = w - 1`, `J = min s ((B - 1) / c)`. -/
def rowClosed (D w L s i : ℕ) : ℕ :=
  let A := L + 1 - i
  let B := D - w * i
  let c := w - 1
  let J := min s ((B - 1) / c)
  (6 * (J + 1) * A * B + c * J * (J + 1) * (2 * J + 1) - 3 * (A * c + B) * J * (J + 1)) / 6

theorem row_eq_closed (D w L s i : ℕ) (hw : 2 ≤ w) (hB : 1 ≤ D - w * i)
    (hA : s ≤ L + 1 - i) :
    LocatorKernelEval.sumRange (fun j => (L + 1 - i - j) * (D - w * i - (w - 1) * j)) (s + 1) =
      rowClosed D w L s i := by
  rw [LocatorKernelEval.sumRange_eq]
  set A := L + 1 - i with hAdef
  set B := D - w * i with hBdef
  set c := w - 1 with hcdef
  set J := min s ((B - 1) / c) with hJdef
  have hc : 1 ≤ c := by omega
  have hJs : J ≤ s := Nat.min_le_left _ _
  have hJA : J ≤ A := le_trans hJs hA
  have hJB : c * J ≤ B := by
    have h1 : J ≤ (B - 1) / c := Nat.min_le_right _ _
    have h2 : c * ((B - 1) / c) ≤ B - 1 := Nat.mul_div_le (B - 1) c
    have h3 : c * J ≤ c * ((B - 1) / c) := Nat.mul_le_mul_left c h1
    omega
  have htrunc : ∑ j ∈ Finset.range (s + 1), (A - j) * (B - c * j) =
      ∑ j ∈ Finset.range (J + 1), (A - j) * (B - c * j) := by
    apply sum_range_trunc _ J s hJs
    intro j hJj hjs
    have hB0 : B - c * j = 0 := by
      have hnotle : ¬ j ≤ (B - 1) / c := by
        intro h
        have : j ≤ J := le_min hjs h
        omega
      have hlt : (B - 1) / c < j := by omega
      have hlt' : B - 1 < j * c := (Nat.div_lt_iff_lt_mul hc).mp hlt
      have hlt'' : B - 1 < c * j := by rw [Nat.mul_comm] at hlt'; exact hlt'
      omega
    rw [hB0, Nat.mul_zero]
  have hmain := sum_affine_prod A B c J hJA hJB
  rw [htrunc]
  unfold rowClosed
  simp only [← hAdef, ← hBdef, ← hcdef, ← hJdef]
  have hsub : 3 * (A * c + B) * J * (J + 1) ≤
      6 * (J + 1) * A * B + c * J * (J + 1) * (2 * J + 1) := by omega
  have hdiv : (6 * (J + 1) * A * B + c * J * (J + 1) * (2 * J + 1) -
      3 * (A * c + B) * J * (J + 1)) =
      6 * (∑ j ∈ Finset.range (J + 1), (A - j) * (B - c * j)) := by omega
  rw [hdiv, Nat.mul_div_cancel_left _ (by norm_num : 0 < 6)]

theorem sumRange_congr (f g : ℕ → ℕ) (n : ℕ) (h : ∀ i, i < n → f i = g i) :
    LocatorKernelEval.sumRange f n = LocatorKernelEval.sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [LocatorKernelEval.sumRange_succ, LocatorKernelEval.sumRange_succ,
        ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

/-- The cutoff count as a sum of closed-form rows, valid when every row up to `t - 1`
has a positive leading factor and enough length. -/
theorem cutoff_eq_rowsClosed (D w L s t : ℕ) (hw : 2 ≤ w)
    (hB : ∀ i, i < t → 1 ≤ D - w * i) (hA : ∀ i, i < t → s ≤ L + 1 - i) :
    LocatorKernelEval.coefficientCountCutoff D w L s t =
      LocatorKernelEval.sumRange (rowClosed D w L s) t := by
  unfold LocatorKernelEval.coefficientCountCutoff
  exact sumRange_congr _ _ t (fun i hi => row_eq_closed D w L s i hw (hB i hi) (hA i hi))

end ProximityPrize.SubmissionLower.LocatorRowClosed
