/-
Optional submission helper. Not part of the challenge; copy it into your
submission root and edit it freely.
-/

-- Only Mathlib: this file is identical for the lower and upper tracks.
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Kernel-cheap evaluation helpers

`by decide` hands the goal to the **kernel**, which discharges it by unfolding
definitions. It never runs `simp`. So no closed-form lemma -- yours, ours, or
Mathlib's -- can make a `decide` cheaper; only the definition it unfolds can.

`Finset.range n` is a `Multiset`, hence a `Quot` of a `List`, and `Finset.sum` is
`Multiset.foldr`, so every summand costs the kernel a `Quot.lift`/`List.rec`
traversal where a `Nat` recursion costs one addition. That is what `sumRange`
below avoids, and what the closed forms remove entirely.
-/

namespace KernelEval

/-- `∑ i ∈ Finset.range n, f i`, by structural recursion on `ℕ`.

Write this where you would write `∑ i ∈ Finset.range n, f i` inside a definition
that a `decide` has to evaluate. -/
def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n

@[simp] theorem sumRange_zero (f : ℕ → ℕ) : sumRange f 0 = 0 := rfl

@[simp] theorem sumRange_succ (f : ℕ → ℕ) (n : ℕ) :
    sumRange f (n + 1) = sumRange f n + f n := rfl

/-- Stated in this direction on purpose: it rewrites *your* definition into the
`Finset` form, so every existing Mathlib lemma about `Finset.sum` still applies.
The kernel speedup comes from the definition; this lemma preserves your proofs. -/
theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => rw [sumRange_succ, ih, Finset.sum_range_succ]

/-! ### Closed forms

`sumRange` is cheaper per element than `Finset.sum`, but still linear in the
number of elements. When the body is affine the sum has a closed form and the
cost drops to O(1), which is a much larger difference than the one above. -/

/-- Division-free form of `∑_{r=0}^{m} (a - r)`: holds in `ℕ` with no division
and no side condition beyond `m ≤ a`. -/
theorem sum_range_sub_add (a m : ℕ) (h : m ≤ a) :
    (∑ r ∈ Finset.range (m + 1), (a - r)) + (∑ r ∈ Finset.range (m + 1), r)
      = (m + 1) * a := by
  rw [← Finset.sum_add_distrib]
  have hpt : ∀ r ∈ Finset.range (m + 1), (a - r) + r = a := by
    intro r hr
    have : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    omega
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]

/-- Closed form of `∑_{r=0}^{m} (a - r)`. `m ≤ a` is exactly the condition under
which the truncated subtraction is honest. -/
theorem sum_range_sub (a m : ℕ) (h : m ≤ a) :
    ∑ r ∈ Finset.range (m + 1), (a - r) = (m + 1) * a - (m + 1) * m / 2 := by
  have hadd := sum_range_sub_add a m h
  have hgauss : (∑ r ∈ Finset.range (m + 1), r) * 2 = (m + 1) * m :=
    Finset.sum_range_id_mul_two (m + 1)
  omega

/-- The same, phrased on `sumRange` so it applies to a definition written with
the kernel-cheap helper. -/
theorem sumRange_sub (a m : ℕ) (h : m ≤ a) :
    sumRange (fun r => a - r) (m + 1) = (m + 1) * a - (m + 1) * m / 2 := by
  rw [sumRange_eq]; exact sum_range_sub a m h

/-! ### Nested sums: close the inner one

A nested `Finset.range` sum is the worst case, because the inner traversal runs
once per outer element. You do not need a closed form for the whole thing to get
most of the win -- closing only the inner sum takes the work from `O(outer *
inner)` to `O(outer)`, and where the inner body is affine that is just
`sum_range_sub` applied pointwise.

Given

```lean
def f (T YS S : ℕ) : ℕ :=
  ∑ y ∈ Finset.range (min T YS + 1),
    ∑ r ∈ Finset.range (min S (min (T-y) (YS-y)) + 1), (T+1-y-r)
```

define it with the inner sum already closed, and recover the original statement
as a lemma so existing proofs still apply:

```lean
def f (T YS S : ℕ) : ℕ :=
  sumRange (fun y =>
    let M := min S (min (T-y) (YS-y))
    (M+1) * (T+1-y) - (M+1) * M / 2) (min T YS + 1)

theorem f_eq (T YS S : ℕ) :
    f T YS S = ∑ y ∈ Finset.range (min T YS + 1),
      ∑ r ∈ Finset.range (min S (min (T-y) (YS-y)) + 1), (T+1-y-r) := by
  rw [f, sumRange_eq]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have h : min S (min (T-y) (YS-y)) ≤ T+1-y := by
    have : min S (min (T-y) (YS-y)) ≤ T - y :=
      le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
    omega
  exact (sum_range_sub (T+1-y) _ h).symm
```

Anything that previously unfolded `f` should be pointed at `f_eq` instead --
typically one `simp` argument or one `rw` per site.

Closing the outer sum too would need a case split on where `min` changes branch;
that is a much larger proof for a much smaller further gain. -/

end KernelEval
