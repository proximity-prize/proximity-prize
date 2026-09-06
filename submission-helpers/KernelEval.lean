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

/-- Close the inner sum of a nested range sum whose body is affine in the inner
index. Exact: the value is unchanged, only the traversal is gone. Prefer this to
any bound -- it cannot lose a case, because it is the same number.

`hK` is the honesty condition on the truncated subtraction, and is usually
immediate from how the inner bound was built. -/
theorem nested_inner_closed (a : ℕ → ℕ) (K : ℕ → ℕ) (n : ℕ)
    (hK : ∀ y ∈ Finset.range n, K y ≤ a y) :
    (∑ y ∈ Finset.range n, ∑ r ∈ Finset.range (K y + 1), (a y - r))
      = ∑ y ∈ Finset.range n, ((K y + 1) * a y - (K y + 1) * K y / 2) :=
  Finset.sum_congr rfl (fun y hy => sum_range_sub (a y) (K y) (hK y hy))

/-! ### Bounds instead of exact values

Reach for this only when the exact value cannot be closed. A closed form is the
same number, so it can never lose a case; a bound can, and then some call sites
need the exact predicate back. If the body is affine in the summation index,
close it and stop here.

The sharpest saving is not a cheaper way to compute a quantity -- it is not
computing it. A `decide` that compares a quantity against a threshold does not
need the quantity; it needs enough to settle the comparison. If the goal is
`cost x < limit`, any `bound` with `cost x ≤ bound x` settles it whenever
`bound x < limit`, and a closed-form `bound` costs the kernel O(1) where the
exact `cost` costs O(n) or worse -- multiplied by however many instances the
`decide` enumerates.

Keep both, and make the cheap one imply the expensive one. Then a goal is
discharged through the bound wherever it is tight enough, and falls back to the
exact predicate where it is not, with nothing weakened: the bounded predicate is
*stronger*, so anything it proves the exact one also holds. -/

/-- Every term bounded gives the whole sum bounded, and the bound has no
traversal left in it. -/
theorem sumRange_le_mul (f : ℕ → ℕ) (b : ℕ) (h : ∀ i, f i ≤ b) :
    ∀ n, sumRange f n ≤ n * b
  | 0 => by simp [sumRange]
  | n + 1 => by
      have hn := sumRange_le_mul f b h n
      have := h n
      simp [sumRange, Nat.succ_mul]
      omega

section BoundExample

/-- Stand-in for a quantity a `decide` would evaluate term by term. -/
private def cost (T : ℕ) : ℕ := sumRange (fun y => T + 1 - y) (T + 1)

/-- A closed form that dominates it. -/
private def costBound (T : ℕ) : ℕ := (T + 1) * (T + 1)

private theorem cost_le_costBound (T : ℕ) : cost T ≤ costBound T :=
  sumRange_le_mul _ (T + 1) (fun _ => by omega) (T + 1)

/-- The predicate you want. -/
private def Fits (T limit : ℕ) : Prop := cost T < limit

/-- The same predicate through the bound: strictly stronger, O(1) to decide. -/
private def FitsBounded (T limit : ℕ) : Prop := costBound T < limit

/-- The bridge. Use `FitsBounded` where the bound is tight enough; keep `Fits`
for the rest. -/
private theorem FitsBounded.toFits {T limit : ℕ} (h : FitsBounded T limit) :
    Fits T limit :=
  lt_of_le_of_lt (cost_le_costBound T) h

end BoundExample

/-! ## Keep a `decide` off `ℤ`

The kernel evaluates `Nat` literals on an accelerated path. `Int` has none: an
`Int` is `Int.ofNat`/`Int.negSucc`, so every `Int` step the kernel takes is a
constructor match wrapped around the same `Nat` work. A `decide` over `Int`
arithmetic pays that wrapper on every operation.

This is worth acting on in one case and not the other.

**Worth it: a comparison whose sign is fixed in the source.** `0 ≤ c - d * i`
over `ℤ`, with `c` and `d` naturals, is `d * i ≤ c` over `ℕ`. The `ℤ`
disappears completely and no sign bookkeeping is left behind. Predicates of the
shape "this affine expression is non-negative here" are the common instance.

**Not worth it: re-encoding signed arithmetic by hand.** Carrying a sign
alongside a magnitude and branching on it in every operation costs the kernel
more than `Int`'s own representation does. A general `ℤ`-to-`ℕ` rewrite of a
polynomial is a slowdown, not a speedup. Convert where the `ℤ` vanishes; leave
it alone where it does not. -/

/-- `0 ≤ c - d * i` over `ℤ` is `d * i ≤ c` over `ℕ`.

Use it to state a non-negativity test so the kernel never builds the `Int`. -/
theorem nonneg_sub_iff (c d i : ℕ) :
    (0 : ℤ) ≤ (c : ℤ) - (d : ℤ) * (i : ℤ) ↔ d * i ≤ c := by
  have h : ((d * i : ℕ) : ℤ) = (d : ℤ) * (i : ℤ) := by push_cast; rfl
  rw [← h]; omega

/-- The same for the `constant + slope * i` spelling with a non-positive slope. -/
theorem nonneg_sub_iff' (c d i : ℕ) :
    (0 : ℤ) ≤ (c : ℤ) + -((d : ℤ) * (i : ℤ)) ↔ d * i ≤ c := by
  have h : ((d * i : ℕ) : ℤ) = (d : ℤ) * (i : ℤ) := by push_cast; rfl
  rw [← h]; omega

/-! Given a predicate the kernel has to decide many times

```lean
structure Affine where
  constant : ℤ
  slope    : ℤ

def Affine.eval (a : Affine) (i : ℕ) : ℤ := a.constant + a.slope * i

def Ok (as : List Affine) (i : ℕ) : Prop := ∀ a ∈ as, 0 ≤ a.eval i
```

carry the magnitudes as naturals instead, so the decision is a `Nat`
comparison, and keep the original statement as a lemma:

```lean
structure Affine where
  constant : ℕ
  slope    : ℕ          -- the slope's magnitude; it is subtracted

def Affine.ok (a : Affine) (i : ℕ) : Bool := a.slope * i ≤ a.constant

def Ok (as : List Affine) (i : ℕ) : Prop := ∀ a ∈ as, a.ok i = true

theorem ok_iff (a : Affine) (i : ℕ) :
    a.ok i = true ↔ (0 : ℤ) ≤ (a.constant : ℤ) - (a.slope : ℤ) * (i : ℤ) := by
  rw [Affine.ok, nonneg_sub_iff]; simp
```

The gain is in `Affine.ok`; `ok_iff` keeps every proof that spoke about the
`ℤ` form. -/

end KernelEval
