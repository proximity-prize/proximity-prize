# Submission helpers

Optional Lean files you may copy into your submission root. Nothing here is part
of the challenge and nothing here is imported by any target: a file reaches the
verifier only if you copy it in, at which point it is submission code like any
other and counts against the file and byte budgets.

## `KernelEval.lean`

Kernel-cheap equivalents for quantities `decide` would otherwise compute by
enumerating a `Finset`. Mathlib-only, and the same file for both tracks.

`by decide` hands the goal to the kernel, which discharges it by unfolding
definitions and never runs `simp`. So no lemma can make a `decide` cheaper —
only the definition it unfolds can. `Finset.range n` is a `Multiset`, hence a
`Quot` of a `List`, so each summand costs a `Quot.lift`/`List.rec` traversal
where a `Nat` recursion costs one addition.

- `sumRange` — write it where a definition a `decide` evaluates would use
  `∑ i ∈ Finset.range n, f i`. `sumRange_eq` rewrites it back to `Finset.sum`,
  so Mathlib lemmas still apply.
- `sum_range_sub` / `sumRange_sub` — closed form for an affine body, removing
  the traversal rather than making it cheaper per element.
- For a nested range sum, closing only the inner one takes the work from
  `O(outer × inner)` to `O(outer)` and is a short proof, since the inner body is
  usually affine. Closing the outer sum too needs a case split on where a `min`
  changes branch, for considerably less gain. The module docstring has the
  worked pattern.

## Using it

Copy the file beside `Solution.lean` in your submission root — not in a
subdirectory, since the root is flat. Then:

```lean
import ProximityPrize.SubmissionLower.KernelEval   -- or SubmissionUpper
open KernelEval
```

The declarations are in the `KernelEval` namespace, so `open` it or qualify them
as `KernelEval.sumRange`. No edit is needed for either track.
