import ProximityPrize.SubmissionLower.FadicGateDim

set_option Elab.async false

/-!
# A Nat-only evaluator for the gate certificate

The kernel evaluates `Nat` literals on its accelerated path and `Int` on none.  This file mirrors
the evaluation chain of `FadicGateDim` in `ℕ`: truncated subtraction stands for every
`max 0 (…)`, and the inner subtractions of the accepted counting formulas never truncate because
each of them is a cardinality.  `rowLossN_eq` identifies the two once, generically.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2 (cappedCount cumulative denominator)
open scoped BigOperators
open Finset

/-- The accepted `denominator` at a natural argument, with `q = n / 6`, `r = n % 6`. -/
def denomQR (q r : ℕ) : ℕ :=
  1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)

def denomN (n : ℕ) : ℕ := denomQR (n / 6) (n % 6)

/-- `denominator (v - k)`, which vanishes for a negative argument. -/
def denomSub (v k : ℕ) : ℕ := if k ≤ v then denomN (v - k) else 0

def cumAux (d v : ℕ) : ℕ :=
  (denomN v + denomSub v (2 * d + 3) + denomSub v (2 * d + 4) + denomSub v (2 * d + 5)) -
    (denomSub v (d + 1) + denomSub v (d + 2) + denomSub v (d + 3) + denomSub v (3 * d + 6))

def cumulativeN (d u : ℕ) : ℕ := cumAux d (min u (3 * d))

/-- The accepted `cappedCount` at natural arguments.  The subtracted count is tested on the
index first: it vanishes whenever the top bound is implied by the index bound. -/
def cappedCountN (d u t : ℕ) : ℕ :=
  cumulativeN d u -
    (if 3 * (t + 1) ≤ u then (if t + 1 ≤ d then cumulativeN (d - (t + 1)) (u - 3 * (t + 1))
      else 0) else 0)










end FadicGate
