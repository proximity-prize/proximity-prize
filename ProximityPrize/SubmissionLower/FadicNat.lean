import ProximityPrize.SubmissionLower.FadicGateDim
import ProximityPrize.SubmissionLower.FadicChunk

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

def termN (J T Θ q : ℕ) : ℕ := if 26 * q ≤ Θ then cappedCountN (padGrade Θ q) J T else 0

def natPrefix (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => natPrefix f n + f n

def fastCountN (B J T Θ : ℕ) : ℕ :=
  natPrefix (termN J T Θ) (flatLo B J) +
    (flatHi B J Θ - flatLo B J) * cappedCountN J J T +
    natPrefix (fun i => termN J T Θ (flatHi B J Θ + i)) (B + 1 - flatHi B J Θ)

def multN (σb σj σt bl bh jl jh r a : ℕ) : ℕ :=
  if bl ≤ depthB σb bh r a ∧ jl ≤ depthJ σj jh r a ∧ 26 * bl ≤ depthΘ bh jh a then
    fastCountN (depthB σb bh r a - bl) (depthJ σj jh r a - jl) ((r - a) * σt)
      (depthΘ bh jh a - 26 * bl)
  else 0

def depthDimN (σb σj σt bl bh jl jh r a : ℕ) : ℕ :=
  if DepthOK bh jh r a then
    fastCountN (depthB σb bh r a) (depthJ σj jh r a) ((r - a) * σt) (depthΘ bh jh a) -
      multN σb σj σt bl bh jl jh r a
  else 0

def fadicDimN (σb σj σt bl bh jl jh r : ℕ) : ℕ :=
  natPrefix (depthDimN σb σj σt bl bh jl jh r) (r / 3 + 1)

def plainDimN (σb σj σt r : ℕ) : ℕ :=
  fastCountN (min (r * σb) 4012) (min (r * σj) 1650) (r * σt) 131312

def gateDimN (S σb σj σt bl bh jl jh r : ℕ) : ℕ :=
  if IsFull σb σj σt r then S
  else max (plainDimN σb σj σt r) (fadicDimN σb σj σt bl bh jl jh r)

def rowLossN (S σb σj σt bl bh jl jh i : ℕ) : ℕ := S - gateDimN S σb σj σt bl bh jl jh (i + 1)

end FadicGate
