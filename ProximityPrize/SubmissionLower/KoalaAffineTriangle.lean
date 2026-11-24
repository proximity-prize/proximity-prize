import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

set_option Elab.async false

set_option autoImplicit false

namespace KoalaAffineTriangle

open scoped BigOperators

def twiceTriangle (x : ℤ) : ℤ :=
  let q := max 0 x
  q * (q + 1)

private def polynomial (a d : ℤ) (n : ℕ) : ℤ :=
  let m : ℤ := n
  6 * m * a * (a + 1) + 3 * d * (2 * a + 1) * m * (m - 1) +
    d * d * m * (m - 1) * (2 * m - 1)

private def closed (a d : ℤ) (n : ℕ) : ℤ := polynomial a d n / 6

















private def firstPositive (a d : ℤ) : ℕ := ((-a)/d+1).toNat





private def fast (a d : ℤ) (n : ℕ) : ℤ :=
  if 0 < d then
    let j := min n (firstPositive a d)
    if j = n then 0 else closed (a+d*(j : ℤ)) d (n-j)
  else if d < 0 then
    closed a d (min n (firstPositive (-a) (-d)))
  else
    (n : ℤ) * twiceTriangle a


/-- Sum a positive triangular term using the unique sign crossing of the affine argument. -/
def sumFast (a d lo : ℤ) (n : ℕ) : ℤ := fast (a+d*lo) d n



end KoalaAffineTriangle
