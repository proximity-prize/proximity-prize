import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect

-- merged module KoalaAffineTriangle
section Merged_KoalaAffineTriangle

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

end Merged_KoalaAffineTriangle

-- merged module KoalaPiecewiseTriangle
section Merged_KoalaPiecewiseTriangle

set_option autoImplicit false
set_option Elab.async false

namespace KoalaPiecewiseTriangle
open Finset
open scoped BigOperators

structure Line where
  a : ℤ
  d : ℤ

def Line.at (f : Line) (x : ℤ) : ℤ := f.a + f.d*x

def Line.sub (f g : Line) : Line := ⟨f.a-g.a,f.d-g.d⟩

inductive Expr
  | affine (f : Line)
  | lower (f g : Expr)
  | upper (f g : Expr)
  | sub (f g : Expr)

def Expr.at : Expr → ℤ → ℤ
  | .affine f, x => f.at x
  | .lower f g, x => min (f.at x) (g.at x)
  | .upper f g, x => max (f.at x) (g.at x)
  | .sub f g, x => f.at x - g.at x

def Expr.const (a : ℤ) : Expr := .affine ⟨a,0⟩

private def ordered (f g : Line) (lo hi : ℤ) : Prop :=
  f.at lo ≤ g.at lo ∧ f.at hi ≤ g.at hi

private instance (f g : Line) (lo hi : ℤ) : Decidable (ordered f g lo hi) := by
  unfold ordered
  infer_instance









structure BandCuts where
  l0 : ℤ
  q1 : ℤ
  first : ℤ
  last : ℤ



private def lineCutSum (b : BandCuts) (l q : Line) (k lo : ℤ) (n : ℕ) : ℤ :=
  let sum := KoalaAffineTriangle.sumFast
  sum (l.a-k-q.a) (l.d-q.d) lo n -
    sum (b.l0-k-q.a) (-q.d) lo n -
    (sum (l.a-k-b.q1) l.d lo n -
      (n : ℤ) * KoalaAffineTriangle.twiceTriangle (b.l0-k-b.q1))


def lineBandSum (b : BandCuts) (l q : Line) (lo : ℤ) (n : ℕ) : ℤ :=
  lineCutSum b l q b.first lo n - lineCutSum b l q b.last lo n









end KoalaPiecewiseTriangle

end Merged_KoalaPiecewiseTriangle

-- merged module Low48PrimaryPivotAggregate
section Merged_Low48PrimaryPivotAggregate

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Low48PrimaryPivot
open K1_13_2_3 Finset KoalaPiecewiseTriangle
open scoped BigOperators

def contactExpr (c f r : ℕ) : Expr :=
  .lower (.const (1650-(f : ℤ)))
    (.lower (.affine ⟨3300-2*(r : ℤ)-3*(c : ℤ)-4*(f : ℤ),-5⟩)
      (.lower (.affine ⟨4950-3*(r : ℤ)-5*(c : ℤ)-7*(f : ℤ),-9⟩)
        (.affine ⟨1650-(r : ℤ)-(c : ℤ)-(f : ℤ)+(1650-(c : ℤ)-3*(f : ℤ))/2,-3⟩)))

theorem contactExpr_eq (c f r t : ℕ) (hr : r < 3)
    (h : (Triple.mk (3*t+r) c f).index ≤ 1650) :
    (contactExpr c f r).at t = ((Triple.mk (3*t+r) c f).contact : ℤ) := by
  rw [contact_eq]
  simp only [contactExpr, Expr.at, Expr.const, Line.at, zero_mul, add_zero, Triple.room, Triple.index] at *
  omega












end Low48PrimaryPivot

end Merged_Low48PrimaryPivotAggregate
