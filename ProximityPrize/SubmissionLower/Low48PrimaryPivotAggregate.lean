import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect
import ProximityPrize.SubmissionLower.KoalaPiecewiseTriangle

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Low48PrimaryPivot
open K1_13_2_3 Finset KoalaPiecewiseTriangle
open scoped BigOperators

private def contactExpr (c f r : ℕ) : Expr :=
  .lower (.const (1650-(f : ℤ)))
    (.lower (.affine ⟨3300-2*(r : ℤ)-3*(c : ℤ)-4*(f : ℤ),-5⟩)
      (.lower (.affine ⟨4950-3*(r : ℤ)-5*(c : ℤ)-7*(f : ℤ),-9⟩)
        (.affine ⟨1650-(r : ℤ)-(c : ℤ)-(f : ℤ)+(1650-(c : ℤ)-3*(f : ℤ))/2,-3⟩)))

private theorem contactExpr_eq (c f r t : ℕ) (hr : r < 3)
    (h : (Triple.mk (3*t+r) c f).index ≤ 1650) :
    (contactExpr c f r).at t = ((Triple.mk (3*t+r) c f).contact : ℤ) := by
  rw [contact_eq]
  simp only [contactExpr, Expr.at, Expr.const, Line.at, zero_mul, add_zero, Triple.room, Triple.index] at *
  omega












end Low48PrimaryPivot
