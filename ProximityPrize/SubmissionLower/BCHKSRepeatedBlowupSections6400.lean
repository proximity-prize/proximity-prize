import ProximityPrize.SubmissionLower.BCHKSRepeatedSingularLine6400

/-!
# Degree-lowering section transform at a ramified affine coordinate

All rows in a fixed-coordinate agreement fibre pass through the same affine
value `a + z*b` at `x`.  Centering at `x`, subtracting that value, and dividing
by the centered variable lowers every section degree by one.  Agreement at
every other coordinate remains affine in `z` after a fixed rescaling.

This is the section side of the ramified blow-up `Y = a + Z*b + X*W`.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

variable {F : Type} [Field F]

/-- Center a polynomial section at `x`, subtract its prescribed value `y`,
and divide by the centered variable. -/
noncomputable def centeredSectionQuotient
    (P : F[X]) (x y : F) : F[X] :=
  (P.comp (Polynomial.C x + Polynomial.X) - Polynomial.C y) /ₘ
    Polynomial.X

/-- The centered numerator is exactly `X` times the quotient whenever the
section has the prescribed value at the base coordinate. -/
theorem X_mul_centeredSectionQuotient
    (P : F[X]) (x y : F) (hxy : P.eval x = y) :
    Polynomial.X * centeredSectionQuotient P x y =
      P.comp (Polynomial.C x + Polynomial.X) - Polynomial.C y := by
  unfold centeredSectionQuotient
  have hroot : Polynomial.IsRoot
      (P.comp (Polynomial.C x + Polynomial.X) - Polynomial.C y) 0 := by
    simp [Polynomial.IsRoot, hxy]
  simpa using
    (Polynomial.mul_divByMonic_eq_iff_isRoot
      (p := P.comp (Polynomial.C x + Polynomial.X) - Polynomial.C y)
      (a := (0 : F))).2 hroot

/-- Centering by a linear translation and subtracting a constant do not
increase degree. -/
theorem centeredSectionNumerator_natDegree_le
    (P : F[X]) (x y : F) :
    (P.comp (Polynomial.C x + Polynomial.X) - Polynomial.C y).natDegree ≤
      P.natDegree := by
  have hlinear : (Polynomial.C x + Polynomial.X : F[X]).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hcomp :
      (P.comp (Polynomial.C x + Polynomial.X)).natDegree ≤ P.natDegree := by
    calc
      _ ≤ P.natDegree *
          (Polynomial.C x + Polynomial.X : F[X]).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ hlinear
      _ = P.natDegree := by omega
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le hcomp (by simp))

/-- The ramified section transform lowers a degree-`k` witness to degree at
most `k-1`. -/
theorem centeredSectionQuotient_natDegree_le_pred
    (P : F[X]) (x y : F) (k : ℕ) (hP : P.natDegree ≤ k) :
    (centeredSectionQuotient P x y).natDegree ≤ k - 1 := by
  unfold centeredSectionQuotient
  rw [Polynomial.natDegree_divByMonic _ Polynomial.monic_X,
    Polynomial.natDegree_X]
  have hnum := centeredSectionNumerator_natDegree_le P x y
  have hnumk :
      (P.comp (Polynomial.C x + Polynomial.X) -
        Polynomial.C y).natDegree ≤ k := hnum.trans hP
  omega

/-- Evaluation form of the centered quotient identity. -/
theorem mul_eval_centeredSectionQuotient
    (P : F[X]) (x y δ : F) (hxy : P.eval x = y) :
    δ * (centeredSectionQuotient P x y).eval δ =
      P.eval (x + δ) - y := by
  have h := congrArg (fun Q : F[X] => Q.eval δ)
    (X_mul_centeredSectionQuotient P x y hxy)
  simpa [Polynomial.eval_comp] using h

/-- Agreement transport before division: a second affine received coordinate
becomes an affine numerator in the challenge. -/
theorem centeredSectionQuotient_affine_transport_mul
    (P : F[X]) (x w a b c d z : F)
    (hbase : P.eval x = a + z * b)
    (hother : P.eval w = c + z * d) :
    (w - x) *
        (centeredSectionQuotient P x (a + z * b)).eval (w - x) =
      (c - a) + z * (d - b) := by
  rw [mul_eval_centeredSectionQuotient P x (a + z * b) (w - x) hbase]
  rw [show x + (w - x) = w by ring, hother]
  ring

/-- Away from the base coordinate, the degree-lowered section still agrees
with an affine received line, after rescaling by the fixed displacement. -/
theorem centeredSectionQuotient_affine_transport
    (P : F[X]) (x w a b c d z : F)
    (hwx : w ≠ x)
    (hbase : P.eval x = a + z * b)
    (hother : P.eval w = c + z * d) :
    (centeredSectionQuotient P x (a + z * b)).eval (w - x) =
      (w - x)⁻¹ * (c - a) +
        z * ((w - x)⁻¹ * (d - b)) := by
  have hmul := centeredSectionQuotient_affine_transport_mul
    P x w a b c d z hbase hother
  have hδ : w - x ≠ 0 := sub_ne_zero.mpr hwx
  field_simp [hδ]
  linear_combination hmul

end ProximityPrize.SubmissionLower
