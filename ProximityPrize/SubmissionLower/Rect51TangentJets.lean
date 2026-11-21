import ProximityPrize.SubmissionLower.Rect51TangentSection

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace Rect51Tangent
noncomputable section
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3 (JetRing ordinate graphIdeal)
open HighCore82706Tangent_3_1 (velocity jetSeparant coefficientDerivative jetCoeffDerivative
  secondAlongVelocity velocityNumerator pureDen pureOrdinate pureDegree)
open HighCore82706Tangent_3_1_2 (reciprocalNumerator clearedAction sepAlong reverseEquation)
open K1_14 (Equation FX Seeds)
open scoped BigOperators
open private coefficientDerivative_zero from ProximityPrize.SubmissionLower.HighCore82706TangentDeps

private theorem second_bound {f : Equation} {s : Axes} (hf : SeedBound f s) :
    Bounded (secondAlongVelocity f) 2 s := by
  have hx := Bounded.C (SeedBound.coeffDiff (SeedBound.coeffDiff hf))
  have hxy := Bounded.C (SeedBound.coeffDiff (SeedBound.derivative hf))
  have hyy := Bounded.C (SeedBound.derivative (SeedBound.derivative hf))
  have h1 : Bounded (2 * velocity * Polynomial.C (coefficientDerivative f.derivative)) 1 s := by
    simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.cast_ofNat, Nat.zero_add, Nat.add_zero] using
      ((Bounded.nat 2).mul Bounded.velocity).mul hxy
  have h2 : Bounded (velocity ^ 2 * Polynomial.C f.derivative.derivative) 2 s := by
    simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.mul_one, Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
      (Bounded.velocity.pow 2).mul hyy
  exact ((hx.mono (by omega) (fun _ => le_rfl)).add (h1.mono (by omega) (fun _ => le_rfl))).add h2
private theorem numerator_bound {f : Equation} {s : Axes} (hf : SeedBound f s) (k : ℕ) :
    Bounded (velocityNumerator f k) (k+1) (k • s) := by
  have hsep := Bounded.C (SeedBound.derivative hf)
  have hxx := second_bound hf
  have hxy := Bounded.C (SeedBound.coeffDiff (SeedBound.derivative hf))
  have hyy := Bounded.C (SeedBound.derivative (SeedBound.derivative hf))
  induction k with
  | zero => simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, velocityNumerator, Nat.zero_mul, Nat.zero_add] using Bounded.velocity
  | succ k ih =>
    have h1 := ih.coeffDiff coefficientDerivative_zero (fun _ h => SeedBound.coeffDiff h)
    have h2 := ih.coeffDiff (Polynomial.derivative_zero (R := Seeds))
      (fun _ h => SeedBound.derivative h)
    have hsum : Bounded (jetCoeffDerivative coefficientDerivative (velocityNumerator f k) +
        velocity * jetCoeffDerivative Polynomial.derivative (velocityNumerator f k)) (k+2) (k • s) := by
      apply (h1.mono (Nat.le_succ _) (fun _ => le_rfl)).add
      simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Bounded.velocity.mul h2
    have h3 := hsep.mul hsum
    have h4 := hxx.mul ih.derivative
    have hs : Bounded (Polynomial.C (coefficientDerivative f.derivative) +
        velocity * Polynomial.C f.derivative.derivative) 1 s := by
      apply (hxy.mono (by omega) (fun _ => le_rfl)).add
      simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.add_zero, Nat.zero_add] using Bounded.velocity.mul hyy
    have h5 := ((Bounded.nat k).mul hs).mul ih
    have e : s + k • s = (k+1) • s := by rw [succ_nsmul, add_comm s]
    rw [velocityNumerator]
    apply Bounded.sub (Bounded.sub ?_ ?_) ?_
    · simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.zero_add, e] using h3
    · simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.add_sub_cancel, Nat.add_comm 2 k, e] using h4
    · simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, ← e] using h5
theorem reciprocal_bound {f : Equation} {s : Axes} (hf : SeedBound f s) (k : ℕ) :
    Bounded (reciprocalNumerator f k) (k+1) (k • s) := by
  have hsep := Bounded.C (SeedBound.derivative hf)
  have hB := second_bound hf
  have hxy := Bounded.C (SeedBound.coeffDiff (SeedBound.derivative hf))
  have hyy := Bounded.C (SeedBound.derivative (SeedBound.derivative hf))
  have hs : Bounded (sepAlong f) 1 s := by
    apply Bounded.add (Bounded.mono hxy (by omega) (fun _ => le_rfl))
    simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.zero_add, Nat.add_zero] using Bounded.mul Bounded.velocity hyy
  induction k with
  | zero => simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, reciprocalNumerator, Nat.zero_mul, Nat.zero_add] using Bounded.neg Bounded.velocity
  | succ k ih =>
    have h1 := Bounded.coeffDiff ih coefficientDerivative_zero (fun _ h => SeedBound.coeffDiff h)
    have h2 := Bounded.coeffDiff ih (Polynomial.derivative_zero (R := K1_14.Seeds))
      (fun _ h => SeedBound.derivative h)
    have hsum : Bounded (jetCoeffDerivative coefficientDerivative (reciprocalNumerator f k) +
        HighCore82706Tangent_3_1.velocity * jetCoeffDerivative Polynomial.derivative (reciprocalNumerator f k))
        (k+2) (k • s) := by
      apply Bounded.add (Bounded.mono h1 (Nat.le_succ _) (fun _ => le_rfl))
      simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Bounded.mul Bounded.velocity h2
    have h3 := Bounded.mul hsep hsum
    have h4 := Bounded.mul hB (Bounded.derivative ih)
    have h5 := Bounded.mul (Bounded.mul (Bounded.nat k) hs) ih
    have h6 := Bounded.mul (Bounded.mul (Bounded.mul (Bounded.nat (k+2)) hsep) Bounded.velocity) ih
    have e : s + k • s = (k+1) • s := by rw [succ_nsmul, add_comm s]
    have hA : Bounded (clearedAction f (reciprocalNumerator f k) -
        (k : JetRing) * sepAlong f * reciprocalNumerator f k) (k+2) ((k+1) • s) := by
      apply Bounded.sub (Bounded.sub ?_ ?_) ?_
      · simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, clearedAction, Nat.zero_add, e] using h3
      · simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.add_sub_cancel, Nat.add_comm 2 k, e] using h4
      · simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, ← e] using h5
    rw [reciprocalNumerator]
    apply Bounded.sub
    · simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.zero_add] using Bounded.mul Bounded.ordinate hA
    · simpa only [zero_add, add_zero, zero_nsmul, smul_zero, one_nsmul, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, ← e] using h6
end
end Rect51Tangent
