import ProximityPrize.SubmissionLower.BCHKSCoreQuotientHenselAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSCoreTransformFiberSetup6400

open Polynomial Polynomial.Bivariate
open BCHKSCoreQuotientHenselAudit6400

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
Fiberwise setup for the common-core affine root transform.  At a center
`x0` outside the locator roots, the root change has unit slope.  Hence it is
an automorphism of the specialized outer polynomial ring: primitivity and
outer degree are preserved, and simple roots transfer with slope multiplied
by the nonzero locator value.
-/

/-- Specializing the coordinate variable turns the core substitution into
an affine polynomial in the root variable over `F[Z]`. -/
theorem triSpecializeX_coreRootSubstitution
    {F : Type*} [Field F] (B0 B1 G : F[X]) (x0 : F) :
    triSpecializeX (coreRootSubstitution B0 B1 G) x0 =
      Polynomial.C
          (Polynomial.C (B0.eval x0) +
            Polynomial.X * Polynomial.C (B1.eval x0)) +
        Polynomial.C (Polynomial.C (G.eval x0)) * Polynomial.X := by
  simp [coreRootSubstitution, triSpecializeX, liftMiddle,
    Polynomial.eval_map]
  rw [mul_comm]

/-- Coordinate specialization commutes with the outer root composition. -/
theorem triSpecializeX_coreRootTransform
    {F : Type*} [Field F]
    (R : F[X][X][Y]) (B0 B1 G : F[X]) (x0 : F) :
    triSpecializeX (coreRootTransform R B0 B1 G) x0 =
      (triSpecializeX R x0).comp
        (Polynomial.C
            (Polynomial.C (B0.eval x0) +
              Polynomial.X * Polynomial.C (B1.eval x0)) +
          Polynomial.C (Polynomial.C (G.eval x0)) * Polynomial.X) := by
  rw [coreRootTransform, triSpecializeX, Polynomial.map_comp]
  rw [show Polynomial.map
      (Polynomial.evalRingHom (Polynomial.C x0))
        (coreRootSubstitution B0 B1 G) =
      Polynomial.C
          (Polynomial.C (B0.eval x0) +
            Polynomial.X * Polynomial.C (B1.eval x0)) +
        Polynomial.C (Polynomial.C (G.eval x0)) * Polynomial.X by
      simpa [triSpecializeX] using
        triSpecializeX_coreRootSubstitution B0 B1 G x0]
  rfl

/-- Primitivity is preserved by an affine root change with invertible
slope.  This is the content-control fact needed by Hensel setup. -/
theorem Polynomial.IsPrimitive.comp_C_mul_X_add_C
    {A : Type*} [CommRing A]
    {p : A[X]} (hp : p.IsPrimitive) (a b : A) [Invertible a] :
    (p.comp (Polynomial.C a * Polynomial.X + Polynomial.C b)).IsPrimitive := by
  intro r hr
  apply hp r
  have h :=
    (Polynomial.dvd_comp_C_mul_X_add_C_iff
      (Polynomial.C r) p a b).mp hr
  simpa using h

/-- The transformed coordinate specialization is primitive whenever the
original specialization is and the chosen center avoids the core locator. -/
theorem triSpecializeX_coreRootTransform_isPrimitive
    {F : Type*} [Field F]
    (R : F[X][X][Y]) (B0 B1 G : F[X]) (x0 : F)
    (hprimitive : (triSpecializeX R x0).IsPrimitive)
    (hGx : G.eval x0 ≠ 0) :
    (triSpecializeX (coreRootTransform R B0 B1 G) x0).IsPrimitive := by
  let a : F[X] := Polynomial.C (G.eval x0)
  let b : F[X] :=
    Polynomial.C (B0.eval x0) +
      Polynomial.X * Polynomial.C (B1.eval x0)
  have ha : a ≠ 0 := by
    simpa [a] using hGx
  letI : Invertible a :=
    (Polynomial.isUnit_C.mpr hGx.isUnit).invertible
  rw [triSpecializeX_coreRootTransform]
  have hp := Polynomial.IsPrimitive.comp_C_mul_X_add_C
    hprimitive a b
  simpa [a, b, add_comm] using hp

/-- At a locator-good center the coordinate-specialized transformed factor
has exactly the same outer degree as the original specialization. -/
theorem triSpecializeX_coreRootTransform_natDegree
    {F : Type*} [Field F]
    (R : F[X][X][Y]) (B0 B1 G : F[X]) (x0 : F)
    (hGx : G.eval x0 ≠ 0) :
    (triSpecializeX (coreRootTransform R B0 B1 G) x0).natDegree =
      (triSpecializeX R x0).natDegree := by
  let a : F[X] := Polynomial.C (G.eval x0)
  let b : F[X] :=
    Polynomial.C (B0.eval x0) +
      Polynomial.X * Polynomial.C (B1.eval x0)
  have ha : a ≠ 0 := by
    simpa [a] using hGx
  have hinner :
      (Polynomial.C b + Polynomial.C a * Polynomial.X).natDegree = 1 := by
    rw [add_comm]
    exact Polynomial.natDegree_linear ha
  rw [triSpecializeX_coreRootTransform]
  change ((triSpecializeX R x0).comp
      (Polynomial.C b + Polynomial.C a * Polynomial.X)).natDegree = _
  rw [Polynomial.natDegree_comp, hinner, Nat.mul_one]

/-- Simple roots transfer through a polynomial affine root substitution.
The new outer slope is the old slope multiplied by `G(x0)`. -/
theorem isSimpleRootAt_comp_polynomialAffine
    {F : Type*} [Field F]
    (R : F[X][Y]) (B G : F[X]) (x0 q0 : F)
    (hGx : G.eval x0 ≠ 0)
    (hsimple : FiniteHensel.IsSimpleRootAt R x0
      (B.eval x0 + G.eval x0 * q0)) :
    FiniteHensel.IsSimpleRootAt
      (R.comp (Polynomial.C B + Polynomial.C G * Polynomial.X)) x0 q0 := by
  unfold FiniteHensel.IsSimpleRootAt FiniteHensel.ySlope at hsimple ⊢
  constructor
  · rw [Polynomial.eval₂_comp]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_C,
      Polynomial.eval₂_mul, Polynomial.eval₂_X]
    simpa [Polynomial.eval_add, Polynomial.eval_mul] using hsimple.1
  · rw [Polynomial.derivative_comp]
    simp only [Polynomial.derivative_add, Polynomial.derivative_C,
      zero_add, Polynomial.derivative_C_mul_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_comp, Polynomial.eval₂_add,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    simpa [Polynomial.eval_add, Polynomial.eval_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      mul_ne_zero hsimple.2 hGx

/-- Benchmark-oriented simple-root adapter for the core transform. -/
theorem coreRootTransform_isSimpleRootAt
    {F : Type*} [Field F]
    (R : F[X][X][Y]) (B0 B1 G Q : F[X]) (x0 z : F)
    (hGx : G.eval x0 ≠ 0)
    (hsimple : FiniteHensel.IsSimpleRootAt (triSpecializeZ R z) x0
      ((B0 + Polynomial.C z * B1 + G * Q).eval x0)) :
    FiniteHensel.IsSimpleRootAt
      (triSpecializeZ (coreRootTransform R B0 B1 G) z) x0 (Q.eval x0) := by
  rw [coreRootTransform, triSpecializeZ, Polynomial.map_comp]
  rw [show Polynomial.map
      (Polynomial.mapRingHom (Polynomial.evalRingHom z))
        (coreRootSubstitution B0 B1 G) =
      Polynomial.C (B0 + Polynomial.C z * B1) +
        Polynomial.C G * Polynomial.X by
      simpa [triSpecializeZ] using
        triSpecializeZ_coreRootSubstitution B0 B1 G z]
  apply isSimpleRootAt_comp_polynomialAffine
  · exact hGx
  · change FiniteHensel.IsSimpleRootAt
      (Polynomial.map
        (Polynomial.mapRingHom (Polynomial.evalRingHom z)) R) x0
      ((B0 + Polynomial.C z * B1 + G * Q).eval x0) at hsimple
    simpa [Polynomial.eval_add, Polynomial.eval_mul] using hsimple

end BCHKSCoreTransformFiberSetup6400
end ProximityPrize.SubmissionLower
