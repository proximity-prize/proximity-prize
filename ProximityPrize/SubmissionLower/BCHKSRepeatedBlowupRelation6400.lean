import ProximityPrize.SubmissionLower.BCHKSRepeatedBlowupSections6400

/-!
# Ramified blow-up of the selected relation

For a bivariate relation `B(X,Y)`, the substitution

`X = x + X`, `Y = y + X*W`

turns every exact polynomial section through `(x,y)` into an exact section
in `W`.  Combined with `B = B_X = B_Y = 0` at the center, the transformed
relation has a common `X^2` content; removing that content is the next
degree-descent relation.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Translate the coefficient variable of a bivariate polynomial. -/
noncomputable def shiftRelationX
    {A : Type} [CommRing A] (B : A[X][Y]) (x : A) : A[X][Y] :=
  B.map (Polynomial.eval₂RingHom (Polynomial.C : A →+* A[X])
    (Polynomial.C x + Polynomial.X))

/-- The ramified substitution `X=x+X`, `Y=y+X*W`.  The outer polynomial
variable in the result represents `W`. -/
noncomputable def ramifiedSubstitute
    {A : Type} [CommRing A] (B : A[X][Y]) (x y : A) : A[X][Y] :=
  Polynomial.eval₂ (Polynomial.C : A[X] →+* A[X][Y])
    (Polynomial.C (Polynomial.C y) +
      Polynomial.C (Polynomial.X : A[X]) * Polynomial.X)
    (shiftRelationX B x)

@[simp]
theorem shiftRelationX_add
    {A : Type} [CommRing A] (B C : A[X][Y]) (x : A) :
    shiftRelationX (B + C) x = shiftRelationX B x + shiftRelationX C x := by
  simp [shiftRelationX]

@[simp]
theorem shiftRelationX_monomial
    {A : Type} [CommRing A] (n : ℕ) (c : A[X]) (x : A) :
    shiftRelationX (Polynomial.monomial n c) x =
      Polynomial.monomial n
        (c.comp (Polynomial.C x + Polynomial.X)) := by
  simp only [shiftRelationX, Polynomial.map_monomial]
  rfl

@[simp]
theorem ramifiedSubstitute_add
    {A : Type} [CommRing A] (B C : A[X][Y]) (x y : A) :
    ramifiedSubstitute (B + C) x y =
      ramifiedSubstitute B x y + ramifiedSubstitute C x y := by
  simp [ramifiedSubstitute]

@[simp]
theorem ramifiedSubstitute_monomial
    {A : Type} [CommRing A] (n : ℕ) (c : A[X]) (x y : A) :
    ramifiedSubstitute (Polynomial.monomial n c) x y =
      Polynomial.C (c.comp (Polynomial.C x + Polynomial.X)) *
        (Polynomial.C (Polynomial.C y) +
          Polynomial.C (Polynomial.X : A[X]) * Polynomial.X) ^ n := by
  simp [ramifiedSubstitute]

variable {F : Type} [Field F]

/-- The substituted root is precisely the shifted original section. -/
theorem ramified_root_substitution_eq_shift
    (P : F[X]) (x y : F) (hxy : P.eval x = y) :
    Polynomial.C y + Polynomial.X * centeredSectionQuotient P x y =
      P.comp (Polynomial.C x + Polynomial.X) := by
  have hmul := X_mul_centeredSectionQuotient P x y hxy
  linear_combination hmul

/-- Exact roots survive the ramified substitution while their section degree
drops by one. -/
theorem ramifiedSubstitute_eval_centeredSectionQuotient
    (B : F[X][Y]) (P : F[X]) (x y : F)
    (hxy : P.eval x = y) :
    (ramifiedSubstitute B x y).eval (centeredSectionQuotient P x y) =
      (B.eval P).comp (Polynomial.C x + Polynomial.X) := by
  have hroot := ramified_root_substitution_eq_shift P x y hxy
  induction B using Polynomial.induction_on' with
  | add B C hB hC =>
      simp [hB, hC]
  | monomial n c =>
      simp only [ramifiedSubstitute_monomial, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.mul_comp, Polynomial.pow_comp,
        Polynomial.eval_monomial]
      rw [hroot]

/-- In particular, an exact original section gives an exact degree-lowered
section of the ramified relation. -/
theorem ramifiedSubstitute_exact_root
    (B : F[X][Y]) (P : F[X]) (x y : F)
    (hxy : P.eval x = y) (hExact : B.eval P = 0) :
    (ramifiedSubstitute B x y).eval
      (centeredSectionQuotient P x y) = 0 := by
  rw [ramifiedSubstitute_eval_centeredSectionQuotient B P x y hxy,
    hExact]
  simp

/-- A polynomial and its first derivative vanishing at `x` make its translate
divisible by `X^2`. -/
theorem X_sq_dvd_comp_shift_of_eval_derivative_eq_zero
    {A : Type} [CommRing A] (p : A[X]) (x : A)
    (hzero : p.eval x = 0) (hderiv : p.derivative.eval x = 0) :
    Polynomial.X ^ 2 ∣ p.comp (Polynomial.C x + Polynomial.X) := by
  rw [show p.comp (Polynomial.C x + Polynomial.X) =
      Polynomial.taylor x p by
        simp only [Polynomial.taylor_apply]
        rw [add_comm]]
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  interval_cases d <;> simp [hzero, hderiv]

/-- The constant `W` coefficient of the ramified transform is the translate
of the original relation restricted to the center line `Y=y`. -/
theorem ramifiedSubstitute_coeff_zero
    {A : Type} [CommRing A] (B : A[X][Y]) (x y : A) :
    (ramifiedSubstitute B x y).coeff 0 =
      (B.eval (Polynomial.C y)).comp
        (Polynomial.C x + Polynomial.X) := by
  induction B using Polynomial.induction_on' with
  | add B C hB hC =>
      simp [hB, hC]
  | monomial n c =>
      simp [ramifiedSubstitute_monomial, Polynomial.coeff_zero_eq_eval_zero]

/-- The linear coefficient after substituting `a + b*X` is the directional
derivative `b * p'(a)`. -/
theorem coeff_one_comp_C_add_C_mul_X
    {A : Type} [CommRing A] (p : A[X]) (a b : A) :
    (p.comp (Polynomial.C a + Polynomial.C b * Polynomial.X)).coeff 1 =
      b * p.derivative.eval a := by
  calc
    (p.comp (Polynomial.C a + Polynomial.C b * Polynomial.X)).coeff 1 =
        ((Polynomial.taylor a p).comp
          (Polynomial.C b * Polynomial.X)).coeff 1 := by
            simp only [Polynomial.taylor_apply, Polynomial.comp_assoc]
            congr 2
            simp [add_comm]
    _ = (Polynomial.taylor a p).coeff 1 * b ^ 1 := by
          rw [Polynomial.comp_C_mul_X_coeff]
    _ = b * p.derivative.eval a := by simp [mul_comm]

/-- All coefficients after the affine substitution `a + b*X` carry the
corresponding power of the slope `b`. -/
theorem coeff_comp_C_add_C_mul_X
    {A : Type} [CommRing A] (p : A[X]) (a b : A) (n : ℕ) :
    (p.comp (Polynomial.C a + Polynomial.C b * Polynomial.X)).coeff n =
      (Polynomial.taylor a p).coeff n * b ^ n := by
  calc
    (p.comp (Polynomial.C a + Polynomial.C b * Polynomial.X)).coeff n =
        ((Polynomial.taylor a p).comp
          (Polynomial.C b * Polynomial.X)).coeff n := by
            simp only [Polynomial.taylor_apply, Polynomial.comp_assoc]
            congr 2
            simp [add_comm]
    _ = (Polynomial.taylor a p).coeff n * b ^ n := by
          rw [Polynomial.comp_C_mul_X_coeff]

/-- Differentiating in the outer variable commutes with translating the
coefficient variable and then restricting to `Y=y`. -/
theorem shiftRelationX_derivative_eval
    {A : Type} [CommRing A] (B : A[X][Y]) (x y : A) :
    (shiftRelationX B x).derivative.eval (Polynomial.C y) =
      (B.derivative.eval (Polynomial.C y)).comp
        (Polynomial.C x + Polynomial.X) := by
  induction B using Polynomial.induction_on' with
  | add B C hB hC => simp [hB, hC]
  | monomial n c =>
      simp [shiftRelationX_monomial, Polynomial.derivative_monomial]

/-- The linear `W` coefficient of the ramified transform is `X` times the
translate of the original `Y` partial along `Y=y`. -/
theorem ramifiedSubstitute_coeff_one
    {A : Type} [CommRing A] (B : A[X][Y]) (x y : A) :
    (ramifiedSubstitute B x y).coeff 1 =
      Polynomial.X *
        (B.derivative.eval (Polynomial.C y)).comp
          (Polynomial.C x + Polynomial.X) := by
  change ((shiftRelationX B x).comp
    (Polynomial.C (Polynomial.C y) +
      Polynomial.C (Polynomial.X : A[X]) * Polynomial.X)).coeff 1 = _
  rw [coeff_one_comp_C_add_C_mul_X,
    shiftRelationX_derivative_eval]

/-- The `n`th `W` coefficient of a ramified transform is divisible by
`X^n`.  Thus only coefficients zero and one need singularity information
to prove common quadratic content. -/
theorem X_pow_dvd_ramifiedSubstitute_coeff
    {A : Type} [CommRing A] (B : A[X][Y]) (x y : A) (n : ℕ) :
    Polynomial.X ^ n ∣ (ramifiedSubstitute B x y).coeff n := by
  change Polynomial.X ^ n ∣
    ((shiftRelationX B x).comp
      (Polynomial.C (Polynomial.C y) +
        Polynomial.C (Polynomial.X : A[X]) * Polynomial.X)).coeff n
  rw [coeff_comp_C_add_C_mul_X]
  exact dvd_mul_left _ _

/-- A single zero at `x` makes the translate divisible by `X`. -/
theorem X_dvd_comp_shift_of_eval_eq_zero
    {A : Type} [CommRing A] (p : A[X]) (x : A)
    (hzero : p.eval x = 0) :
    Polynomial.X ∣ p.comp (Polynomial.C x + Polynomial.X) := by
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp]
  simp [hzero]

/-- If a relation and both first partials vanish at `(x,y)`, its ramified
transform has common `X^2` content across every `W` coefficient. -/
theorem C_X_sq_dvd_ramifiedSubstitute_of_singular
    {A : Type} [CommRing A] (B : A[X][Y]) (x y : A)
    (hzero : (B.eval (Polynomial.C y)).eval x = 0)
    (hX : (B.eval (Polynomial.C y)).derivative.eval x = 0)
    (hY : (B.derivative.eval (Polynomial.C y)).eval x = 0) :
    Polynomial.C (Polynomial.X ^ 2) ∣ ramifiedSubstitute B x y := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro n
  rcases n with _ | _ | n
  · rw [ramifiedSubstitute_coeff_zero]
    exact X_sq_dvd_comp_shift_of_eval_derivative_eq_zero _ _ hzero hX
  · rw [ramifiedSubstitute_coeff_one]
    simpa [pow_two] using
      (mul_dvd_mul_left Polynomial.X
        (X_dvd_comp_shift_of_eval_eq_zero _ _ hY))
  · exact (pow_dvd_pow Polynomial.X (by omega)).trans
      (X_pow_dvd_ramifiedSubstitute_coeff B x y (n + 2))

/-- Translation of the coefficient variable is injective. -/
theorem shiftRelationX_eq_zero_iff
    {A : Type} [CommRing A] (B : A[X][Y]) (x : A) :
    shiftRelationX B x = 0 ↔ B = 0 := by
  unfold shiftRelationX
  apply Polynomial.map_eq_zero_iff
  intro p q hpq
  apply Polynomial.taylor_injective x
  change p.comp (Polynomial.C x + Polynomial.X) =
    q.comp (Polynomial.C x + Polynomial.X) at hpq
  simpa only [Polynomial.taylor_apply, add_comm] using hpq

/-- The ramified coordinate change is injective: a nonzero relation cannot
collapse to zero under `X=x+X`, `Y=y+X*W`. -/
theorem ramifiedSubstitute_eq_zero_iff
    {A : Type} [CommRing A] (B : A[X][Y]) (x y : A) :
    ramifiedSubstitute B x y = 0 ↔ B = 0 := by
  change (shiftRelationX B x).comp
      (Polynomial.C (Polynomial.C y) +
        Polynomial.C (Polynomial.X : A[X]) * Polynomial.X) = 0 ↔ _
  rw [show (shiftRelationX B x).comp
      (Polynomial.C (Polynomial.C y) +
        Polynomial.C (Polynomial.X : A[X]) * Polynomial.X) =
      (Polynomial.taylor (Polynomial.C y) (shiftRelationX B x)).comp
        (Polynomial.C (Polynomial.X : A[X]) * Polynomial.X) by
    simp only [Polynomial.taylor_apply, Polynomial.comp_assoc]
    congr 2
    simp [add_comm]]
  rw [Polynomial.comp_C_mul_X_eq_zero_iff
      (Polynomial.monic_X.mem_nonZeroDivisors),
    Polynomial.taylor_eq_zero, shiftRelationX_eq_zero_iff]

/-- The quadratic content can be removed without annihilating a nonzero
relation.  This packages the deflated relation existentially, avoiding any
choice of polynomial division algorithm in the coefficient ring. -/
theorem exists_nonzero_ramifiedDeflation
    {A : Type} [CommRing A] (B : A[X][Y]) (x y : A)
    (hB : B ≠ 0)
    (hzero : (B.eval (Polynomial.C y)).eval x = 0)
    (hX : (B.eval (Polynomial.C y)).derivative.eval x = 0)
    (hY : (B.derivative.eval (Polynomial.C y)).eval x = 0) :
    ∃ Q : A[X][Y], Q ≠ 0 ∧
      ramifiedSubstitute B x y =
        Polynomial.C (Polynomial.X ^ 2) * Q := by
  obtain ⟨Q, hQ⟩ :=
    C_X_sq_dvd_ramifiedSubstitute_of_singular B x y hzero hX hY
  refine ⟨Q, ?_, hQ⟩
  intro hQzero
  apply hB
  rw [← ramifiedSubstitute_eq_zero_iff B x y, hQ, hQzero, mul_zero]

/-- Translating the coefficient variable commutes with a coefficient-ring
map. -/
theorem map_shiftRelationX
    {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (R : A[X][Y]) (x : A) :
    (shiftRelationX R x).map (Polynomial.mapRingHom f) =
      shiftRelationX (R.map (Polynomial.mapRingHom f)) (f x) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS => simp [hR, hS]
  | monomial n c =>
      simp [shiftRelationX_monomial, Polynomial.map_comp]

/-- The full ramified substitution commutes with specializing the base
coefficient ring. -/
theorem map_ramifiedSubstitute
    {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (R : A[X][Y]) (x y : A) :
    (ramifiedSubstitute R x y).map (Polynomial.mapRingHom f) =
      ramifiedSubstitute (R.map (Polynomial.mapRingHom f)) (f x) (f y) := by
  change ((shiftRelationX R x).comp
      (Polynomial.C (Polynomial.C y) +
        Polynomial.C (Polynomial.X : A[X]) * Polynomial.X)).map
        (Polynomial.mapRingHom f) = _
  rw [Polynomial.map_comp, map_shiftRelationX]
  simp [ramifiedSubstitute, Polynomial.comp]

end ProximityPrize.SubmissionLower
