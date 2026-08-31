import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactLocalDivisibility

 











namespace ProximityPrize.SubmissionLower.ContactSecondContactLocalDivisibility6660Research

open Polynomial

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K]

 
def secondContactResidual (P : K[X]) (x : K) : K[X] :=
  Polynomial.taylor x P - Polynomial.C (P.eval x) -
    (Polynomial.X : K[X]) * Polynomial.taylor x (Polynomial.derivative P) +
      (Polynomial.C ((2 : K)⁻¹) *
        Polynomial.taylor x (Polynomial.derivative (Polynomial.derivative P))) *
          (Polynomial.X : K[X]) ^ 2

private theorem taylor_coeff_eq_derivative_div_factorial
    (P : K[X]) (x : K) (j : ℕ) (hfactorial : (j.factorial : K) ≠ 0) :
    (Polynomial.taylor x P).coeff j =
      (Polynomial.derivative^[j] P).eval x / (j.factorial : K) := by
  have hpoly : (j.factorial : Polynomial K) * Polynomial.hasseDeriv j P =
      Polynomial.derivative^[j] P := by
    have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) j) P
    change j.factorial • (Polynomial.hasseDeriv j P) =
      Polynomial.derivative^[j] P at h
    simpa only [nsmul_eq_mul] using h
  have hvalue := congrArg (Polynomial.evalRingHom x) hpoly
  simp only [map_mul, map_natCast] at hvalue
  change (j.factorial : K) * (Polynomial.hasseDeriv j P).eval x =
    (Polynomial.derivative^[j] P).eval x at hvalue
  rw [Polynomial.taylor_coeff]
  apply (eq_div_iff hfactorial).mpr
  simpa only [mul_comm] using hvalue

private theorem taylor_coeff_two (P : K[X]) (x : K)
    (h2 : (2 : K) ≠ 0) :
    (Polynomial.taylor x P).coeff 2 =
      (2 : K)⁻¹ * (Polynomial.derivative (Polynomial.derivative P)).eval x := by
  have h := taylor_coeff_eq_derivative_div_factorial P x 2 (by norm_num [h2])
  have hfac : ((Nat.factorial 2 : ℕ) : K) = (2 : K) := by norm_num
  rw [hfac] at h
  simpa only [div_eq_inv_mul, Function.iterate_succ_apply,
    Function.iterate_zero_apply] using h

private theorem coeff_secondContactResidual_zero (P : K[X]) (x : K) :
    (secondContactResidual P x).coeff 0 = 0 := by
  simp [secondContactResidual]

private theorem coeff_secondContactResidual_one (P : K[X]) (x : K) :
    (secondContactResidual P x).coeff 1 = 0 := by
  simp [secondContactResidual, Polynomial.coeff_mul_X_pow']

 
theorem coeff_secondContactResidual_two (P : K[X]) (x : K)
    (h2 : (2 : K) ≠ 0) :
    (secondContactResidual P x).coeff 2 = 0 := by
  rw [secondContactResidual]
  simp [Polynomial.coeff_mul_X_pow', taylor_coeff_two P x h2]
  have hinv : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by
    calc
      (2 : K)⁻¹ + (2 : K)⁻¹ = (2 : K)⁻¹ * (2 : K) := by ring
      _ = 1 := inv_mul_cancel₀ h2
  calc
    (2 : K)⁻¹ * (Polynomial.derivative (Polynomial.derivative P)).eval x -
          (Polynomial.derivative (Polynomial.derivative P)).eval x +
          (2 : K)⁻¹ * (Polynomial.derivative (Polynomial.derivative P)).eval x =
        ((2 : K)⁻¹ + (2 : K)⁻¹ - 1) *
          (Polynomial.derivative (Polynomial.derivative P)).eval x := by ring
    _ = 0 := by rw [hinv]; ring

 

theorem X_cube_dvd_secondContactResidual (P : K[X]) (x : K)
    (h2 : (2 : K) ≠ 0) :
    (Polynomial.X : K[X]) ^ 3 ∣ secondContactResidual P x := by
  rw [Polynomial.X_pow_dvd_iff]
  intro j hj
  interval_cases j
  · exact coeff_secondContactResidual_zero P x
  · exact coeff_secondContactResidual_one P x
  · exact coeff_secondContactResidual_two P x h2

 
theorem exists_secondContactQuotient (P : K[X]) (x : K)
    (h2 : (2 : K) ≠ 0) :
    ∃ B : K[X],
      Polynomial.taylor x P =
        Polynomial.C (P.eval x) +
          (Polynomial.X : K[X]) * Polynomial.taylor x (Polynomial.derivative P) -
          Polynomial.C ((2 : K)⁻¹) * (Polynomial.X : K[X]) ^ 2 *
            Polynomial.taylor x (Polynomial.derivative (Polynomial.derivative P)) +
            (Polynomial.X : K[X]) ^ 3 * B := by
  obtain ⟨B, hB⟩ := X_cube_dvd_secondContactResidual P x h2
  refine ⟨B, ?_⟩
  change secondContactResidual P x = (Polynomial.X : K[X]) ^ 3 * B at hB
  dsimp only [secondContactResidual] at hB
  linear_combination hB

end

end ProximityPrize.SubmissionLower.ContactSecondContactLocalDivisibility6660Research

#print axioms ProximityPrize.SubmissionLower.ContactSecondContactLocalDivisibility6660Research.X_cube_dvd_secondContactResidual
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactLocalDivisibility6660Research.exists_secondContactQuotient
