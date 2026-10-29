import ProximityPrize.SubmissionBinaryLower.P64C7Auxiliary
import ProximityPrize.SubmissionBinaryLower.P64C6Line

/-!
# Residual divisibility along the finite flow

At a point missing from a curve, the vertical factor has constant coefficient
coprime to the horizontal prime. Coefficient induction cancels that factor
without constructing an infinite implicit-function solution.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Residual

open Polynomial P64C6Coordinates P64C7Auxiliary BCHKSSubstitutionVanish

section Cancellation

variable {B : Type*} [CommRing B] [IsDomain B]

theorem cancel_coefficients (π : B) (hπ : Prime π) (s m : ℕ)
    (g h : PowerSeries B) (hunit : ¬ π ∣ PowerSeries.constantCoeff g)
    (hprod : ∀ ρ ≤ m, π ^ s ∣ PowerSeries.coeff ρ (g * h)) :
    ∀ ρ ≤ m, π ^ s ∣ PowerSeries.coeff ρ h := by
  classical
  intro ρ
  induction ρ using Nat.strong_induction_on with
  | h ρ ih =>
    intro hρ
    have hsum : π ^ s ∣ ∑ p ∈ (Finset.antidiagonal ρ).erase (0, ρ),
        PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 h := by
      apply Finset.dvd_sum
      intro p hp
      obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hp
      have he := Finset.mem_antidiagonal.mp hp
      have hlt : p.2 < ρ := by
        by_contra hn
        apply hne
        apply Prod.ext <;> omega
      exact dvd_mul_of_dvd_right (ih p.2 hlt (hlt.le.trans hρ)) _
    have hh := hprod ρ hρ
    rw [PowerSeries.coeff_mul,
      ← Finset.sum_erase_add _ _ (show (0, ρ) ∈ Finset.antidiagonal ρ by simp)] at hh
    have hc : π ^ s ∣ PowerSeries.coeff 0 g * PowerSeries.coeff ρ h := by
      simpa only [add_sub_cancel_left] using dvd_sub hh hsum
    exact hπ.pow_dvd_of_dvd_mul_left s
      (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hunit) hc

end Cancellation

variable {F : Type*} [Field F]

noncomputable local instance : CommRing (Polynomial F) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial F)) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial F))) := Polynomial.commRing

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

lemma theta_xLine (R : Tri) (P : F[X]) (x z : F) (m : ℕ) :
    theta R P z m (xLine x) = PowerSeries.C (Polynomial.X - Polynomial.C x) := by
  rw [theta_eq_curveEval]
  simp [xLine, reorder, P64C6Res.curveEval, P64C6Flow.Ev,
    Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_C_C]

lemma triEval_yLine (P y : F[X]) (z : F) :
    triEval (yLine y) z P = P - Polynomial.C (y.eval z) := by
  simp [yLine, triEval, specializeZ]

/-- A residual auxiliary contributes the full horizontal multiplicity at a missing point. -/
theorem theta_residual_order (R H : Tri) (x z : F) (P y : F[X]) (s m ρ : ℕ)
    (hflat : Residual R H x y s) (hmiss : P.eval x ≠ y.eval z)
    (hcurve : triEval R z P = 0) (hρ : ρ ≤ m) :
    (Polynomial.X - Polynomial.C x) ^ s ∣ PowerSeries.coeff ρ (theta R P z m H) := by
  obtain ⟨A, B, he⟩ := hflat
  let π : F[X] := Polynomial.X - Polynomial.C x
  let g := theta R P z m (yLine y) ^ s
  have hunit : ¬ π ∣ PowerSeries.constantCoeff g := by
    rw [Polynomial.dvd_iff_isRoot]
    change ¬ Polynomial.eval x (PowerSeries.constantCoeff g) = 0
    dsimp [g]
    rw [map_pow, constantCoeff_theta, triEval_yLine]
    simpa using pow_ne_zero s (sub_ne_zero.mpr hmiss)
  apply cancel_coefficients π (Polynomial.prime_X_sub_C x) s m g (theta R P z m H) hunit
    (fun k hk => ?_) ρ hρ
  have hmul : (PowerSeries.X : PowerSeries (F[X])) ^ (m + 1) ∣ theta R P z m (R * B) := by
    rw [map_mul]
    exact dvd_mul_of_dvd_left (theta_self R P z m hcurve) _
  have hz := PowerSeries.X_pow_dvd_iff.mp hmul k (by omega)
  have ht := congrArg (theta R P z m) he
  rw [map_mul, map_pow, map_add, map_mul, map_pow, theta_xLine] at ht
  change g * theta R P z m H = _ at ht
  rw [ht, map_add, hz, add_zero, ← map_pow, PowerSeries.coeff_C_mul]
  exact dvd_mul_right _ _

end P64C7Residual
end ProximityPrize.SubmissionBinaryLower
