import ProximityPrize.SubmissionBinaryLower.P64C6Coordinates

/-!
# Spatial degree bounds for the finite flow

The coefficient of order `ρ` after flow evaluation has degree at most
`W + 2ρ(w - D)`. The zero polynomial is treated separately so the bound also
has its intended meaning when an intermediate integer bound is negative.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Degree

open Polynomial P64C6Flow P64C6Theta P64C6Coordinates

variable {F : Type*} [Field F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

lemma natDegree_swap_coeff_le (p : Polynomial (Polynomial F)) (b : ℕ) :
    ((Polynomial.Bivariate.swap p).coeff b).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro a ha
  rw [coeff_swap, Polynomial.coeff_eq_zero_of_natDegree_lt ha, Polynomial.coeff_zero]

lemma reorder_degree (R : Tri) (D W : ℕ) (hR : wd R D ≤ W) :
    (((degGrading F).poly 0).poly D).mem W (reorder R) := by
  intro a b
  simp only [reorder, Polynomial.coe_mapRingHom, coeff_map]
  change (degGrading F).mem ((W : ℤ) - a * D - b * 0)
    (((Polynomial.Bivariate.swap (R.coeff a)).coeff b))
  rw [mul_zero, sub_zero]
  by_cases hz : (Polynomial.Bivariate.swap (R.coeff a)).coeff b = 0
  · exact Or.inl hz
  right
  have ha : R.coeff a ≠ 0 := by
    intro h
    simp [h] at hz
  have h1 := natDegree_swap_coeff_le (R.coeff a) b
  have h2 := (P64Caps.Weighted.coeffWeight_le_of_ne R D a ha).trans hR
  have h1' : (((Polynomial.Bivariate.swap (R.coeff a)).coeff b).natDegree : ℤ) ≤
      (R.coeff a).natDegree := by exact_mod_cast h1
  have h2' : ((R.coeff a).natDegree : ℤ) + D * a ≤ W := by exact_mod_cast h2
  nlinarith

/-- The Taylor coefficient of `V^a W^b` has spatial degree at most `W - aD`. -/
lemma center_degree (R : Tri) (P : F[X]) (z : F) (D W : ℕ)
    (hR : wd R D ≤ W) (hP : P.natDegree ≤ D) (a b : ℕ) :
    (degGrading F).mem ((W : ℤ) - a * D) (((center P z R).coeff a).coeff b) := by
  have hc : (((degGrading F).poly 0).poly D).mem W (center P z R) := by
    apply shift_mem (reorder_degree R D W hR)
    · exact Or.inr (by simp)
    · exact Or.inr (by exact_mod_cast hP)
  have h := hc a b
  simpa [Grading.poly] using h

/-- The derivative along the curve has spatial degree at most `w - D`. -/
lemma derivativeAlong_degree (R : Tri) (P : F[X]) (z : F) (D w : ℕ)
    (hR : wd R D ≤ w) (hP : P.natDegree ≤ D) :
    (degGrading F).mem ((w : ℤ) - D) (derivativeAlong R P z) := by
  rw [derivativeAlong, ← center_coeff_one]
  simpa using center_degree R P z D w hR hP 1 0

/-- The complete linear degree profile of the finite flow. -/
theorem theta_degree (R H : Tri) (P : F[X]) (z : F) (D w W m : ℕ)
    (hR : wd R D ≤ w) (hH : wd H D ≤ W) (hP : P.natDegree ≤ D) :
    Prof (degGrading F) W (2 * ((w : ℤ) - D)) (theta R P z m H) := by
  apply prof_jet (u := D) (v := (w : ℤ) - D)
    (derivativeAlong_degree R P z D w hR hP)
  · intro a b
    convert center_degree R P z D w hR hP a b using 1
    congr 1
    ring
  · exact center_degree H P z D W hH hP

theorem coeff_theta_degree (R H : Tri) (P : F[X]) (z : F) (D w W m ρ : ℕ)
    (hR : wd R D ≤ w) (hH : wd H D ≤ W) (hP : P.natDegree ≤ D)
    (hne : PowerSeries.coeff ρ (theta R P z m H) ≠ 0) :
    ((PowerSeries.coeff ρ (theta R P z m H)).natDegree : ℤ) ≤
      W + 2 * ((w : ℤ) - D) * ρ :=
  (theta_degree R H P z D w W m hR hH hP ρ).resolve_left hne

end P64C6Degree
end ProximityPrize.SubmissionBinaryLower
