import ProximityPrize.SubmissionBinaryLower.P64C6Shear

/-!
# Local order profiles in line coordinates

After shifting a line to `U = V = 0`, substitute `U = X - x` and
`V = Δ(X) + V`. If `X - x` divides `Δ`, total order at the line becomes
a divisibility profile on the coefficients of `V`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Line

open Polynomial P64C6Flow P64C6Coordinates P64C6Shear

variable {F : Type*} [Field F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

/-- Substitute `z + W` in a coefficient polynomial, retaining `F[X]` as the base ring. -/
noncomputable def paramHom (z : F) : F[X] →+* Polynomial (Polynomial F) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
    (Polynomial.X + Polynomial.C (Polynomial.C z))

noncomputable def lineExpand (x : F) (Δ : F[X]) (z : F) : Tri →+* Tri :=
  Polynomial.eval₂RingHom (R := Polynomial (Polynomial F)) (S := Tri)
    (Polynomial.eval₂RingHom (R := Polynomial F) (S := Tri)
      (Polynomial.C.comp (paramHom z))
      (Polynomial.C (Polynomial.C ((Polynomial.X : F[X]) - Polynomial.C x))))
    (Polynomial.X + Polynomial.C (Polynomial.C Δ))

lemma ord_poly_nonpos (π : F[X]) (n : ℤ) (hn : n ≤ 0) (p : Polynomial (Polynomial F)) :
    ((Grading.ord π).poly 0).mem n p := by
  intro b
  change π ^ (n - b * 0).toNat ∣ p.coeff b
  simp [Int.toNat_eq_zero.mpr hn]

theorem lineExpand_order (S : Tri) (x z : F) (Δ : F[X]) (μ : ℕ)
    (hS : ∀ a b, a + b < μ → (S.coeff b).coeff a = 0)
    (hΔ : Polynomial.X - Polynomial.C x ∣ Δ) :
    (((Grading.ord (Polynomial.X - Polynomial.C x)).poly 0).poly 1).mem μ
      (lineExpand x Δ z S) := by
  let π : F[X] := Polynomial.X - Polynomial.C x
  let G := ((Grading.ord π).poly 0).poly 1
  have hπ : (Grading.ord π).mem 1 π := by simp [Grading.ord]
  have hΔ' : (Grading.ord π).mem 1 Δ := by simpa [Grading.ord, π] using hΔ
  apply Grading.eval₂_mem G _ S
    (G.add_mem (Grading.poly_X _ _) (Grading.poly_C (Grading.poly_C hΔ')))
  intro b
  apply Grading.eval₂_mem G _ (S.coeff b)
    (Grading.poly_C (Grading.poly_C hπ))
  intro a
  by_cases hlt : a + b < μ
  · rw [hS a b hlt, map_zero]
    exact G.zero_mem _
  · apply Grading.poly_C
    apply ord_poly_nonpos
    push_cast
    omega

noncomputable def displacement (y : F[X]) (z : F) : Polynomial (Polynomial F) :=
  paramHom z y - Polynomial.C (Polynomial.C (y.eval z))

lemma displacement_zero (y : F[X]) (z : F) : (displacement y z).coeff 0 = 0 := by
  induction y using Polynomial.induction_on' with
  | add p q hp hq => simp [displacement, map_add] at hp hq ⊢; linear_combination hp + hq
  | monomial a c =>
      simp [displacement, paramHom, coeff_zero_eq_eval_zero, eval₂_monomial,
        eval_pow, eval_mul]

/-- The local expansion agrees with the moving-line shear of the curve-centred polynomial. -/
lemma lineExpand_shift (R : Tri) (x z : F) (P y : F[X]) :
    lineExpand x (P - Polynomial.C (y.eval z)) z (P64LineOrder.lineShift R x y) =
      shear (displacement y z) (center P z R) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      simpa [P64LineOrder.lineShift, Polynomial.Bivariate.shift, add_comp] using congrArg₂ (· + ·) hR hS
  | monomial j p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          simpa [P64LineOrder.lineShift, Polynomial.Bivariate.shift, add_comp] using congrArg₂ (· + ·) hp hq
      | monomial a p =>
          induction p using Polynomial.induction_on' with
          | add p q hp hq =>
              simpa [P64LineOrder.lineShift, Polynomial.Bivariate.shift, add_comp] using congrArg₂ (· + ·) hp hq
          | monomial b c =>
              simp [lineExpand, P64LineOrder.lineShift, Polynomial.Bivariate.shift,
                shear, center, shiftHom, reorder, paramHom, displacement,
                Polynomial.Bivariate.swap_monomial_monomial, Polynomial.taylor_apply,
                Polynomial.eval₂_pow, Polynomial.eval₂_add,
                Polynomial.eval₂_mul, Polynomial.eval₂_monomial]
              simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
              ring

/-- Line order becomes the coefficient profile for the sheared, curve-centred polynomial. -/
lemma shear_center_order (R : Tri) (x z : F) (P y : F[X]) (μ : ℕ)
    (hR : P64LineOrder.OrdGE R x y μ) (hmatch : P.eval x = y.eval z) (a b : ℕ) :
    (Grading.ord (Polynomial.X - Polynomial.C x)).mem ((μ : ℤ) - a)
      (((shear (displacement y z) (center P z R)).coeff a).coeff b) := by
  have hΔ : Polynomial.X - Polynomial.C x ∣ P - Polynomial.C (y.eval z) := by
    rw [Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot, hmatch]
  have h := lineExpand_order (P64LineOrder.lineShift R x y) x z
    (P - Polynomial.C (y.eval z)) μ hR hΔ
  rw [lineExpand_shift] at h
  simpa [Grading.poly] using h a b

/-- Vanishing along a line increases the order of every finite-flow coefficient. -/
theorem theta_order (R H : Tri) (x z : F) (P y : F[X]) (μ ν m ρ : ℕ)
    (hμ : 1 ≤ μ) (hρ : ρ ≤ m)
    (hR : P64LineOrder.OrdGE R x y μ) (hH : P64LineOrder.OrdGE H x y ν)
    (hmatch : P.eval x = y.eval z) (hcurve : BCHKSSubstitutionVanish.triEval R z P = 0)
    (hs : derivativeAlong R P z ≠ 0) :
    (Polynomial.X - Polynomial.C x) ^ (ν + 2 * ρ * (μ - 1)) ∣
      PowerSeries.coeff ρ (theta R P z m H) := by
  let π : F[X] := Polynomial.X - Polynomial.C x
  let f := center P z R
  let η := displacement y z
  have hη : η.coeff 0 = 0 := displacement_zero y z
  have h00 : (f.coeff 0).coeff 0 = 0 := by
    rw [center_coeff_zero]; exact hcurve
  have h10 : (f.coeff 1).coeff 0 = derivativeAlong R P z := center_coeff_one R P z
  have hsg : (Grading.ord π).mem ((μ : ℤ) - 1) (derivativeAlong R P z) := by
    have h := shear_center_order R x z P y μ hR hmatch 1 0
    rw [shear_coeff_one _ (displacement_zero y z), center_coeff_one] at h
    exact h
  have ho := jet_order_of_shear (G := Grading.ord π) (L := (μ : ℤ) - 1) (N := ν)
    f (center P z H) η hη (derivativeAlong R P z) hs m ρ hρ h00 h10 hsg
    (fun a b => by
      rw [show (1 : ℤ) + ((μ : ℤ) - 1) - a = μ - a by ring]
      exact shear_center_order R x z P y μ hR hmatch a b)
    (shear_center_order H x z P y ν hH hmatch)
  change π ^ ((ν : ℤ) + 2 * ((μ : ℤ) - 1) * ρ).toNat ∣ _ at ho
  have he : ((ν : ℤ) + 2 * ((μ : ℤ) - 1) * ρ).toNat = ν + 2 * ρ * (μ - 1) := by
    have hi : (ν : ℤ) + 2 * ((μ : ℤ) - 1) * ρ = (ν + 2 * ρ * (μ - 1) : ℕ) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hμ]
      push_cast
      ring
    rw [hi, Int.toNat_natCast]
  rw [he] at ho
  exact ho

/-- A local cofactor may be removed because the defining equation vanishes to the truncation order. -/
theorem theta_flat_order (R H G : Tri) (x z : F) (P y : F[X]) (μ ν m ρ : ℕ)
    (hμ : 1 ≤ μ) (hρ : ρ ≤ m)
    (hR : P64LineOrder.OrdGE R x y μ)
    (hflat : P64LineOrder.OrdGE (H + R * G) x y ν)
    (hmatch : P.eval x = y.eval z) (hcurve : BCHKSSubstitutionVanish.triEval R z P = 0)
    (hs : derivativeAlong R P z ≠ 0) :
    (Polynomial.X - Polynomial.C x) ^ (ν + 2 * ρ * (μ - 1)) ∣
      PowerSeries.coeff ρ (theta R P z m H) := by
  have ho := theta_order R (H + R * G) x z P y μ ν m ρ hμ hρ hR hflat hmatch hcurve hs
  have hmul : (PowerSeries.X : PowerSeries (F[X])) ^ (m + 1) ∣ theta R P z m (R * G) := by
    rw [map_mul]
    exact dvd_mul_of_dvd_left (theta_self R P z m hcurve) _
  have hcoeff := PowerSeries.X_pow_dvd_iff.mp hmul ρ (by omega)
  have hev : theta R P z m (H + R * G) = theta R P z m H + theta R P z m (R * G) :=
    (theta R P z m).map_add H (R * G)
  rw [hev, map_add, hcoeff, add_zero] at ho
  exact ho

end P64C6Line
end ProximityPrize.SubmissionBinaryLower
