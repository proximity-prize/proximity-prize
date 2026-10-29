import ProximityPrize.SubmissionBinaryLower.P64C6Count

/-!
# Comparing the flow in moving line coordinates

A line displacement is a polynomial `η(W)` with zero constant coefficient.
The finite flow is unchanged, through its truncation order, when this
displacement is absorbed into the outer coordinate. This also applies to
Frobenius-twisted lines, whose displacement is a higher power of `W`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Shear

open Polynomial P64C6Flow P64C6Theta

variable {B : Type*} [CommRing B]

noncomputable def shear (η : Polynomial B) :
    Polynomial (Polynomial B) →+* Polynomial (Polynomial B) :=
  Polynomial.compRingHom (Polynomial.X + Polynomial.C η)

lemma Ev_shear (x y : PowerSeries B) (η : Polynomial B) (f : Polynomial (Polynomial B)) :
    Ev x y (shear η f) = Ev (x + η.eval₂ PowerSeries.C y) y f := by
  simp [shear, Ev_apply, eval₂_comp, eval₂_add, eval₂_C, eval₂_X]

lemma shear_coeff_zero (η : Polynomial B) (hη : η.coeff 0 = 0)
    (f : Polynomial (Polynomial B)) :
    ((shear η f).coeff 0).coeff 0 = (f.coeff 0).coeff 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial a p =>
      have hη' : η.eval 0 = 0 := by simpa only [coeff_zero_eq_eval_zero] using hη
      simp [shear, coeff_zero_eq_eval_zero, eval_comp, hη', eval_pow]

lemma shear_derivative (η : Polynomial B) (f : Polynomial (Polynomial B)) :
    shear η (Polynomial.derivative f) = Polynomial.derivative (shear η f) := by
  simp [shear, derivative_comp]

lemma shear_coeff_one (η : Polynomial B) (hη : η.coeff 0 = 0)
    (f : Polynomial (Polynomial B)) :
    ((shear η f).coeff 1).coeff 0 = (f.coeff 1).coeff 0 := by
  have h := shear_coeff_zero η hη (Polynomial.derivative f)
  rw [shear_derivative, coeff_derivative, coeff_derivative] at h
  simpa using h

noncomputable def correction (η : Polynomial B) (s : B) : PowerSeries B :=
  PowerSeries.C s * PowerSeries.X * η.divX.eval₂ PowerSeries.C (parameter s)

lemma constantCoeff_correction (η : Polynomial B) (s : B) :
    PowerSeries.constantCoeff (correction η s) = 0 := by
  simp [correction]

lemma correction_spec (η : Polynomial B) (hη : η.coeff 0 = 0) (s : B) :
    PowerSeries.C s * correction η s = η.eval₂ PowerSeries.C (parameter s) := by
  have heq : Polynomial.X * η.divX = η := by
    simpa [hη] using Polynomial.X_mul_divX_add η
  conv_rhs => rw [← heq, eval₂_mul, eval₂_X]
  simp only [correction, parameter, pow_two, map_mul]
  ring

/-- Evaluation preserves congruence in its outer argument. -/
lemma Ev_sub_dvd (f : Polynomial (Polynomial B)) (y x x' : PowerSeries B) :
    x - x' ∣ Ev x y f - Ev x' y f := by
  have h := Polynomial.sub_dvd_eval_sub x x'
    (f.map (Polynomial.eval₂RingHom PowerSeries.C y))
  simpa [Polynomial.eval_map, Ev_apply] using h

lemma Ev_correction (f : Polynomial (Polynomial B)) (η : Polynomial B)
    (hη : η.coeff 0 = 0) (s : B) (x : PowerSeries B) :
    Ev (PowerSeries.C s * (x - correction η s)) (parameter s) (shear η f) =
      Ev (PowerSeries.C s * x) (parameter s) f := by
  rw [Ev_shear, ← correction_spec η hη s]
  rw [mul_sub, sub_add_cancel]

variable [IsDomain B]

lemma X_pow_dvd_of_C_mul {c : B} (hc : c ≠ 0) {x : PowerSeries B} {n : ℕ}
    (h : (PowerSeries.X : PowerSeries B) ^ n ∣ PowerSeries.C c * x) :
    (PowerSeries.X : PowerSeries B) ^ n ∣ x := by
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro k hk
  have heq := h k hk
  rw [PowerSeries.coeff_C_mul] at heq
  exact (mul_eq_zero.mp heq).resolve_left hc

/-- The corrected iterate solves the shifted equation to the same order. -/
lemma corrected_residual (f : Polynomial (Polynomial B)) (η : Polynomial B)
    (hη : η.coeff 0 = 0) (s : B) (hs : s ≠ 0) (m : ℕ)
    (h00 : (f.coeff 0).coeff 0 = 0) (h10 : (f.coeff 1).coeff 0 = s) :
    let x := iter (red f s) m - correction η s
    (PowerSeries.X : PowerSeries B) ^ (m + 1) ∣
      x + Ev x PowerSeries.X (red (shear η f) s) := by
  dsimp only
  apply X_pow_dvd_of_C_mul (pow_ne_zero 2 hs)
  rw [← red_spec (shear η f) s
    (by rw [shear_coeff_zero η hη, h00]) (by rw [shear_coeff_one η hη, h10])]
  change PowerSeries.X ^ (m + 1) ∣
    Ev (PowerSeries.C s * (iter (red f s) m - correction η s)) (parameter s) (shear η f)
  rw [Ev_correction f η hη s]
  exact X_pow_dvd_jet_self f s m h00 h10

/-- Uniqueness identifies the corrected iterate with the local one. -/
lemma corrected_iter_congr (f : Polynomial (Polynomial B)) (η : Polynomial B)
    (hη : η.coeff 0 = 0) (s : B) (hs : s ≠ 0) (m : ℕ)
    (h00 : (f.coeff 0).coeff 0 = 0) (h10 : (f.coeff 1).coeff 0 = s) :
    (PowerSeries.X : PowerSeries B) ^ (m + 1) ∣
      (iter (red f s) m - correction η s) - iter (red (shear η f) s) m := by
  apply eq_mod_of_residual (red (shear η f) s) (red_coeff_one_zero _ _) m
  · simp [constantCoeff_iter _ (red_coeff_zero_zero f s), constantCoeff_correction]
  · exact constantCoeff_iter _ (red_coeff_zero_zero _ _) m
  · exact corrected_residual f η hη s hs m h00 h10
  · exact iter_residual _ (red_coeff_zero_zero _ _) (red_coeff_one_zero _ _) m

theorem jet_shear_congr (f H : Polynomial (Polynomial B)) (η : Polynomial B)
    (hη : η.coeff 0 = 0) (s : B) (hs : s ≠ 0) (m : ℕ)
    (h00 : (f.coeff 0).coeff 0 = 0) (h10 : (f.coeff 1).coeff 0 = s) :
    (PowerSeries.X : PowerSeries B) ^ (m + 1) ∣
      jet f s m H - jet (shear η f) s m (shear η H) := by
  have hc := dvd_mul_of_dvd_right (corrected_iter_congr f η hη s hs m h00 h10)
    (PowerSeries.C s)
  rw [mul_sub] at hc
  have he := dvd_trans hc (Ev_sub_dvd (shear η H) (parameter s) _ _)
  rw [Ev_correction H η hη s] at he
  exact he

theorem coeff_jet_shear (f H : Polynomial (Polynomial B)) (η : Polynomial B)
    (hη : η.coeff 0 = 0) (s : B) (hs : s ≠ 0) (m ρ : ℕ) (hρ : ρ ≤ m)
    (h00 : (f.coeff 0).coeff 0 = 0) (h10 : (f.coeff 1).coeff 0 = s) :
    PowerSeries.coeff ρ (jet f s m H) =
      PowerSeries.coeff ρ (jet (shear η f) s m (shear η H)) := by
  have h := PowerSeries.X_pow_dvd_iff.mp (jet_shear_congr f H η hη s hs m h00 h10) ρ (by omega)
  simpa only [map_sub, sub_eq_zero] using h

/-- Transport a local profile back to the global flow, through its truncation order. -/
theorem jet_order_of_shear {G : Grading B} {L N : ℤ}
    (f H : Polynomial (Polynomial B)) (η : Polynomial B) (hη : η.coeff 0 = 0)
    (s : B) (hs : s ≠ 0) (m ρ : ℕ) (hρ : ρ ≤ m)
    (h00 : (f.coeff 0).coeff 0 = 0) (h10 : (f.coeff 1).coeff 0 = s)
    (hsg : G.mem L s)
    (hf : ∀ a b : ℕ, G.mem (1 + L - a) (((shear η f).coeff a).coeff b))
    (hH : ∀ a b : ℕ, G.mem (N - a) (((shear η H).coeff a).coeff b)) :
    G.mem (N + 2 * L * ρ) (PowerSeries.coeff ρ (jet f s m H)) := by
  rw [coeff_jet_shear f H η hη s hs m ρ hρ h00 h10]
  exact prof_jet (u := 1) hsg (by simpa using hf) (by simpa using hH) m ρ

end P64C6Shear
end ProximityPrize.SubmissionBinaryLower
