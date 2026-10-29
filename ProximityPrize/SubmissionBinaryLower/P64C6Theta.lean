import ProximityPrize.SubmissionBinaryLower.P64C6Flow

/-!
# Finite flow evaluation and its coefficient profiles

The same calculation controls degree in `F[X]` and divisibility by powers of
`X - xᵢ`. No inversion of the derivative `s` is used.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Theta

open PowerSeries P64C6Flow

variable {B : Type*} [CommRing B]

noncomputable def flow (f : Polynomial (Polynomial B)) (s : B) (m : ℕ) : B⟦X⟧ :=
  C s * iter (red f s) m

noncomputable def parameter (s : B) : B⟦X⟧ := C (s ^ 2) * X

/-- Evaluate a polynomial in the displacement coordinates along the finite flow. -/
noncomputable def jet (f : Polynomial (Polynomial B)) (s : B) (m : ℕ) :
    Polynomial (Polynomial B) →+* B⟦X⟧ := Ev (flow f s m) (parameter s)

lemma constantCoeff_flow (f : Polynomial (Polynomial B)) (s : B) (m : ℕ) :
    constantCoeff (flow f s m) = 0 := by
  simp [flow, constantCoeff_iter _ (red_coeff_zero_zero f s)]

lemma constantCoeff_parameter (s : B) : constantCoeff (parameter s) = 0 := by
  simp [parameter]

lemma constantCoeff_jet (f H : Polynomial (Polynomial B)) (s : B) (m : ℕ) :
    constantCoeff (jet f s m H) = (H.coeff 0).coeff 0 :=
  constantCoeff_Ev _ _ H (constantCoeff_flow f s m) (constantCoeff_parameter s)

/-- The defining equation vanishes to the requested truncation order. -/
theorem X_pow_dvd_jet_self (f : Polynomial (Polynomial B)) (s : B) (m : ℕ)
    (h00 : (f.coeff 0).coeff 0 = 0) (h10 : (f.coeff 1).coeff 0 = s) :
    (X : B⟦X⟧) ^ (m + 1) ∣ jet f s m f := by
  change X ^ (m + 1) ∣ Ev (C s * iter (red f s) m) (C (s ^ 2) * X) f
  rw [red_spec f s h00 h10]
  exact dvd_mul_of_dvd_right
    (iter_residual _ (red_coeff_zero_zero f s) (red_coeff_one_zero f s) m) _

/-- Multiples of the defining equation vanish to the same order. -/
lemma X_pow_dvd_jet_mul (f H : Polynomial (Polynomial B)) (s : B) (m : ℕ)
    (h00 : (f.coeff 0).coeff 0 = 0) (h10 : (f.coeff 1).coeff 0 = s) :
    (X : B⟦X⟧) ^ (m + 1) ∣ jet f s m (f * H) := by
  rw [map_mul]
  exact dvd_mul_of_dvd_left (X_pow_dvd_jet_self f s m h00 h10) _

/-- The normalization `f(sV,s²W)/s²` preserves the required linear profile. -/
lemma red_profile {G : Grading B} {u v : ℤ} {f : Polynomial (Polynomial B)} {s : B}
    (hs : G.mem v s)
    (hf : ∀ a b : ℕ, G.mem (u + v - a * u) ((f.coeff a).coeff b)) (a b : ℕ) :
    G.mem ((u - v) - a * (u - v) + b * (2 * v)) (((red f s).coeff a).coeff b) := by
  rw [coeff_red, redCoeff]
  split_ifs with h
  · refine G.congr_mem ?_ (G.mul_mem (hf a b) (G.pow_mem hs (a + 2 * b - 2)))
    rw [Nat.cast_sub h]
    push_cast
    ring
  · exact G.zero_mem _

lemma prof_flow {G : Grading B} {u v : ℤ} {f : Polynomial (Polynomial B)} {s : B}
    (hs : G.mem v s)
    (hf : ∀ a b : ℕ, G.mem (u + v - a * u) ((f.coeff a).coeff b)) (m : ℕ) :
    Prof G u (2 * v) (flow f s m) := by
  exact ((Prof.C_mem hs).mul (prof_iter (red f s) (red_profile hs hf) m)).congr (by ring)

lemma prof_parameter {G : Grading B} {v : ℤ} {s : B} (hs : G.mem v s) :
    Prof G 0 (2 * v) (parameter s) := by
  exact ((Prof.C_mem (G.pow_mem hs 2)).mul Prof.X_mem).congr (by ring)

/-- Degree and order bounds for every coefficient of the finite flow evaluation. -/
theorem prof_jet {G : Grading B} {u v W : ℤ} {f H : Polynomial (Polynomial B)} {s : B}
    (hs : G.mem v s)
    (hf : ∀ a b : ℕ, G.mem (u + v - a * u) ((f.coeff a).coeff b))
    (hH : ∀ a b : ℕ, G.mem (W - a * u) ((H.coeff a).coeff b)) (m : ℕ) :
    Prof G W (2 * v) (jet f s m H) := by
  refine prof_Ev (prof_flow hs hf m) (prof_parameter hs) H fun a b => ?_
  simpa using hH a b

end P64C6Theta
end ProximityPrize.SubmissionBinaryLower
