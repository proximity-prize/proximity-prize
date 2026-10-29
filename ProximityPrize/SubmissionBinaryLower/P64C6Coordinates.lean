import ProximityPrize.SubmissionBinaryLower.P64C6Res
import ProximityPrize.SubmissionBinaryLower.P64C6Graded

/-!
# Flow coordinates for the trivariate challenge polynomials

The challenge stores `F[Z][X][Y]`. The flow keeps `F[X]` as the coefficient
ring and translates the other two variables around `(P(X), z)`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Coordinates

open Polynomial P64C6Flow P64C6Theta BCHKSSubstitutionVanish

section Shift

variable {B : Type*} [CommRing B]

noncomputable def shiftHom (u v : B) :
    Polynomial (Polynomial B) →+* Polynomial (Polynomial B) :=
  (Polynomial.mapRingHom (Polynomial.taylorAlgHom u).toRingHom).comp
    (Polynomial.taylorAlgHom (Polynomial.C v)).toRingHom

lemma shiftHom_apply (u v : B) (f : Polynomial (Polynomial B)) :
    shiftHom u v f = Polynomial.Bivariate.shift f u v := rfl

lemma Ev_shift (x y : PowerSeries B) (u v : B) (f : Polynomial (Polynomial B)) :
    Ev x y (shiftHom u v f) = Ev (x + PowerSeries.C v) (y + PowerSeries.C u) f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial a p =>
      simp [shiftHom, taylor_apply, Ev_apply, eval₂_comp, eval₂_pow, eval₂_add,
        eval₂_C, eval₂_X]

lemma shift_mem {G : Grading B} {u v W : ℤ} {p : Polynomial (Polynomial B)} {x y : B}
    (hp : ((G.poly u).poly v).mem W p) (hx : G.mem u x) (hy : G.mem v y) :
    ((G.poly u).poly v).mem W (shiftHom x y p) := by
  apply Grading.map_mem (Polynomial.taylorAlgHom x).toRingHom
    (fun _ _ h => Grading.taylor_mem h hx)
  exact Grading.taylor_mem hp (Grading.poly_C hy)

end Shift

section Coordinates

variable {F : Type*} [Field F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

/-- Interchange the two coefficient variables, leaving the outer `Y` variable fixed. -/
noncomputable def reorder : Tri →+* Tri :=
  Polynomial.mapRingHom Polynomial.Bivariate.swap.toRingHom

noncomputable def center (P : F[X]) (z : F) : Tri →+* Tri :=
  (shiftHom (Polynomial.C z) P).comp reorder

lemma coeff_swap (p : Polynomial (Polynomial F)) (a b : ℕ) :
    ((Polynomial.Bivariate.swap p).coeff b).coeff a = (p.coeff a).coeff b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp_all
      | monomial m c =>
          rw [Polynomial.Bivariate.swap_monomial_monomial]
          simp only [coeff_monomial]
          split_ifs <;> simp_all [coeff_monomial]

lemma eval_swap (p : Polynomial (Polynomial F)) (z : F) :
    (Polynomial.Bivariate.swap p).eval (Polynomial.C z) =
      p.map (Polynomial.evalRingHom z) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp_all
      | monomial m c =>
          rw [Polynomial.Bivariate.swap_monomial_monomial]
          simp [← C_mul_X_pow_eq_monomial]
          ring

lemma eval_reorder (R : Tri) (P : F[X]) (z : F) :
    (reorder R).eval₂ (Polynomial.evalRingHom (Polynomial.C z)) P = triEval R z P := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS => simp [hR, hS, triEval, specializeZ]
  | monomial a p =>
      simp [reorder, eval_swap, triEval, specializeZ, coe_evalRingHom]

lemma center_coeff_zero (R : Tri) (P : F[X]) (z : F) :
    (((center P z R).coeff 0).coeff 0) = triEval R z P := by
  simp only [center, shiftHom, RingHom.comp_apply, Polynomial.coe_mapRingHom, coeff_map]
  change ((Polynomial.taylor (Polynomial.C z)
    ((Polynomial.taylor (Polynomial.C P) (reorder R)).coeff 0)).coeff 0) = _
  rw [taylor_coeff_zero, taylor_coeff_zero]
  calc _ = (reorder R).eval₂ (Polynomial.evalRingHom (Polynomial.C z)) P := by
        simpa only [coe_evalRingHom, eval_C] using
          (Polynomial.eval₂_at_apply (p := reorder R)
            (Polynomial.evalRingHom (Polynomial.C z)) (Polynomial.C P)).symm
    _ = _ := eval_reorder R P z

lemma center_derivative (R : Tri) (P : F[X]) (z : F) :
    center P z (Polynomial.derivative R) = Polynomial.derivative (center P z R) := by
  simp [center, shiftHom, reorder, taylor_apply, derivative_map, derivative_comp]

lemma center_coeff_one (R : Tri) (P : F[X]) (z : F) :
    (((center P z R).coeff 1).coeff 0) = triEval (Polynomial.derivative R) z P := by
  rw [← center_coeff_zero, center_derivative, coeff_derivative]
  simp

noncomputable def derivativeAlong (R : Tri) (P : F[X]) (z : F) : F[X] :=
  triEval (Polynomial.derivative R) z P

/-- The finite flow, expressed on the original challenge coordinates. -/
noncomputable def theta (R : Tri) (P : F[X]) (z : F) (m : ℕ) :
    Tri →+* PowerSeries (F[X]) :=
  (jet (center P z R) (derivativeAlong R P z) m).comp (center P z)

lemma theta_eq_curveEval (R H : Tri) (P : F[X]) (z : F) (m : ℕ) :
    theta R P z m H = P64C6Res.curveEval
      (PowerSeries.C P + flow (center P z R) (derivativeAlong R P z) m)
      (Polynomial.C z) ((derivativeAlong R P z) ^ 2) (reorder H) := by
  change Ev _ _ (shiftHom _ _ (reorder H)) = _
  rw [Ev_shift]
  simp only [P64C6Res.curveEval, parameter, add_comm]

lemma theta_self (R : Tri) (P : F[X]) (z : F) (m : ℕ) (hR : triEval R z P = 0) :
    (PowerSeries.X : PowerSeries (F[X])) ^ (m + 1) ∣ theta R P z m R := by
  apply X_pow_dvd_jet_self
  · rwa [center_coeff_zero]
  · exact center_coeff_one R P z

lemma constantCoeff_theta (R H : Tri) (P : F[X]) (z : F) (m : ℕ) :
    PowerSeries.constantCoeff (theta R P z m H) = triEval H z P := by
  rw [theta, RingHom.comp_apply, constantCoeff_jet, center_coeff_zero]

end Coordinates

end P64C6Coordinates
end ProximityPrize.SubmissionBinaryLower
