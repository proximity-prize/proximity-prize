import ProximityPrize.SubmissionBinaryLower.P64Frobenius
import ProximityPrize.SubmissionBinaryLower.P64C6Case

/-!
# Degree and line-order transfers for Frobenius descent
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6TwistTransfer

open Polynomial P64Found P64LineOrder P64Cofactor

section CoefficientMap

variable {A B : Type*} [CommRing A] [CommRing B]

lemma weighted_map (f : A →+* B) (hf : Function.Injective f)
    (R : Polynomial (Polynomial A)) (D : ℕ) :
    P64Caps.Weighted.weightedSupportDegree (R.map (Polynomial.mapRingHom f)) D =
      P64Caps.Weighted.weightedSupportDegree R D := by
  unfold P64Caps.Weighted.weightedSupportDegree
  rw [Polynomial.support_map_of_injective R (Polynomial.map_injective _ hf)]
  apply Finset.sup_congr rfl
  intro j _
  rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom,
    Polynomial.natDegree_map_eq_of_injective hf]

lemma tord_map (f : A →+* B) (hf : Function.Injective f)
    (R : Polynomial (Polynomial A)) (hR : R ≠ 0) :
    tord (R.map (Polynomial.mapRingHom f)) = tord R := by
  have hmap : R.map (Polynomial.mapRingHom f) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Polynomial.map_injective _ hf)).mpr hR
  apply le_antisymm
  · apply (le_tord_iff hR).mpr
    intro a b hab
    have hz := (le_tord_iff hmap).mp le_rfl a b hab
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom] at hz
    apply hf
    simpa using hz
  · apply (le_tord_iff hmap).mpr
    intro a b hab
    have hz := (le_tord_iff hR).mp le_rfl a b hab
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, hz, map_zero]

lemma shift_map (f : A →+* B) (R : Polynomial (Polynomial A)) (x y : A) :
    (Polynomial.Bivariate.shift R x y).map (Polynomial.mapRingHom f) =
      Polynomial.Bivariate.shift (R.map (Polynomial.mapRingHom f)) (f x) (f y) := by
  have hp : ∀ p : Polynomial A, (p.comp (Polynomial.X + Polynomial.C x)).map f =
      (p.map f).comp (Polynomial.X + Polynomial.C (f x)) := by
    intro p
    rw [Polynomial.map_comp]
    simp
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      simpa [Polynomial.Bivariate.shift] using congrArg₂ (· + ·) hR hS
  | monomial j p =>
      simp [Polynomial.Bivariate.shift, Polynomial.monomial_comp, hp]

end CoefficientMap

section Frobenius

variable {F : Type} [Field F] [CharP F 2] [PerfectRing F 2]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

noncomputable def paramSquare : Tri →+* Tri :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.expand F 2).toRingHom)

theorem paramSquare_frobLift (R : Tri) : paramSquare (frobLift R) = R ^ 2 := by
  have hh : paramSquare.comp frobLift = frobenius Tri 2 := by
    ext c <;> simp [paramSquare, frobLift, frobenius_def]
  simpa [frobenius_def] using RingHom.congr_fun hh R

lemma frobLift_ne_zero {R : Tri} (hR : R ≠ 0) : frobLift R ≠ 0 := by
  intro hz
  have h := paramSquare_frobLift R
  rw [hz, map_zero] at h
  exact pow_ne_zero 2 hR h.symm

theorem spatial_weight_frobLift (R : Tri) (hR : R ≠ 0) (D : ℕ) :
    P64Caps.Weighted.weightedSupportDegree (frobLift R) D =
      2 * P64Caps.Weighted.weightedSupportDegree R D := by
  have hi : Function.Injective ((Polynomial.expand F 2).toRingHom : F[X] → F[X]) :=
    Polynomial.expand_injective (by norm_num)
  rw [← weighted_map (Polynomial.expand F 2).toRingHom hi (frobLift R) D]
  change P64Caps.Weighted.weightedSupportDegree (paramSquare (frobLift R)) D = _
  rw [paramSquare_frobLift, weightedSupportDegree_pow R hR D 2]

theorem parameter_weight_transfer (R : Tri) (q d : ℕ)
    (hw : WtLE 0 q 1 d (frobLift R)) : WtLE 0 (2 * q) 1 d R := by
  intro a b l hn
  have hn' : c3 (frobLift R) (a * 2) (b * 2) l ≠ 0 := by
    unfold c3
    rw [coeff_coeff_frobLift, Polynomial.coeff_map]
    exact fun hz => hn (by simpa [c3] using hz)
  have h := hw (a * 2) (b * 2) l hn'
  nlinarith

theorem lineOrd_frobLift (R : Tri) (hR : R ≠ 0) (x : F) (y : F[X]) :
    lineOrd (frobLift R) x y = 2 * lineOrd R x (Polynomial.expand F 2 y) := by
  let f : F[X] →+* F[X] := (Polynomial.expand F 2).toRingHom
  have hf : Function.Injective f := Polynomial.expand_injective (by norm_num)
  have heq : (lineShift (frobLift R) x y).map (Polynomial.mapRingHom f) =
      lineShift (R ^ 2) x (Polynomial.expand F 2 y) := by
    change (Polynomial.Bivariate.shift (frobLift R) (Polynomial.C x) y).map
      (Polynomial.mapRingHom f) = _
    rw [shift_map]
    have hx : f (Polynomial.C x) = Polynomial.C x := by simp [f]
    rw [hx]
    change lineShift (paramSquare (frobLift R)) x (Polynomial.expand F 2 y) = _
    rw [paramSquare_frobLift]
  have ht := tord_map f hf (lineShift (frobLift R) x y)
    ((lineShift_eq_zero_iff _ x y).not.mpr (frobLift_ne_zero hR))
  rw [heq] at ht
  change lineOrd (R ^ 2) x (Polynomial.expand F 2 y) = lineOrd (frobLift R) x y at ht
  rw [lineOrd_pow hR] at ht
  exact ht.symm

end Frobenius

end P64C6TwistTransfer
end ProximityPrize.SubmissionBinaryLower
