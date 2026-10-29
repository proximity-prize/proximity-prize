import ProximityPrize.SubmissionBinaryLower.P64C6Incidence
import ProximityPrize.SubmissionBinaryLower.P64C6Geometry

/-!
# Curves on which the outer derivative vanishes
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Exceptional

open Polynomial P64Found P64C6Coordinates P64C6Finite P64Resultant
  BCHKSSubstitutionVanish

variable {F : Type} [Field F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

lemma derivative_parameter_weight (R : Tri) (q d : ℕ) (hR : WtLE 0 q 1 d R) :
    WtLE 0 q 1 d (Polynomial.derivative R) := by
  intro a b l hn
  have he : c3 (Polynomial.derivative R) a b l = c3 R a (b + 1) l * ((b : F) + 1) := by
    unfold c3
    rw [Polynomial.coeff_derivative]
    rw [show ((b : Polynomial (Polynomial F)) + 1) =
      Polynomial.C (Polynomial.C ((b : F) + 1)) by simp]
    rw [Polynomial.coeff_mul_C, Polynomial.coeff_mul_C]
  rw [he] at hn
  have h := hR a (b + 1) l (left_ne_zero_of_mul hn)
  nlinarith

lemma derivative_X_cap (R : Tri) (w : ℕ) (hR : ∀ j, (R.coeff j).natDegree ≤ w) (j : ℕ) :
    ((Polynomial.derivative R).coeff j).natDegree ≤ w := by
  rw [Polynomial.coeff_derivative]
  calc (R.coeff (j + 1) * ((j : Polynomial (Polynomial F)) + 1)).natDegree ≤
        (R.coeff (j + 1)).natDegree + ((j : Polynomial (Polynomial F)) + 1).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ w + 0 := by
      apply Nat.add_le_add (hR (j + 1))
      rw [show ((j : Polynomial (Polynomial F)) + 1) =
        Polynomial.C ((j : Polynomial F) + 1) by simp]
      simp
    _ = w := by omega

variable [Fintype F] [DecidableEq F]

theorem card_derivative_zero_le (R : Tri) (hirr : Irreducible R) (hh : 0 < R.natDegree)
    (hsep : Polynomial.derivative R ≠ 0) (D w q d : ℕ)
    (hRw : P64Caps.Weighted.weightedSupportDegree R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (hF : 2 * R.natDegree * w < Fintype.card F)
    (S : Finset F) (P : F → F[X]) (hcurve : ∀ z ∈ S, triEval R z (P z) = 0) :
    (S.filter fun z => derivativeAlong R (P z) z = 0).card ≤ 2 * R.natDegree * d := by
  have hdeg : (Polynomial.derivative R).natDegree < R.natDegree :=
    Polynomial.natDegree_derivative_lt (by omega)
  have hndvd : ¬ R ∣ Polynomial.derivative R := by
    intro hd
    have hle := Polynomial.natDegree_le_of_dvd hd hsep
    omega
  have hX : ∀ j, (R.coeff j).natDegree ≤ w :=
    fun j => (coeff_natDegree_le_weighted R D j).trans hRw
  have hc := card_common_le R (Polynomial.derivative R) hirr hh hndvd d d w
    (coefficient_parameter_degree R q d hRyz)
    (coefficient_parameter_degree _ q d (derivative_parameter_weight R q d hRyz))
    hX (derivative_X_cap R w hX) ?_
    (S.filter fun z => derivativeAlong R (P z) z = 0) P (fun z hz => ?_)
  · calc _ ≤ (Polynomial.derivative R).natDegree * d + R.natDegree * d := hc
      _ ≤ R.natDegree * d + R.natDegree * d :=
        Nat.add_le_add_right (Nat.mul_le_mul_right d (Nat.le_of_lt hdeg)) _
      _ = _ := by ring
  · calc ((Polynomial.derivative R).natDegree + R.natDegree) * w ≤ (2 * R.natDegree) * w :=
        Nat.mul_le_mul_right w (by omega)
      _ < _ := hF
  · obtain ⟨hz, hzero⟩ := Finset.mem_filter.mp hz
    exact ⟨hcurve z hz, hzero⟩

end P64C6Exceptional
end ProximityPrize.SubmissionBinaryLower
