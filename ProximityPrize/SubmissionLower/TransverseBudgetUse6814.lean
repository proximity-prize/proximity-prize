import ProximityPrize.SubmissionLower.ContactPencilDirection6814

/-! Local controls for the repeated common-factor case. These are not
counterexamples to the full received-word packet hypotheses. -/
namespace ProximityPrize.SubmissionLower.TransverseBudgetUse6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial

variable {K : Type*} [CommRing K]

def cheap (f : K) : Polynomial K := Polynomial.X^3+Polynomial.C f
def thick (f : K) : Polynomial K := (Polynomial.X-1)*(cheap f)^2

theorem cheap_dvd_thick (f : K) : cheap f ∣ thick f := by
  refine ⟨(Polynomial.X-1)*cheap f,?_⟩
  simp only [thick]
  ring

theorem thick_expansion (f : K) : thick f =
    Polynomial.X^7-Polynomial.X^6+Polynomial.C (2*f)*Polynomial.X^4-
      Polynomial.C (2*f)*Polynomial.X^3+Polynomial.C (f^2)*Polynomial.X-Polynomial.C (f^2) := by
  simp only [thick,cheap,map_mul,map_ofNat,map_pow]
  ring

theorem thick_low_coeffs (f : K) :
    (thick f).coeff 0 = -(f^2) ∧
    (thick f).coeff 1 = f^2 ∧
    (thick f).coeff 2 = 0 := by
  rw [thick_expansion]
  simp only [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_X,Polynomial.coeff_X_pow,Polynomial.coeff_C]
  norm_num

theorem squared_normal_factor_in_first_three_coeffs (f : K) :
    ∀ j<3, f^2 ∣ (thick f).coeff j := by
  intro j hj
  have h := thick_low_coeffs f
  interval_cases j
  · rw [h.1]
    exact dvd_neg.mpr (dvd_refl _)
  · rw [h.2.1]
  · rw [h.2.2]
    exact dvd_zero _

theorem reduced_thick : thick (0 : K)=Polynomial.X^6*(Polynomial.X-1) := by
  simp only [thick,cheap,map_zero,add_zero]
  ring

theorem reduced_root_order_exactly_six {E : Type*} [Field E] :
    (Polynomial.X : Polynomial E)^6 ∣ thick (0 : E) ∧
      ¬ (Polynomial.X : Polynomial E)^7 ∣ thick (0 : E) := by
  rw [reduced_thick]
  constructor
  · exact dvd_mul_right _ _
  · intro h
    have hc := (Polynomial.X_pow_dvd_iff.mp h) 6 (by decide)
    simp [Polynomial.coeff_X_pow_mul'] at hc

theorem constant_helper_nonzero {E : Type*} [Field E] (f : E) (hf : f≠0) :
    (thick f).coeff 0 ≠ 0 := by
  rw [(thick_low_coeffs f).1]
  exact neg_ne_zero.mpr (pow_ne_zero _ hf)

#print axioms squared_normal_factor_in_first_three_coeffs
#print axioms reduced_root_order_exactly_six
#print axioms constant_helper_nonzero
end
end ProximityPrize.SubmissionLower.TransverseBudgetUse6814
