import ProximityPrize.SubmissionLower.Part.G033


section Compact_SecondJetContact
/-! The contact identity behind the exploratory second-derivative space.
This establishes the local algebra only, not the rank calculations or a
stronger protocol claim. Hasse derivatives avoid a characteristic-two
exception in the identity itself. -/
namespace ProximityPrize.SubmissionLower.SecondJetContact
open Polynomial
noncomputable section
set_option autoImplicit false

variable {K : Type*} [CommRing K]

theorem second_contact_residue (q : Polynomial K) :
    (Polynomial.X : Polynomial K)^3 ∣
      q - C (q.coeff 0) - Polynomial.X*q.derivative + Polynomial.X^2*hasseDeriv 2 q := by
  rw [X_pow_dvd_iff]
  intro d hd
  interval_cases d <;>
    simp [coeff_sub, coeff_add, coeff_X_pow_mul', coeff_X_mul,
      coeff_derivative, hasseDeriv_coeff] <;> ring

theorem exists_second_contact_expansion (q : Polynomial K) :
    ∃ U : Polynomial K,
      q - C (q.coeff 0) =
        Polynomial.X * (q.derivative - Polynomial.X*hasseDeriv 2 q + Polynomial.X^2*U) := by
  obtain ⟨U, hU⟩ := second_contact_residue q
  refine ⟨U, ?_⟩
  linear_combination hU

theorem taylor_second_contact (f : Polynomial K) (x : K) :
    ∃ U : Polynomial K,
      taylor x f - C (f.eval x) =
        Polynomial.X * ((taylor x f).derivative - Polynomial.X*hasseDeriv 2 (taylor x f) + Polynomial.X^2*U) := by
  simpa only [taylor_coeff_zero] using exists_second_contact_expansion (taylor x f)

end
end ProximityPrize.SubmissionLower.SecondJetContact

end Compact_SecondJetContact
