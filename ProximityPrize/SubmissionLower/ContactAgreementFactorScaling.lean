import ProximityPrize.SubmissionLower.ContactNumeratorFactorScaling

/-! Scaling of cleared agreement numerators along an original factor. -/

namespace ProximityPrize.SubmissionLower.ContactAgreementFactorScaling

open scoped BigOperators
open ContactDifferentialRing ContactTaylorNumerators
open ContactNumeratorFactorScaling

noncomputable section

variable {K : Type*} [Field K]

private theorem commonTerm_scaling_mod (F Q : Poly4 K) (w j : ℕ) (hj : j≤w)
    (c : ℕ → K) (x : K) :
    Ideal.Quotient.mk (factorIdeal F) (commonNumeratorTerm (F*Q) w c x j) =
      Ideal.Quotient.mk (factorIdeal F) Q^(2*w) *
        Ideal.Quotient.mk (factorIdeal F) (commonNumeratorTerm F w c x j) := by
  let ev := Ideal.Quotient.mk (factorIdeal F)
  have he : 2*j+2*(w-j)=2*w := by omega
  unfold commonNumeratorTerm
  simp only [map_mul,map_pow]
  rw [numerator_scaling_mod, polyH_mul_factor_mod, mul_pow]
  calc
    _ = ev Q^(2*j+2*(w-j)) *
        (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
          ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j) := by
      rw [pow_add]
      ring
    _ = ev Q^(2*w) *
        (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
          ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j) := by rw [he]
    _ = _ := by ring

private theorem seed_scaling_mod (F Q : Poly4 K) (w : ℕ) (u0 u1 : K) :
    Ideal.Quotient.mk (factorIdeal F)
        (affineSeedPolynomial u0 u1*polyH K (F*Q)^(2*w)) =
      Ideal.Quotient.mk (factorIdeal F) Q^(2*w) *
        Ideal.Quotient.mk (factorIdeal F)
          (affineSeedPolynomial u0 u1*polyH K F^(2*w)) := by
  simp only [map_mul,map_pow]
  rw [polyH_mul_factor_mod,mul_pow]
  ring

theorem agreementNumerator_scaling_mod (F Q : Poly4 K) (w : ℕ)
    (c : ℕ → K) (x u0 u1 : K) :
    Ideal.Quotient.mk (factorIdeal F) (agreementNumerator (F*Q) w c x u0 u1) =
      Ideal.Quotient.mk (factorIdeal F) Q^(2*w) *
        Ideal.Quotient.mk (factorIdeal F) (agreementNumerator F w c x u0 u1) := by
  let ev := Ideal.Quotient.mk (factorIdeal F)
  have hsum : ev (clearedTaylorNumerator (F*Q) w c x) =
      ev Q^(2*w)*ev (clearedTaylorNumerator F w c x) := by
    unfold clearedTaylorNumerator
    simp only [map_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact commonTerm_scaling_mod F Q w j (by have := Finset.mem_range.mp hj; omega) c x
  unfold agreementNumerator
  rw [map_sub,map_sub,hsum,seed_scaling_mod]
  ring

/-- Divisibility form used to contract proper agreement cuts. -/
theorem factor_dvd_agreement_sub_power (F Q : Poly4 K) (w : ℕ)
    (c : ℕ → K) (x u0 u1 : K) :
    F ∣ agreementNumerator (F*Q) w c x u0 u1-
      Q^(2*w)*agreementNumerator F w c x u0 u1 := by
  rw [← Ideal.mem_span_singleton]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub,map_mul,map_pow,
    agreementNumerator_scaling_mod,sub_self]

end
end ProximityPrize.SubmissionLower.ContactAgreementFactorScaling
