import ProximityPrize.SubmissionLower.ContactAgreementFactorScaling
import ProximityPrize.SubmissionLower.ContactGenericSurface
import ProximityPrize.SubmissionLower.ContactReconstructionFieldMembership

/-! Canonical reconstruction and proper agreement cuts survive contraction
from a product surface to its regular active factor. -/

namespace ProximityPrize.SubmissionLower.ContactFactorReconstruction

open ContactDifferentialRing ContactTaylorNumerators ContactRegularPoint
open ContactPolynomiality ContactGlobalPolynomiality DifferentialTaylorCoefficients
open ContactAgreementEvaluation
open ContactNumeratorFactorScaling ContactAgreementFactorScaling
open ContactGenericSurface
open ContactReconstructionFieldMembership

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 15000

variable {K L Ω : Type} [Field K] [Field L] [Field Ω]

theorem map_agreementNumerator_base
    (c : K →+* L) (F : Poly4 K) (w : ℕ) (a : ℕ → K) (x u0 u1 : K) :
    MvPolynomial.map c (agreementNumerator F w a x u0 u1) =
      agreementNumerator (MvPolynomial.map c F) w (fun j => c (a j))
        (c x) (c u0) (c u1) := by
  simp only [agreementNumerator,clearedTaylorNumerator,commonNumeratorTerm,
    affineSeedPolynomial,map_sub,map_sum,map_add,map_mul,map_pow,MvPolynomial.map_C,
    MvPolynomial.map_X,map_numerator,polyH,MvPolynomial.pderiv_map]

/-- The canonical Taylor polynomial of a regular product branch is the
canonical Taylor polynomial of its active factor. -/
theorem globalPolynomial_mul_factor
    (c : K →+* L) (F Q : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom c v F = 0)
    (hQ : MvPolynomial.eval₂Hom c v Q ≠ 0)
    (hregF : MvPolynomial.eval₂Hom c v (polyH K F) ≠ 0)
    (hprod : MvPolynomial.eval₂Hom c v (F*Q) = 0)
    (hregprod : MvPolynomial.eval₂Hom c v (polyH K (F*Q)) ≠ 0)
    (w : ℕ) :
    globalPolynomial c (F*Q) v hprod hregprod w =
      globalPolynomial c F v hF hregF w := by
  let ev := MvPolynomial.eval₂Hom c v
  change ev F = 0 at hF
  change ev Q ≠ 0 at hQ
  change ev (polyH K F) ≠ 0 at hregF
  have hHscale : ev (polyH K (F*Q)) = ev (polyH K F) * ev Q := by
    unfold polyH
    rw [MvPolynomial.pderiv_mul]
    simp only [map_add,map_mul,hF,zero_mul,add_zero]
  have hNscale (j : ℕ) : ev (numerator K (F*Q) j) =
      ev Q^(2*j)*ev (numerator K F j) := by
    obtain ⟨A,hA⟩ := factor_dvd_numerator_sub_power F Q j
    have h := congrArg ev hA
    simp only [map_sub,map_mul,map_pow,hF,zero_mul] at h
    exact sub_eq_zero.mp h
  have hrecon : reconstructedPolynomial c (F*Q) v hprod hregprod w =
      reconstructedPolynomial c F v hF hregF w := by
    ext j
    simp only [reconstructedPolynomial,jetPolynomial_coeff]
    by_cases hj : j<w+1
    · rw [if_pos hj,if_pos hj]
      rw [jetCoefficient_eq_evaluated_numerator,
        jetCoefficient_eq_evaluated_numerator]
      change ev (numerator K (F*Q) j) * (ev (polyH K (F*Q)))⁻¹^(2*j) /
          (j.factorial : L) =
        ev (numerator K F j) * (ev (polyH K F))⁻¹^(2*j) /
          (j.factorial : L)
      rw [hNscale,hHscale,mul_inv,mul_pow]
      have hcancel : ev Q^(2*j)*(ev Q)⁻¹^(2*j)=1 := by
        rw [← mul_pow,mul_inv_cancel₀ hQ,one_pow]
      calc
        _ = (ev Q^(2*j)*(ev Q)⁻¹^(2*j)) *
            (ev (numerator K F j)*(ev (polyH K F))⁻¹^(2*j)) /
              (j.factorial : L) := by ring
        _ = _ := by rw [hcancel,one_mul]
    · rw [if_neg hj,if_neg hj]
  unfold globalPolynomial
  rw [hrecon]

end
end ProximityPrize.SubmissionLower.ContactFactorReconstruction
