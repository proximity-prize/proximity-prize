import ProximityPrize.SubmissionLower.ContactPolynomialRecovery
import ProximityPrize.SubmissionLower.ContactTailClosure

/-! Naturality and regular-jet uniqueness for polynomial reconstruction.
These are the algebraic recentering steps needed for the first-tail identity
branch; no assertion about coefficient-curve descent is assumed here. -/

namespace ProximityPrize.SubmissionLower.ContactPolynomialRecenter

open ContactDifferentialRing ContactRegularPoint ContactPolynomiality
open ContactTaylorNumerators ContactAgreementEvaluation ContactPolynomialSolutions
open ContactGlobalPolynomiality ContactPolynomialRecovery ContactTranslation
open DifferentialTaylorCoefficients ContactTailClosure ContactInterpolation

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 30000

variable {K L M : Type} [Field K] [Field L] [Field M]

/-- The existing low-weight first-tail theorem applied to the canonical
reconstruction, rather than an unspecified existential polynomial. -/
theorem canonical_polynomiality_of_first_tail
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F=0)
    (hreg : MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2 : Fin 4) F)≠0)
    (p bound w seedCap slopeCap : ℕ) [CharP L p]
    (hw : 1≤w) (hshort : w+1≤bound) (hchar : bound<p)
    (hcaps : F ∈ globalCoefficientBox K bound w seedCap slopeCap)
    (hdiv : F ∣ numerator K F (w+1)) :
    specialization L (globalPolynomial coefficients F v hF hreg w) (v 3)
      (MvPolynomial.map coefficients F)=0 := by
  apply global_polynomiality_of_all_tails coefficients F v hF hreg
    p bound w seedCap slopeCap hw hshort hchar hcaps
  intro j hj _
  exact all_tail_jets_zero_of_first_tail_dvd coefficients F v hF hreg w hdiv j hj

end
end ProximityPrize.SubmissionLower.ContactPolynomialRecenter
