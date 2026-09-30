import ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814
namespace ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN086 RCN136 RCN313
open MovingSourceFlowNumerator6814 MovingSourceDenominatorChange6814

variable {K Ω R : Type} [Field K] [Field Ω] [CommRing R] [IsDomain R]
local notation "Poly" => MvPolynomial (Fin 4) K

theorem global_tails_associated
    (phi : Polynomial K →+* Ω) (hphi : Function.Injective phi)
    (ev : MvPolynomial (Fin 3) Ω →+* R) (F H G : Poly) (n : ℕ)
    (hF : ev (surfaceMap phi F)=0)
    (hOld : IsUnit (ev (surfaceMap phi (polyH K F)))) (hNew : IsUnit (ev (surfaceMap phi H)))
    (hdiv : F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n) :
    Associated (ev (globalTailCut phi F n)) (ev (surfaceMap phi (numerators H G n))) := by
  have hh := tails_associated (ev.comp (surfaceMap phi)) F H G n hF hOld hNew hdiv
  have hu : IsUnit ((-phi Polynomial.X)^n) :=
    isUnit_iff_ne_zero.mpr (tail_scalar_ne_zero phi hphi n)
  have hu' : IsUnit (ev (MvPolynomial.C ((-phi Polynomial.X)^n))) :=
    (hu.map (MvPolynomial.C : Ω →+* MvPolynomial (Fin 3) Ω)).map ev
  rw [globalTailCut_eq,map_mul]
  exact (associated_mul_unit_left _ _ hu').trans hh

end
end ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814
