import ProximityPrize.SubmissionLower.MovingSourceLinearOwnerData6814

/-! Transport the actual global tail cuts, their DVR orders, and their
first proper delays. The code-coordinate scalar in globalTailCut is
handled explicitly; it is a unit at the generic code coordinate. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN086 RCN136 RCN313
open MovingSourceFlowNumerator6814 MovingSourceDenominatorChange6814

variable {K Ω R : Type} [Field K] [Field Ω] [CommRing R] [IsDomain R]
local notation "Poly" => MvPolynomial (Fin 4) K

theorem base_tails_associated
    (ev : Poly →+* R) (F H G : Poly) (n : ℕ) (hF : ev F=0)
    (hOld : IsUnit (ev (polyH K F))) (hNew : IsUnit (ev H))
    (hdiv : F∣H^(2*(n+2))*numerator K F (n+2)-
      (polyH K F)^(2*(n+2))*numerators H G (n+2)) :
    Associated (ev (RCN055.baseNumerator F n)) (ev (numerators H G (n+2))) := by
  have hh := tails_associated ev F H G (n+2) hF hOld hNew hdiv
  rw [RCN055.numerator_eq_H_cube,map_mul,map_pow] at hh
  exact (associated_isUnit_mul_left_iff (hOld.pow 3)).mp hh

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

theorem global_tail_orders [IsDiscreteValuationRing R]
    (phi : Polynomial K →+* Ω) (hphi : Function.Injective phi)
    (ev : MvPolynomial (Fin 3) Ω →+* R) (F H G : Poly) (n : ℕ)
    (hF : ev (surfaceMap phi F)=0)
    (hOld : IsUnit (ev (surfaceMap phi (polyH K F)))) (hNew : IsUnit (ev (surfaceMap phi H)))
    (hdiv : F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n) :
    IsDiscreteValuationRing.addVal R (ev (globalTailCut phi F n))=
      IsDiscreteValuationRing.addVal R (ev (surfaceMap phi (numerators H G n))) :=
  (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr
    (global_tails_associated phi hphi ev F H G n hF hOld hNew hdiv)

theorem proper_delay_iff
    (phi : Polynomial K →+* Ω) (hphi : Function.Injective phi)
    (ev : MvPolynomial (Fin 3) Ω →+* R) (F H G : Poly)
    (hF : ev (surfaceMap phi F)=0)
    (hOld : IsUnit (ev (surfaceMap phi (polyH K F)))) (hNew : IsUnit (ev (surfaceMap phi H)))
    (hdiv : ∀ n, F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n)
    (start delay : ℕ) :
    ((∀ j<delay, ¬IsUnit (ev (globalTailCut phi F (start+j)))) ∧
      IsUnit (ev (globalTailCut phi F (start+delay)))) ↔
    ((∀ j<delay, ¬IsUnit (ev (surfaceMap phi (numerators H G (start+j))))) ∧
      IsUnit (ev (surfaceMap phi (numerators H G (start+delay))))) := by
  have hu (n : ℕ) : IsUnit (ev (globalTailCut phi F n)) ↔
      IsUnit (ev (surfaceMap phi (numerators H G n))) :=
    (global_tails_associated phi hphi ev F H G n hF hOld hNew (hdiv n)).isUnit_iff
  simp_rw [hu]

theorem persistent_iff
    (phi : Polynomial K →+* Ω) (hphi : Function.Injective phi)
    (ev : MvPolynomial (Fin 3) Ω →+* R) (F H G : Poly)
    (hF : ev (surfaceMap phi F)=0)
    (hOld : IsUnit (ev (surfaceMap phi (polyH K F)))) (hNew : IsUnit (ev (surfaceMap phi H)))
    (hdiv : ∀ n, F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n)
    (start : ℕ) :
    (∀ j, ¬IsUnit (ev (globalTailCut phi F (start+j)))) ↔
      (∀ j, ¬IsUnit (ev (surfaceMap phi (numerators H G (start+j))))) := by
  have hu (n : ℕ) : IsUnit (ev (globalTailCut phi F n)) ↔
      IsUnit (ev (surfaceMap phi (numerators H G n))) :=
    (global_tails_associated phi hphi ev F H G n hF hOld hNew (hdiv n)).isUnit_iff
  simp_rw [hu]

#print axioms global_tail_orders
#print axioms proper_delay_iff
#print axioms persistent_iff
end
end ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814
