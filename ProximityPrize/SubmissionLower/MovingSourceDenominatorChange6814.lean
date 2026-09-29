import ProximityPrize.SubmissionLower.MovingSourceFlowNumerator6814

/-! A denominator change on the faithful carrier field preserves every
tail. The field derivation is constructed here from the original carrier;
it is not assumed to act correctly on the replacement flow. -/
namespace ProximityPrize.SubmissionLower.MovingSourceDenominatorChange6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN313
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814 MovingSourceCarrierField6814

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K

theorem old_flow_stable (F : Poly) :
    ∀ P ∈ Ideal.span ({F} : Set Poly), flow (polyH K F) (polyG K F) P∈Ideal.span ({F} : Set Poly) := by
  intro P hP
  rw [Ideal.mem_span_singleton] at hP ⊢
  apply flow_preserves_carrier F (polyH K F) (polyG K F) ?_ P hP
  rw [mul_comm (polyH K F),sub_self]
  exact dvd_zero F

def quotientD (F : Poly) : Derivation K (CarrierRing F) (CarrierRing F) :=
  RCN077.quotientDerivation (flow (polyH K F) (polyG K F)) _ (old_flow_stable F)

def carrierD (F : Poly) [Fact (Irreducible F)] : Derivation K (CarrierField F) (CarrierField F) :=
  (carrierMap F (polyH K F))⁻¹ •
    RCN188.localizationDerivation (nonZeroDivisors (CarrierRing F)) (quotientD F)

theorem carrierD_apply (F : Poly) [Fact (Irreducible F)]
    (hH : carrierMap F (polyH K F)≠0) (P : Poly) :
    carrierD F (carrierMap F P)=carrierMap F (pderiv 0 P)+
      carrierMap F (MvPolynomial.X 2)*carrierMap F (pderiv 1 P)+
      carrierMap F (polyG K F)*(carrierMap F (polyH K F))⁻¹*carrierMap F (pderiv 2 P) := by
  change (carrierMap F (polyH K F))⁻¹*
    RCN188.localizationDerivation (nonZeroDivisors (CarrierRing F)) (quotientD F)
      (algebraMap (CarrierRing F) (CarrierField F) (Ideal.Quotient.mk _ P))=_
  rw [RCN188.localizationDerivation_algebraMap,quotientD,RCN077.quotientDerivation_mk]
  change (carrierMap F (polyH K F))⁻¹*carrierMap F (flow (polyH K F) (polyG K F) P)=_
  rw [flow_apply]
  simp only [map_add,map_mul]
  field_simp

theorem carrierD_new_flow (F : Poly) [Fact (Irreducible F)] (H G : Poly)
    (hOld : carrierMap F (polyH K F)≠0) (hNew : carrierMap F H≠0)
    (hcross : F∣H*polyG K F-G*polyH K F) (P : Poly) :
    carrierD F (carrierMap F P)=carrierMap F (pderiv 0 P)+
      carrierMap F (MvPolynomial.X 2)*carrierMap F (pderiv 1 P)+
      carrierMap F G*(carrierMap F H)⁻¹*carrierMap F (pderiv 2 P) := by
  have hh := (carrierMap_zero_iff F _).mpr hcross
  simp only [map_sub,map_mul] at hh
  have he : carrierMap F (polyG K F)*(carrierMap F (polyH K F))⁻¹=
      carrierMap F G*(carrierMap F H)⁻¹ := by
    field_simp
    linear_combination hh
  rw [carrierD_apply F hOld P,he]

theorem denominator_change (F : Poly) [Fact (Irreducible F)] (H G : Poly)
    (hOld : carrierMap F (polyH K F)≠0) (hNew : carrierMap F H≠0)
    (hcross : F∣H*polyG K F-G*polyH K F) (n : ℕ) :
    F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n := by
  apply (carrierMap_zero_iff F _).mp
  simp only [map_sub,map_mul,map_pow]
  have hh := numerator_cross_eq (carrierD F) (carrierMap F) (polyH K F) (polyG K F)
    H G hOld hNew (carrierD_apply F hOld) (carrierD_new_flow F H G hOld hNew hcross) n
  rw [old_numerators] at hh
  linear_combination hh

theorem linear_denominator_change [CharP K 2130706433]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJ : J≠0) (hs : J.degreeOf 1=1)
    (F : Poly) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (T : ℕ) (hshape : ∀ e ∈ J.support, e 1+e 2+e 3+e 4≤T)
    (hFT : T<RCN234.wt RCN156.residualTotalWeights F)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).eval
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=0) (n : ℕ) :
    F∣(linearH J)^(2*n)*numerator K F n-
      (polyH K F)^(2*n)*numerators (linearH J) (linearG J) n := by
  have hH : carrierMap F (polyH K F)≠0 := by
    intro hz
    apply carrier_H_nonzero F hpos hsmall
    rw [map_mul,hz,mul_zero]
  exact denominator_change F (linearH J) (linearG J) hH
    (linearH_nonzero_on_carrier J hJ hs F T hshape hFT)
    (carrier_cross_identity J hs F hpos hsmall hroot) n

/-- In a local domain where both denominators are units, the old and new
tails are associated. This preserves local multiplicities as well as zeros. -/
theorem tails_associated {R : Type} [CommRing R] [IsDomain R]
    (ev : Poly →+* R) (F H G : Poly) (n : ℕ) (hF : ev F=0)
    (hOld : IsUnit (ev (polyH K F))) (hNew : IsUnit (ev H))
    (hdiv : F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n) :
    Associated (ev (numerator K F n)) (ev (numerators H G n)) := by
  have hh := map_dvd ev hdiv
  rw [hF,zero_dvd_iff,map_sub,map_mul,map_mul,map_pow,map_pow,sub_eq_zero] at hh
  have he : ev (numerator K F n)*(ev H)^(2*n)=
      ev (numerators H G n)*(ev (polyH K F))^(2*n) := by simpa only [mul_comm] using hh
  apply associated_of_dvd_dvd
  · apply (hOld.pow (2*n)).dvd_mul_right.mp
    rw [←he]
    exact dvd_mul_right _ _
  · apply (hNew.pow (2*n)).dvd_mul_right.mp
    rw [he]
    exact dvd_mul_right _ _

#print axioms linear_denominator_change
#print axioms tails_associated
end
end ProximityPrize.SubmissionLower.MovingSourceDenominatorChange6814
