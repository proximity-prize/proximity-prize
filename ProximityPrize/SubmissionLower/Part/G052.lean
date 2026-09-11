import ProximityPrize.SubmissionLower.Part.G051


section Compact_SecondJetComponentRoots
/-! The fixed leading coefficient isolates exactly the components on which
mapped degree and high root multiplicity are retained. -/
namespace ProximityPrize.SubmissionLower.SecondJetComponentRoots
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open RCN002 RCN136
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K E : Type} [Field K] [Field E]

def coefficientMap (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] :
    MvPolynomial (Fin 4) K →+* CoordinateField E C :=
  (coordinateEvaluation E C).toRingHom.comp (surfaceMap φ)

def componentPolynomial (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) : Polynomial (CoordinateField E C) :=
  (asS P).map (coefficientMap φ C)

theorem evaluation_zero_iff (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (Q : MvPolynomial (Fin 3) E) : coordinateEvaluation E C Q = 0 ↔ Q ∈ C := by
  change Q ∈ RingHom.ker (coordinateEvaluation E C).toRingHom ↔ Q ∈ C
  rw [coordinateEvaluation_ker]

theorem degree_retained (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) (hlead : surfaceMap φ (asS P).leadingCoeff ∉ C) :
    componentPolynomial φ C P ≠ 0 ∧ (componentPolynomial φ C P).natDegree = (asS P).natDegree := by
  apply SecondJetCoefficientAvoidance.map_degree_preserved
  change coordinateEvaluation E C (surfaceMap φ (asS P).leadingCoeff) ≠ 0
  exact fun hz => hlead ((evaluation_zero_iff C _).mp hz)

theorem coefficients (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) (j : ℕ) :
    (componentPolynomial φ C P).coeff j =
      MvPolynomial.eval₂Hom (algebraMap E (CoordinateField E C)) (coordinate E C)
        (SecondJetFlagCoefficients.freeze (φ Polynomial.X)
          ((asS (MvPolynomial.map (φ.comp Polynomial.C) P)).coeff j)) := by
  rw [SecondJetSurfaceMap.frozen_mapped_coefficient]
  rw [componentPolynomial,Polynomial.coeff_map]
  change coordinateEvaluation E C _ = _
  rw [coordinateEvaluation_eq_aeval]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _)

theorem roots_retained (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K) (s k : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hF : surfaceMap φ F ∈ C) (hH : surfaceMap φ (RCN313.polyH K F) ∉ C)
    (hlead : surfaceMap φ (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ d ≤ k, F ∣ helper P F (s-d) d)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0) :
    (Polynomial.X-Polynomial.C (RCN064.movingRatio C
      (surfaceMap φ (RCN313.polyH K F)) (surfaceMap φ (RCN313.polyG K F))/2))^(k+1) ∣
      componentPolynomial φ C P := by
  have hf : coefficientMap φ C F = 0 := (evaluation_zero_iff C _).mpr hF
  have hh : coordinateEvaluation E C (surfaceMap φ (RCN313.polyH K F)) ≠ 0 :=
    fun hz => hH ((evaluation_zero_iff C _).mp hz)
  have h2e : (2 : CoordinateField E C) ≠ 0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap E (CoordinateField E C)).injective.ne h2
  have hfe : (k.factorial : CoordinateField E C) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (algebraMap E (CoordinateField E C)).injective.ne hfact
  have hden : coefficientMap φ C (2*RCN313.polyH K F) ≠ 0 := by
    rw [map_mul,map_ofNat]
    exact mul_ne_zero h2e hh
  have hr := SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd P F (coefficientMap φ C)
    s k hS hf hden (degree_retained φ C P hlead).1 hfe hdiv
  have heq : SecondJetCarrierDichotomy.ratio (coefficientMap φ C) F =
      RCN064.movingRatio C (surfaceMap φ (RCN313.polyH K F))
        (surfaceMap φ (RCN313.polyG K F))/2 := by
    simp only [SecondJetCarrierDichotomy.ratio,coefficientMap,RingHom.comp_apply,
      RCN064.movingRatio,map_mul,map_ofNat,AlgHom.toRingHom_eq_coe,RingHom.coe_coe]
    field_simp
    <;> ring
  rwa [heq] at hr

end
end ProximityPrize.SubmissionLower.SecondJetComponentRoots

end Compact_SecondJetComponentRoots
