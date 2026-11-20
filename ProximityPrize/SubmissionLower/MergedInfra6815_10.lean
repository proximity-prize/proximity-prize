import ProximityPrize.SubmissionLower.LowerGeometry
set_option Elab.async false

-- Modified from prior Proximity Prize sources.
namespace ProximityPrize.SubmissionLower.SecondJetTotalAvoidance
open MvPolynomial SecondJetSupport SecondJetCoefficients RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K : Type*} [Field K]

theorem coefficient_total_weight (P : Poly (K := K)) (L j : ℕ)
    (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L) :
    wt residualTotalWeights ((asS P).coeff j) ≤ L-j := by
  apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
  intro e he
  have hh := hP _ (coefficient_support P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  rw [h1,h2,h3,h4] at hh
  simp [residualTotalWeights, RCN081.weight_fin4]
  omega

theorem coefficient_not_dvd (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (L j : ℕ) (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L)
    (hF : L < wt residualTotalWeights F) (hC : (asS P).coeff j ≠ 0) :
    ¬ F ∣ (asS P).coeff j := by
  intro hdiv
  have hh := RCN081.weightedTotalDegree_le_of_dvd residualTotalWeights F
    ((asS P).coeff j) hdiv hC
  have hc := coefficient_total_weight P L j hP
  change wt residualTotalWeights F ≤ wt residualTotalWeights ((asS P).coeff j) at hh
  omega

theorem leading_not_dvd (P : Poly (K := K)) (hP : P ≠ 0)
    (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hPL : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L)
    (hF : L < wt residualTotalWeights F) :
    (asS P).leadingCoeff ≠ 0 ∧ ¬ F ∣ (asS P).leadingCoeff := by
  have hn : asS P ≠ 0 := by
    intro hz
    apply hP
    apply (asS (K := K)).injective
    simpa only [map_zero] using hz
  have hc := Polynomial.leadingCoeff_ne_zero.mpr hn
  exact ⟨hc,coefficient_not_dvd P F L (asS P).natDegree hPL hF hc⟩

end
end ProximityPrize.SubmissionLower.SecondJetTotalAvoidance
