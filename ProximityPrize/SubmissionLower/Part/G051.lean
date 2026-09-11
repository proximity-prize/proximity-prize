import ProximityPrize.SubmissionLower.Part.G050


section Compact_SecondJetCoefficientAvoidance
/-! The conservative coefficient avoidance gate makes every nonzero S
coefficient proper with respect to a carrier of larger Z degree. -/
namespace ProximityPrize.SubmissionLower.SecondJetCoefficientAvoidance
open MvPolynomial SecondJetSupport SecondJetCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K]

theorem coefficient_z_degree (P : Poly (K := K)) (L j : ℕ)
    (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L) :
    ((asS P).coeff j).degreeOf 3 ≤ L-j := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  have hh := hP _ (coefficient_support P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  rw [h1,h2,h3,h4] at hh
  omega

theorem coefficient_not_dvd (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (L j : ℕ) (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L)
    (hF : L < F.degreeOf 3) (hC : (asS P).coeff j ≠ 0) :
    ¬ F ∣ (asS P).coeff j := by
  intro hdiv
  have hh := RCN081.degreeOf_le_of_dvd 3 F ((asS P).coeff j) hdiv hC
  have hc := coefficient_z_degree P L j hP
  omega

theorem leading_not_dvd (P : Poly (K := K)) (hP : P ≠ 0)
    (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hPL : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L) (hF : L < F.degreeOf 3) :
    (asS P).leadingCoeff ≠ 0 ∧ ¬ F ∣ (asS P).leadingCoeff := by
  have hn : asS P ≠ 0 := by
    intro hz
    apply hP
    apply (asS (K := K)).injective
    simpa only [map_zero] using hz
  have hc := Polynomial.leadingCoeff_ne_zero.mpr hn
  exact ⟨hc,coefficient_not_dvd P F L (asS P).natDegree hPL hF hc⟩

theorem map_degree_preserved {R T : Type*} [CommRing R] [CommRing T]
    (P : Polynomial R) (φ : R →+* T) (hC : φ P.leadingCoeff ≠ 0) :
    P.map φ ≠ 0 ∧ (P.map φ).natDegree = P.natDegree := by
  constructor
  · intro hz
    have hh := congrArg (fun Q : Polynomial T => Q.coeff P.natDegree) hz
    simp only [Polynomial.coeff_map,Polynomial.coeff_zero,Polynomial.coeff_natDegree] at hh
    exact hC hh
  · exact Polynomial.natDegree_map_eq_iff.mpr (Or.inl hC)

end
end ProximityPrize.SubmissionLower.SecondJetCoefficientAvoidance

end Compact_SecondJetCoefficientAvoidance
