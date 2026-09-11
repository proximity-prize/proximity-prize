import ProximityPrize.SubmissionLower.PartG049


section Compact_SecondJetCarrierDichotomy
/-! Over a carrier field, either a cleared derivative is proper or the
interpolant has the required high-multiplicity root. -/
namespace ProximityPrize.SubmissionLower.SecondJetCarrierDichotomy
open MvPolynomial SecondJetSupport SecondJetCoefficients
open SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K E : Type*} [Field K] [Field E]

def ratio (φ : MvPolynomial (Fin 4) K →+* E) (F : MvPolynomial (Fin 4) K) : E :=
  φ (RCN313.polyG K F)/φ (2*RCN313.polyH K F)

theorem mapped_helper (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (φ : MvPolynomial (Fin 4) K →+* E) (s d : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s) (hH : φ (2*RCN313.polyH K F) ≠ 0) :
    φ (helper P F (s-d) d) = φ (2*RCN313.polyH K F)^(s-d)*
      ((Polynomial.derivative)^[d] ((asS P).map φ)).eval (ratio φ F) := by
  rw [helper,map_cleared]
  have hdegree : ((asS ((pderiv 1)^[d] P)).map φ).natDegree ≤ s-d :=
    Polynomial.natDegree_map_le.trans (asS_derivative_degree P s d hS)
  have hrel : φ (2*RCN313.polyH K F)*ratio φ F = φ (RCN313.polyG K F) := by
    unfold ratio
    field_simp
  rw [cleared_eval _ (s-d) hdegree _ _ _ hrel,asS_iterate,← Polynomial.iterate_derivative_map]

theorem helper_or_multiplicity (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (φ : MvPolynomial (Fin 4) K →+* E) (s k : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s) (hF : φ F = 0)
    (hH : φ (2*RCN313.polyH K F) ≠ 0)
    (hP : (asS P).map φ ≠ 0) (hk : (k.factorial : E) ≠ 0) :
    (∃ d ≤ k, ¬ F ∣ helper P F (s-d) d) ∨
      (Polynomial.X-Polynomial.C (ratio φ F))^(k+1) ∣ (asS P).map φ := by
  rcases RootMultiplicityDichotomy.derivative_or_high_multiplicity
    ((asS P).map φ) hP (ratio φ F) k hk with hder | hroot
  · left
    obtain ⟨d,hd,hne⟩ := hder
    refine ⟨d,hd,?_⟩
    intro hdiv
    have hh := map_dvd φ hdiv
    rw [hF,zero_dvd_iff,mapped_helper P F φ s d hS hH] at hh
    exact (mul_ne_zero (pow_ne_zero _ hH) hne) hh
  · exact Or.inr hroot


theorem multiplicity_of_helpers_dvd (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (φ : MvPolynomial (Fin 4) K →+* E) (s k : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s) (hF : φ F = 0)
    (hH : φ (2*RCN313.polyH K F) ≠ 0)
    (hP : (asS P).map φ ≠ 0) (hk : (k.factorial : E) ≠ 0)
    (hdiv : ∀ d ≤ k, F ∣ helper P F (s-d) d) :
    (Polynomial.X-Polynomial.C (ratio φ F))^(k+1) ∣ (asS P).map φ := by
  rcases helper_or_multiplicity P F φ s k hS hF hH hP hk with h | h
  · obtain ⟨d,hd,hn⟩ := h
    exact False.elim (hn (hdiv d hd))
  · exact h

end
end ProximityPrize.SubmissionLower.SecondJetCarrierDichotomy

end Compact_SecondJetCarrierDichotomy
