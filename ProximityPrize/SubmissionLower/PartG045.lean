import ProximityPrize.SubmissionLower.PartG044


section Compact_SecondJetSurfaceMap
/-! Transporting coefficient flags to the generic carrier surface. -/
namespace ProximityPrize.SubmissionLower.SecondJetSurfaceMap
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetFlagCoefficients
open RCN136
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K E : Type*} [Field K] [Field E]

theorem coefficient_map (f : K →+* E) (P : Poly (K := K)) (j : ℕ) :
    (asS (MvPolynomial.map f P)).coeff j = MvPolynomial.map f ((asS P).coeff j) := by
  ext e
  rw [asS_coeff,MvPolynomial.coeff_map,MvPolynomial.coeff_map,asS_coeff]

theorem freeze_map_eq_surface (φ : Polynomial K →+* E) (P : MvPolynomial (Fin 4) K) :
    freeze (φ Polynomial.X) (MvPolynomial.map (φ.comp Polynomial.C) P) = surfaceMap φ P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [freeze]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P i hp =>
    simp only [map_mul,hp,MvPolynomial.map_X]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [freeze]
    · rw [surfaceMap_X_succ]
      fin_cases j <;> simp [freeze]

theorem frozen_mapped_coefficient (φ : Polynomial K →+* E) (P : Poly (K := K)) (j : ℕ) :
    freeze (φ Polynomial.X) ((asS (MvPolynomial.map (φ.comp Polynomial.C) P)).coeff j) =
      surfaceMap φ ((asS P).coeff j) := by
  rw [coefficient_map,freeze_map_eq_surface]

theorem mapped_support_bounds (f : K →+* E) (P : Poly (K := K)) (B U T : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T) :
    ∀ e ∈ (MvPolynomial.map f P).support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T := by
  intro e he
  exact hP e (MvPolynomial.support_map_subset f P he)

end
end ProximityPrize.SubmissionLower.SecondJetSurfaceMap

end Compact_SecondJetSurfaceMap
