import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFreshCoefficientFieldGenerationResearch
import ProximityPrize.SubmissionLower.ContactTrdegTower6731Research

/-! Removing the one fresh rational-function parameter from the recovered
coefficient field. -/

namespace ProximityPrize.SubmissionLower.ContactCoefficientFieldTrdeg6731Research

open ContactFreshCoefficientFieldGenerationResearch

noncomputable section

variable {k L : Type} [Field k] [Field L] [Algebra k L]

def baseCoefficientField (P : Polynomial L) (γ : L) : IntermediateField k L :=
  IntermediateField.adjoin k
    (insert γ (Set.range (fun j : ℕ => P.coeff j)))

theorem baseCoefficientField_map_le (P : Polynomial L) (γ : L) :
    (baseCoefficientField (k := k) P γ).map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤
      coefficientField (k := k) P γ := by
  rw [IntermediateField.map_le_iff_le_comap]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases hx with h | hx
  · rw [h]
    change algebraMap L (RatFunc L) γ ∈ coefficientField (k := k) P γ
    exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
  obtain ⟨j,hj⟩ := hx
  rw [← hj]
  change algebraMap L (RatFunc L) (P.coeff j) ∈ coefficientField (k := k) P γ
  exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))

/-- A two-parameter bound on the field recovered after adding tau becomes a
one-parameter bound on the genuine coefficient field. -/
theorem baseCoefficientField_trdeg_le_one
    (P : Polynomial L) (γ : L)
    (hE : Algebra.trdeg k (coefficientField (k := k) P γ) ≤ 2) :
    Algebra.trdeg k (baseCoefficientField (k := k) P γ) ≤ 1 := by
  apply ContactTrdegTower6731Research.coefficient_trdeg_le_one_of_rational_extension
    (B := baseCoefficientField (k := k) P γ)
    (E := coefficientField (k := k) P γ)
    (baseCoefficientField_map_le P γ) _ hE
  exact IntermediateField.subset_adjoin k _ (Or.inl rfl)

end
end ProximityPrize.SubmissionLower.ContactCoefficientFieldTrdeg6731Research
