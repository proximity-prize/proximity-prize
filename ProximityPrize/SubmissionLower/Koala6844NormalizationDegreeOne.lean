import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryPrimitiveLiftDegrees
import ProximityPrize.SubmissionLower.Koala6844NormalizationClassify


namespace ProximityPrize.SubmissionLower.Koala6844Separated

open MvPolynomial Koala6844HighOrdinary Koala6844Comparison
open Koala6844CoefficientSystem (coefficientPolynomial)
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K]

private theorem from_seed_support (P : SeedCoefficients K) (j : ℕ) (z : Fin 2 →₀ ℕ)
    (hz : z ∈ (P.coeff j).support) :
    ∃ e ∈ (retainCarrier (carrierOfSeedCoefficients P)).support, e 3 = z 0 ∧ e 4 = z 1 := by
  let R := (MvPolynomial.optionEquivLeft K (Fin 2)).symm P
  let f := carrierCoordinates ∘ carrierCoefficientCoordinates
  let d := z.optionElim j
  have hdf : d ∈ R.support := by
    apply MvPolynomial.mem_support_iff.mpr
    have he := MvPolynomial.optionEquivLeft_coeff_coeff K R j z
    change ((((MvPolynomial.optionEquivLeft K (Fin 2))
      ((MvPolynomial.optionEquivLeft K (Fin 2)).symm P)).coeff j).coeff z) = R.coeff d at he
    rw [AlgEquiv.apply_symm_apply] at he
    exact he ▸ MvPolynomial.mem_support_iff.mp hz
  have hf : Function.Injective f := by
    change ∀ i j : Option (Fin 2), f i = f j → i = j
    decide
  have hLift : retainCarrier (carrierOfSeedCoefficients P) = MvPolynomial.rename f R := by
    rw [retainCarrier, carrierOfSeedCoefficients]
    change MvPolynomial.rename carrierCoordinates (MvPolynomial.rename carrierCoefficientCoordinates R) = _
    rw [MvPolynomial.rename_rename]
  refine ⟨Finsupp.mapDomain f d, ?_, ?_, ?_⟩
  · rw [hLift, MvPolynomial.support_rename_of_injective hf]
    exact Finset.mem_image.mpr ⟨d, hdf, rfl⟩
  · change Finsupp.mapDomain f d (f (some 0)) = _
    rw [Finsupp.mapDomain_apply_of_injective hf]
    simp [d]
  · change Finsupp.mapDomain f d (f (some 1)) = _
    rw [Finsupp.mapDomain_apply_of_injective hf]
    simp [d]

private theorem coefficientPolynomial_zero_off_constant (P : SeedCoefficients K)
    (hwt : weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients P)) = 0)
    (z : Fin 2 →₀ ℕ) (hz : z ≠ 0) (δ : ℕ) : coefficientPolynomial P z δ = 0 := by
  unfold coefficientPolynomial
  apply Finset.sum_eq_zero
  intro j _
  suffices (P.coeff j).coeff z = 0 by rw [this, Polynomial.monomial_zero_right]
  by_contra h
  obtain ⟨e, he, h₀, h₁⟩ := from_seed_support P j z (MvPolynomial.mem_support_iff.mpr h)
  have hdegree := MvPolynomial.le_weightedTotalDegree totalWeights he
  change Finsupp.weight totalWeights e ≤ weightDegree totalWeights
    (retainCarrier (carrierOfSeedCoefficients P)) at hdegree
  rw [hwt, total_weight, h₀, h₁] at hdegree
  apply hz
  ext i
  fin_cases i
  · change z 0 = 0
    omega
  · change z 1 = 0
    omega

private theorem value_coefficient_weights_zero (q : SymbolicRow (SeedRing K))
    (hf : q.first ≠ 0) (hs : q.second ≠ 0)
    (hdegree : weightDegree totalWeights (primitiveRowLift q) ≤ 1) :
    weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.first)) = 0 ∧
      weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.second)) = 0 := by
  have hfirst : retainCarrier (carrierOfSeedCoefficients q.first) ≠ 0 := fun hz =>
    carrierOfSeedCoefficients_ne_zero hf (retainCarrier_injective (by simpa using hz))
  have hsecond : retainCarrier (carrierOfSeedCoefficients q.second) ≠ 0 := fun hz =>
    carrierOfSeedCoefficients_ne_zero hs (retainCarrier_injective (by simpa using hz))
  rw [primitiveRowLift_weight_max, weight_mul_eq _ hfirst (MvPolynomial.X_ne_zero _),
    weight_mul_eq _ hsecond (MvPolynomial.X_ne_zero _), weight_X, weight_X] at hdegree
  change max (max (weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.beta)))
    (weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.first)) + 1))
    (weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.second)) + 1) ≤ 1 at hdegree
  exact ⟨by omega, by omega⟩

theorem all_minors_singular_of_total_weight_le_one (q : SymbolicRow (SeedRing K))
    (hf : q.first ≠ 0) (hs : q.second ≠ 0) (δ : ℕ)
    (hdegree : weightDegree totalWeights (primitiveRowLift q) ≤ 1) :
    ∀ keys : Fin 4 → (Fin 2 →₀ ℕ), (Koala6844RankFour.matrix q keys δ).det = 0 := by
  classical
  obtain ⟨hfirst, hsecond⟩ := value_coefficient_weights_zero q hf hs hdegree
  intro keys
  let M := Koala6844RankFour.matrix q keys δ
  let a := coefficientPolynomial q.first 0 δ
  let b := coefficientPolynomial q.second 0 δ
  have hcol₀ (i : Fin 4) : M i 0 = if keys i = 0 then a else 0 := by
    change coefficientPolynomial q.first (keys i) δ = _
    by_cases hz : keys i = 0
    · simp [hz, a]
    · exact (coefficientPolynomial_zero_off_constant q.first hfirst _ hz δ).trans (ite_eq_right hz).symm
  have hcol₂ (i : Fin 4) : M i 2 = if keys i = 0 then b else 0 := by
    change coefficientPolynomial q.second (keys i) δ = _
    by_cases hz : keys i = 0
    · simp [hz, b]
    · exact (coefficientPolynomial_zero_off_constant q.second hsecond _ hz δ).trans (ite_eq_right hz).symm
  change M.det = 0
  by_cases ha : a = 0
  · exact Matrix.det_eq_zero_of_column_eq_zero 0 (fun i ↦ by simp [hcol₀, ha])
  apply Matrix.det_eq_zero_of_not_linearIndependent_cols
  intro hLI
  let v : Fin 4 → Polynomial K := ![b, 0, -a, 0]
  have hv : ∑ j, v j • (fun i ↦ Mᵀ j i) = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, Fin.sum_univ_succ,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero, Matrix.transpose_apply]
    change b * M i 0 + (0 * M i 1 + (-a * M i 2 + 0 * M i 3)) = 0
    rw [hcol₀, hcol₂]
    split_ifs <;> ring
  exact ha (neg_eq_zero.mp ((Fintype.linearIndependent_iff.mp hLI v hv) 2))

end

end ProximityPrize.SubmissionLower.Koala6844Separated

namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open ProximityPrize.Benchmark
open Koala6844Comparison (SymbolicRow SeedRing primitiveExcess primitiveRowLift)
open Koala6844HighOrdinary (weightDegree totalWeights)

theorem normal_form_of_degree_one
    {received : Koala6844BenchmarkCases.ReceivedWords}
    {retained : Finset IRSProfile.Field} {selected : IRSProfile.Field → Polynomial IRSProfile.Field}
    {q : SymbolicRow (SeedRing IRSProfile.Field)}
    (h : Koala6844BenchmarkRetention.RetainedComparison received retained selected q)
    (hc : weightDegree totalWeights (primitiveRowLift q) ≤ 1) :
    Nonempty (Koala6844Separation.NormalForm q 131071 (primitiveExcess 131071 q)) :=
  normal_form_of_retained_singular h
    (Koala6844Separated.all_minors_singular_of_total_weight_le_one q
      h.first_ne h.second_ne (primitiveExcess 131071 q) hc)

end ProximityPrize.SubmissionLower.Koala6844Normalization
