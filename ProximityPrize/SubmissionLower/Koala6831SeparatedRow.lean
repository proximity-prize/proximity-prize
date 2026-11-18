import ProximityPrize.SubmissionLower.Koala6831PrimitiveLiftDegrees
import ProximityPrize.SubmissionLower.Koala6831SeparationNormalForm
import ProximityPrize.SubmissionLower.Koala6831SeparatedJet

namespace ProximityPrize.SubmissionLower.Koala6831Separated

open MvPolynomial Koala6831Ordinary Koala6831Comparison
open Koala6831Separation (regroup coeff_regroup_eq NormalForm)
open Koala6831SeparationFactors (affine)
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

private theorem regroup_coeff_coeff (P : SeedCoefficients K) (d : Fin 2 →₀ ℕ) (j : ℕ) :
    ((regroup P).coeff d).coeff j = (P.coeff j).coeff d := by
  let cap := max P.natDegree j
  have hj : j ≤ cap := le_max_right _ _
  rw [coeff_regroup_eq P d cap (le_max_left _ _), Koala6831CoefficientSystem.coefficientPolynomial,
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff, ite_eq_left hj]

theorem lifted_block_le (P : SeedCoefficients K) (a b : ℕ)
    (ha : (regroup P).degreeOf 0 ≤ a) (hb : (regroup P).degreeOf 1 ≤ b) :
    weightDegree leftWeights (retainCarrier (carrierOfSeedCoefficients P)) ≤ a ∧
      weightDegree rightWeights (retainCarrier (carrierOfSeedCoefficients P)) ≤ b := by
  have indices (e : Fin 5 →₀ ℕ) (he : e ∈ (retainCarrier (carrierOfSeedCoefficients P)).support) :
      e 1 = 0 ∧ e 2 = 0 ∧ e 3 ≤ a ∧ e 4 ≤ b := by
    obtain ⟨hy₀, hy₁, _, z, hz, hz₀, hz₁⟩ := liftedCoefficient_support_shape P e he
    have hreg : z ∈ (regroup P).support := by
      apply MvPolynomial.mem_support_iff.mpr
      intro hzero
      have heq := regroup_coeff_coeff P z (e 0)
      rw [hzero, Polynomial.coeff_zero] at heq
      exact (MvPolynomial.mem_support_iff.mp hz) heq.symm
    exact ⟨hy₀, hy₁,
      hz₀ ▸ (MvPolynomial.le_degreeOf_of_mem_support (0 : Fin 2) hreg).trans ha,
      hz₁ ▸ (MvPolynomial.le_degreeOf_of_mem_support (1 : Fin 2) hreg).trans hb⟩
  constructor
  · apply Finset.sup_le
    intro e he
    obtain ⟨h, _, hz, _⟩ := indices e he
    simpa [h] using hz
  · apply Finset.sup_le
    intro e he
    obtain ⟨_, h, _, hz⟩ := indices e he
    simpa [h] using hz

theorem lifted_second_zero (P : SeedCoefficients K) :
    weightDegree secondWeights (retainCarrier (carrierOfSeedCoefficients P)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro e he
  have hz := (liftedCoefficient_support_shape P e he).2.1
  simp [hz]

private theorem affine_degreeOf_le (i j : Fin 2) (a b : Polynomial K) :
    (affine j a b).degreeOf i ≤ if i = j then 1 else 0 := by
  unfold affine
  apply (MvPolynomial.degreeOf_add_le i _ _).trans
  apply max_le
  · exact (MvPolynomial.degreeOf_C a i).trans_le (Nat.zero_le _)
  · exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans_eq (MvPolynomial.degreeOf_X i j)

private theorem paired_affine_degreeOf_le (i : Fin 2) (a b c d : Polynomial K) :
    (affine 0 a b * affine 1 c d).degreeOf i ≤ 1 := by
  apply (MvPolynomial.degreeOf_mul_le i _ _).trans
  have h₀ := affine_degreeOf_le i 0 a b
  have h₁ := affine_degreeOf_le i 1 c d
  fin_cases i <;> simp at h₀ h₁ ⊢ <;> omega

theorem coefficient_block_caps {q : SymbolicRow (SeedRing K)} {w δ : ℕ} (N : NormalForm q w δ) :
    weightDegree leftWeights (retainCarrier (carrierOfSeedCoefficients q.beta)) ≤ 1 ∧
    weightDegree leftWeights (retainCarrier (carrierOfSeedCoefficients q.first)) = 0 ∧
    weightDegree leftWeights (retainCarrier (carrierOfSeedCoefficients q.second)) ≤ 1 ∧
    weightDegree rightWeights (retainCarrier (carrierOfSeedCoefficients q.beta)) ≤ 1 ∧
    weightDegree rightWeights (retainCarrier (carrierOfSeedCoefficients q.first)) ≤ 1 ∧
    weightDegree rightWeights (retainCarrier (carrierOfSeedCoefficients q.second)) = 0 := by
  have beta (i : Fin 2) : (regroup q.beta).degreeOf i ≤ 1 := by
    rw [N.beta_eq]
    exact (MvPolynomial.degreeOf_add_le i _ _).trans (max_le
      (paired_affine_degreeOf_le i _ _ _ _) (paired_affine_degreeOf_le i _ _ _ _))
  have first (i : Fin 2) : (regroup q.first).degreeOf i ≤ if i = 1 then 1 else 0 := by
    rw [N.first_eq]
    exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans (affine_degreeOf_le i 1 _ _)
  have second (i : Fin 2) : (regroup q.second).degreeOf i ≤ if i = 0 then 1 else 0 := by
    rw [N.second_eq, MvPolynomial.degreeOf_neg]
    exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans (affine_degreeOf_le i 0 _ _)
  obtain ⟨βL, βR⟩ := lifted_block_le q.beta 1 1 (beta 0) (beta 1)
  obtain ⟨aL, aR⟩ := lifted_block_le q.first 0 1 (by simpa using first 0) (by simpa using first 1)
  obtain ⟨bL, bR⟩ := lifted_block_le q.second 1 0 (by simpa using second 0) (by simpa using second 1)
  exact ⟨βL, Nat.eq_zero_of_le_zero aL, bL, βR, aR, Nat.eq_zero_of_le_zero bR⟩

theorem primitive_block_weights {q : SymbolicRow (SeedRing K)} {w δ : ℕ}
    (N : NormalForm q w δ) (hf : q.first ≠ 0) (hs : q.second ≠ 0) :
    weightDegree secondWeights (primitiveRowLift q) = 1 ∧
    weightDegree leftWeights (primitiveRowLift q) = 1 ∧
    weightDegree rightWeights (primitiveRowLift q) = 1 := by
  obtain ⟨hβL, haL, hbL, hβR, haR, hbR⟩ := coefficient_block_caps N
  have hfirst : retainCarrier (carrierOfSeedCoefficients q.first) ≠ 0 := fun hz =>
    carrierOfSeedCoefficients_ne_zero hf (retainCarrier_injective (by simpa using hz))
  have hsecond : retainCarrier (carrierOfSeedCoefficients q.second) ≠ 0 := fun hz =>
    carrierOfSeedCoefficients_ne_zero hs (retainCarrier_injective (by simpa using hz))
  have hmax (v : Fin 5 → ℕ) :
      weightDegree v (primitiveRowLift q) =
        max (max (weightDegree v (retainCarrier (carrierOfSeedCoefficients q.beta)))
          (weightDegree v (retainCarrier (carrierOfSeedCoefficients q.first)) + v 1))
          (weightDegree v (retainCarrier (carrierOfSeedCoefficients q.second)) + v 2) := by
    rw [primitiveRowLift_weight_max, weight_mul_eq v hfirst (MvPolynomial.X_ne_zero _),
      weight_mul_eq v hsecond (MvPolynomial.X_ne_zero _), weight_X, weight_X]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmax, lifted_second_zero, lifted_second_zero, lifted_second_zero]
    decide
  · rw [hmax, haL]
    change max (max (weightDegree leftWeights (retainCarrier (carrierOfSeedCoefficients q.beta))) (0 + 1))
      (weightDegree leftWeights (retainCarrier (carrierOfSeedCoefficients q.second)) + 0) = 1
    omega
  · rw [hmax, hbR]
    change max (max (weightDegree rightWeights (retainCarrier (carrierOfSeedCoefficients q.beta)))
      (weightDegree rightWeights (retainCarrier (carrierOfSeedCoefficients q.first)) + 0)) (0 + 1) = 1
    omega

end

end ProximityPrize.SubmissionLower.Koala6831Separated
