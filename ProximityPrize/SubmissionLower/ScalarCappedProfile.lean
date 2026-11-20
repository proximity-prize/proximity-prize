/- Explicit first-order squarefree list bounds using ArkLib's interpolation and
Taylor-degree theorems. Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.ScalarListTransport
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Interpolant
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.TailBound

namespace ProximityPrize.SubmissionLower.ScalarCappedProfile
open ProximityPrize.Benchmark ReedSolomon ReedSolomon.HiddenDerivative
open PolynomialDifferential MvPolynomial ReedSolomon.FirstOrder.Squarefree
open scoped BigOperators
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

/-- Sum over the derivative exponent explicitly when every total-degree row is active. -/
theorem dimension_rows {D A m M μ : ℕ} (cut : D * μ ≤ m * A) :
    firstOrderDimensionCount D A m M μ =
      ∑ t ∈ Finset.range (μ + 1),
        ((min t M + 1) * (m * A - D * t) + (min t M + 1) * min t M / 2) := by
  unfold firstOrderDimensionCount
  refine Finset.sum_congr rfl fun t ht => ?_
  have le : D * t ≤ m * A := (Nat.mul_le_mul_left D (Finset.mem_range_succ_iff.mp ht)).trans cut
  have row (b : ℕ) : m * A + b - D * t = (m * A - D * t) + b := by omega
  simp_rw [row]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Finset.sum_range_id]
  simp

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : CharP IRSProfile.Field 2130706433 := charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- Turn a verified interpolation-dimension surplus and a squarefree list budget
into a bound on scalar codewords for the fixed KoalaBear profile. -/
theorem words_of_profile {A m M μ limit : ℕ} (lo : 131072 ≤ A) (hi : A ≤ 262144)
    (positive : 0 < m * A) (cap : M ≤ μ) (char : max 131071 M < 2130706433)
    (gate : 262144 * certifiedEnlargedRankBound 1 m M 0 <
      firstOrderDimensionCount 131071 A m M μ)
    (budget : (firstOrderCurveFiberStageOne 131072 μ M (regularTaylorExponent 131071) : ℝ) *
      131073 / ((A - 131071 : ℕ) : ℝ) + (ordinaryDegreeEnvelope μ M : ℝ) < (limit + 1 : ℕ)) :
    IntermediateScalar.Words A limit := by
  apply IntermediateScalar.of_scalar lo
  intro x u
  classical
  let S := closePolynomialSet x u 131072 A
  have fin : S.Finite := (closePolynomialSet_finite_and_ncard_mul_choose_le x u lo).1
  change S.ncard ≤ _
  rw [Set.ncard_eq_toFinset_card S fin]
  obtain ⟨Q, nz, box, constraints⟩ := exists_nonzero_firstOrder_interpolant_of_dimensionCount
    (F := IRSProfile.Field) (by decide : 0 < 131071) x u (by simpa using gate)
  have slope : jetDegree Q 1 ≤ M := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have h : e (some (⟨1, by decide⟩ : Fin 2)) ≤ M := by
      simpa only [firstJetExponent_eq_coordinates Nat.one_pos, jetExponentCoordinatesEquiv_apply]
        using (mem_firstOrderSpace_iff.mp box e he).1
    exact h
  have accept (P : Polynomial IRSProfile.Field) (hP : P ∈ fin.toFinset) :=
    fin.mem_toFinset.mp hP
  have vanish (P : Polynomial IRSProfile.Field) (hP : P ∈ fin.toFinset) :
      differentialSpecialization Q P = 0 := by
    have mem := accept P hP
    have degree : P.natDegree ≤ 131071 := by
      by_cases hz : P = 0
      · simp [hz]
      · have hd : P.natDegree < 131072 := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr mem.1
        omega
    exact differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
      x u (polynomialAgreementSet x u P)
      (differentialWeightedDegree_lt_of_mem_firstOrderSpace positive box)
      (fun i _ => constraints i) P degree x.injective.injOn mem.2
      (fun i hi => (mem_polynomialAgreementSet x u P i).mp hi)
  have count := FirstOrder.Squarefree.finite_squarefree_agreement_solutions_card_le
    (n := 262144) (D := 131071) (A := A) x u Q nz (by decide) (by simpa using lo) hi cap
    (jetTotalDegree_le_of_mem_firstOrderSpace box) slope
    (Or.inr (by rwa [ringChar.eq IRSProfile.Field 2130706433]))
    fin.toFinset vanish (fun P hP => accept P hP)
  have bound : (fin.toFinset.card : ℝ) < (limit + 1 : ℕ) := count.trans_lt budget
  exact Nat.le_of_lt_succ (by exact_mod_cast bound)


/-- Bound on the scalar list at 180961 agreements, with surplus 1876992. -/
theorem words_81183 : IntermediateScalar.Words 180961 107146011704 := by
  apply words_of_profile (m := 455) (M := 140) (μ := 627)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount, dimension_rows (by decide)]
    decide +kernel
  · norm_num [firstOrderCurveFiberStageOne, cappedDegreeMixedVolume, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularTaylorExponent, ordinaryDegreeEnvelope]

/-- Bound on the scalar list at 180958 agreements, with surplus 3760575. -/
theorem words_81186 : IntermediateScalar.Words 180958 113387658701 := by
  apply words_of_profile (m := 468) (M := 144) (μ := 645)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount, dimension_rows (by decide)]
    decide +kernel
  · norm_num [firstOrderCurveFiberStageOne, cappedDegreeMixedVolume, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularTaylorExponent, ordinaryDegreeEnvelope]

/-- Bound on the scalar list at 180951 agreements, with surplus 5007895. -/
theorem words_81193 : IntermediateScalar.Words 180951 129977088619 := by
  apply words_of_profile (m := 501) (M := 154) (μ := 691)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount, dimension_rows (by decide)]
    decide +kernel
  · norm_num [firstOrderCurveFiberStageOne, cappedDegreeMixedVolume, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularTaylorExponent, ordinaryDegreeEnvelope]

#print axioms words_81183
#print axioms words_81193
end
end ProximityPrize.SubmissionLower.ScalarCappedProfile
