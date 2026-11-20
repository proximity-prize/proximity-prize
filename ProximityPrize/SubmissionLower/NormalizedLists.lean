/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.ScalarCappedProfile

namespace ProximityPrize.SubmissionLower.NormalizedLists

open ProximityPrize.Benchmark ReedSolomon ReedSolomon.HiddenDerivative
open PolynomialDifferential MvPolynomial ReedSolomon.FirstOrder.Squarefree
open scoped BigOperators
noncomputable section
set_option maxRecDepth 120000
set_option maxHeartbeats 7000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : CharP IRSProfile.Field 2130706433 :=
  charP_of_injective_algebraMap' KoalaBear.Field 2130706433

def ListBound (n D A limit : ℕ) : Prop :=
  ∀ (x : Fin n ↪ IRSProfile.Field) (u : Fin n → IRSProfile.Field)
    (words : Finset (Polynomial IRSProfile.Field)),
    (∀ P ∈ words, P.natDegree ≤ D) →
    (∀ P ∈ words, A ≤ (polynomialAgreementSet x u P).card) → words.card ≤ limit

theorem from_profile {n D A m M μ limit : ℕ}
    (degree : 0 < D) (lo : D+1 ≤ A) (hi : A ≤ n)
    (positive : 0 < m*A) (cap : M ≤ μ) (char : max D M < 2130706433)
    (gate : n * certifiedEnlargedRankBound 1 m M 0 < firstOrderDimensionCount D A m M μ)
    (budget : (firstOrderCurveFiberStageOne (D+1) μ M (regularTaylorExponent D) : ℝ) *
      ((n-D : ℕ) : ℝ) / ((A-D : ℕ) : ℝ) + (ordinaryDegreeEnvelope μ M : ℝ) < (limit+1 : ℕ)) :
    ListBound n D A limit := by
  intro x u words hdegree hagree
  classical
  obtain ⟨Q, nz, box, constraints⟩ := exists_nonzero_firstOrder_interpolant_of_dimensionCount
    (F := IRSProfile.Field) degree x u (by simpa using gate)
  have slope : jetDegree Q 1 ≤ M := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have bound : e (some (⟨1, by decide⟩ : Fin 2)) ≤ M := by
      simpa only [firstJetExponent_eq_coordinates Nat.one_pos, jetExponentCoordinatesEquiv_apply]
        using (mem_firstOrderSpace_iff.mp box e he).1
    exact bound
  have vanish (P : Polynomial IRSProfile.Field) (hp : P ∈ words) :
      differentialSpecialization Q P = 0 :=
    differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt x u
      (polynomialAgreementSet x u P) (differentialWeightedDegree_lt_of_mem_firstOrderSpace positive box)
      (fun i _ => constraints i) P (hdegree P hp) x.injective.injOn (hagree P hp)
      (fun i hi => (mem_polynomialAgreementSet x u P i).mp hi)
  have count := finite_squarefree_agreement_solutions_card_le
    (n := n) (D := D) (A := A) x u Q nz degree lo hi cap
    (jetTotalDegree_le_of_mem_firstOrderSpace box) slope
    (Or.inr (by rwa [ringChar.eq IRSProfile.Field 2130706433])) words vanish (by
      intro P hp
      refine ⟨?_, hagree P hp⟩
      by_cases hz : P = 0
      · simp [hz]
      · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mp (Nat.lt_succ_of_le (hdegree P hp)))
  have bound : (words.card : ℝ) < (limit+1 : ℕ) := count.trans_lt budget
  exact Nat.le_of_lt_succ (by exact_mod_cast bound)

/-- A normalized family may exceed the selected word degree by 120. -/
theorem at_131191 : ListBound 262144 131191 180951 52388760855477 := by
  apply from_profile (m := 10000) (M := 3099) (μ := 13792)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount, ScalarCappedProfile.dimension_rows (by decide)]
    decide +kernel
  · norm_num [firstOrderCurveFiberStageOne, cappedDegreeMixedVolume, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularTaylorExponent, ordinaryDegreeEnvelope]

#print axioms at_131191
end
end ProximityPrize.SubmissionLower.NormalizedLists
