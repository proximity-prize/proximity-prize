/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.NormalizedLists

namespace ProximityPrize.SubmissionLower.NormalizedLists
open ProximityPrize.Benchmark ReedSolomon ReedSolomon.HiddenDerivative
open PolynomialDifferential MvPolynomial ReedSolomon.FirstOrder.Squarefree
open scoped BigOperators
noncomputable section
set_option maxRecDepth 120000
set_option maxHeartbeats 7000000

def UpTo (maxNodes D A limit : ℕ) : Prop :=
  ∀ n, A ≤ n → n ≤ maxNodes → ListBound n D A limit

private theorem scheduled (maxNodes D μ : ℕ)
    (geometry : 0 < D ∧ D+1 ≤ 180951 ∧ 3099 ≤ μ ∧ max D 3099 < 2130706433 ∧ D*μ ≤ 10000*180951)
    (gate : maxNodes * firstOrderRankCount 10000 3099 <
      ∑ t ∈ Finset.range (μ+1),
        ((min t 3099+1)*(10000*180951-D*t)+(min t 3099+1)*min t 3099/2))
    (price : (firstOrderCurveFiberStageOne (D+1) μ 3099 (regularTaylorExponent D) : ℝ) *
        ((maxNodes-D : ℕ) : ℝ) / ((180951-D : ℕ) : ℝ) + (ordinaryDegreeEnvelope μ 3099 : ℝ)
        < (53000000000000+1 : ℕ)) : UpTo maxNodes D 180951 53000000000000 := by
  intro n hi hn
  obtain ⟨hd, lo, cap, char, cut⟩ := geometry
  apply from_profile hd lo hi (m := 10000) (by decide) cap char
  · rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount, ScalarCappedProfile.dimension_rows cut]
    exact (Nat.mul_le_mul_right _ hn).trans_lt gate
  · have diff : ((n-D : ℕ) : ℝ) ≤ ((maxNodes-D : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hn D
    apply lt_of_le_of_lt _ price
    gcongr

theorem dense : UpTo 262144 131191 180951 53000000000000 := by
  exact scheduled 262144 131191 13792 (by decide) (by decide +kernel) (by
    norm_num [firstOrderCurveFiberStageOne, cappedDegreeMixedVolume, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularTaylorExponent, ordinaryDegreeEnvelope])

theorem intermediate : UpTo 256357 133571 180951 53000000000000 := by
  exact scheduled 256357 133571 13547 (by decide) (by decide +kernel) (by
    norm_num [firstOrderCurveFiberStageOne, cappedDegreeMixedVolume, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularTaylorExponent, ordinaryDegreeEnvelope])

theorem sparse : UpTo 246652 137760 180951 53000000000000 := by
  exact scheduled 246652 137760 13135 (by decide) (by decide +kernel) (by
    norm_num [firstOrderCurveFiberStageOne, cappedDegreeMixedVolume, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularTaylorExponent, ordinaryDegreeEnvelope])

#print axioms sparse
end
end ProximityPrize.SubmissionLower.NormalizedLists
