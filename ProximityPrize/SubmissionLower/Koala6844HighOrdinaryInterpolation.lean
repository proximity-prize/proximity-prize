import ProximityPrize.SubmissionLower.Koala6831OrdinaryInterpolation
import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryJet

namespace ProximityPrize.SubmissionLower.Koala6844HighOrdinary

open MvPolynomial Koala6844HighOrdinaryQuotient
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K]

export Koala6831Ordinary (globalMultiplier exists_ordinary_interpolant)

private theorem ordinaryProfiles_admissible (idx : Fin 9) :
    2 ≤ (ordinaryProfiles idx).1 ∧ 1 ≤ (ordinaryProfiles idx).2.1 ∧
      idx.val + 2 ≤ (ordinaryProfiles idx).2.2 ∧
      131071 + 31614 < (ordinaryProfiles idx).1 * 180957 := by
  fin_cases idx <;> decide +kernel

theorem exists_ordinary_interpolant_6844 {I : Type*} [Fintype I]
    (x u₀ v₀ u₁ v₁ : I → K) (q : Poly K) (q_ne : q ≠ 0)
    (idx : Fin 9) (δ : ℕ) (large : 11500 ≤ δ) (small : δ ≤ 31614)
    (node_count : Fintype.card I ≤ 262144)
    (q_code : weightDegree (codeWeights 131071) q = 131071 + δ)
    (q_value : weightDegree valueWeights q = 1)
    (q_total : weightDegree totalWeights q = idx.val + 2)
    (q_order : ∀ i, (weightLift germWeights (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q)).natTrailingDegree = 1) :
    let (m, y, L) := ordinaryProfiles idx
    ∃ Q : Poly K, Q ∈ ordinaryBox K (m * 180957) 131071 y L ∧ ¬ q ∣ Q ∧
      ∀ i, ∃ B : Poly K, ∀ d ∈
        (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) Q -
          centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q * B).support,
        m ≤ d 0 + d 1 + d 2 := by
  have gate := ordinaryDimensionGate idx δ large
  have admissible := ordinaryProfiles_admissible idx
  cases profile : ordinaryProfiles idx with
  | mk m caps =>
      obtain ⟨y, L⟩ := caps
      simp only [profile] at gate admissible ⊢
      obtain ⟨m_pos, value_le, total_le, code_upper⟩ := admissible
      exact exists_ordinary_interpolant x u₀ v₀ u₁ v₁ q q_ne (m * 180957) 131071 y L m δ (idx.val + 2)
        (by omega) value_le total_le m_pos q_code q_value q_total q_order
        ((Nat.add_le_add_left (Nat.mul_le_mul_right _ node_count) _).trans_lt gate)

end

end ProximityPrize.SubmissionLower.Koala6844HighOrdinary
