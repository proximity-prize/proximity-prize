import ProximityPrize.SubmissionLower.Koala6831OrdinaryJet

namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open MvPolynomial Koala6831Quotient
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

def globalMultiplier (q : Poly K) (D w y L δ c : ℕ)
    (code_le : w + δ < D) (value_le : 1 ≤ y) (total_le : c ≤ L)
    (q_code : weightDegree (codeWeights w) q = w + δ)
    (q_value : weightDegree valueWeights q = 1) (q_total : weightDegree totalWeights q = c) :
    ordinaryBox K (D - w - δ) w (y - 1) (L - c) →ₗ[K] ordinaryBox K D w y L :=
  ((leftMultiply q).comp (ordinaryBox K (D - w - δ) w (y - 1) (L - c)).subtype).codRestrict _
    (fun B => by
      change q * B.val ∈ ordinaryBox K D w y L
      apply (ordinaryBox_iff_weights (by omega) _).mpr
      have small := (ordinaryBox_iff_weights (by omega) B.val).mp B.property
      have hcode := weight_mul_le (codeWeights w) q B.val
      have hvalue := weight_mul_le valueWeights q B.val
      have htotal := weight_mul_le totalWeights q B.val
      rw [q_code] at hcode
      rw [q_value] at hvalue
      rw [q_total] at htotal
      exact ⟨by omega, by omega, by omega⟩)

theorem exists_ordinary_interpolant {I : Type*} [Fintype I]
    (x u₀ v₀ u₁ v₁ : I → K) (q : Poly K) (q_ne : q ≠ 0)
    (D w y L m δ c : ℕ) (code_le : w + δ < D) (value_le : 1 ≤ y)
    (total_le : c ≤ L) (m_pos : 2 ≤ m)
    (q_code : weightDegree (codeWeights w) q = w + δ)
    (q_value : weightDegree valueWeights q = 1) (q_total : weightDegree totalWeights q = c)
    (q_order : ∀ i, (weightLift germWeights (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q)).natTrailingDegree = 1)
    (gate : ordinaryColumns (D - w - δ) w (y - 1) (L - c) +
      Fintype.card I * (ordinaryColumns m 1 (m - 1) L - ordinaryColumns (m - 1) 1 (m - 2) (L - c)) <
      ordinaryColumns D w y L) :
    ∃ Q : Poly K, Q ∈ ordinaryBox K D w y L ∧ ¬ q ∣ Q ∧
      ∀ i, ∃ B : Poly K, ∀ d ∈
        (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) Q -
          centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q * B).support,
        m ≤ d 0 + d 1 + d 2 := by
  classical
  let mult := globalMultiplier q D w y L δ c code_le value_le total_le q_code q_value q_total
  let germ i := truncateGerm D w y L m (by omega) (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i)
  let row i := centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q
  have row_total (i : I) : weightDegree totalWeights (row i) ≤ c :=
    (center_total_le _ _ _ _ _ _).trans q_total.le
  let mul i := truncateMultiplier m L c m_pos total_le (row i) (row_total i)
  have injective_local (i : I) : Function.Injective (mul i) :=
    truncateMultiplier_injective m L c m_pos total_le (row i) (row_total i) (q_order i)
  have injective_global : Function.Injective mult := by
    intro B R equal
    apply Subtype.ext
    exact mul_left_cancel₀ q_ne (congrArg Subtype.val equal)
  have local_cutoff : m - 1 - 1 = m - 2 := by omega
  have gate' : Module.finrank K mult.range +
      (∑ _ : I, (Module.finrank K (LocalBox K m L) - Module.finrank K (LocalBox K (m - 1) (L - c)))) <
      Module.finrank K (ordinaryBox K D w y L) := by
    rw [LinearMap.finrank_range_of_inj injective_global]
    simp only [LocalBox, ordinaryBox_finrank, local_cutoff, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact gate
  obtain ⟨Q, proper, contacts⟩ := exists_relative_interpolant mult.range germ mul injective_local gate'
  refine ⟨Q.val, Q.property, ?_, ?_⟩
  · intro divides
    apply proper
    obtain ⟨B, hB⟩ := divides
    have small : B ∈ ordinaryBox K (D - w - δ) w (y - 1) (L - c) := by
      by_cases B_zero : B = 0
      · rw [B_zero]
        exact Submodule.zero_mem _
      have hQ := (ordinaryBox_iff_weights (by omega) Q.val).mp Q.property
      rw [hB, weight_mul_eq _ q_ne B_zero, weight_mul_eq _ q_ne B_zero,
        weight_mul_eq _ q_ne B_zero, q_code, q_value, q_total] at hQ
      exact (ordinaryBox_iff_weights (by omega) B).mpr ⟨by omega, by omega, by omega⟩
    exact ⟨⟨B, small⟩, Subtype.ext hB.symm⟩
  · intro i
    obtain ⟨B, hB⟩ := contacts i
    have equal : truncate m (row i * B.val) =
        truncate m (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) Q.val) := congrArg Subtype.val hB
    exact ⟨B.val, by
      simpa only [row, germ_weight] using high_of_truncate_eq m _ _ equal.symm⟩

private theorem ordinaryProfiles_admissible (idx : Fin 9) :
    2 ≤ (ordinaryProfiles idx).1 ∧ 1 ≤ (ordinaryProfiles idx).2.1 ∧
      idx.val + 2 ≤ (ordinaryProfiles idx).2.2 ∧
      131071 + 31357 < (ordinaryProfiles idx).1 * 181078 := by
  fin_cases idx <;> decide +kernel

theorem exists_ordinary_interpolant_6831 {I : Type*} [Fintype I]
    (x u₀ v₀ u₁ v₁ : I → K) (q : Poly K) (q_ne : q ≠ 0)
    (idx : Fin 9) (δ : ℕ) (large : 11000 ≤ δ) (small : δ ≤ 31357)
    (node_count : Fintype.card I ≤ 262144)
    (q_code : weightDegree (codeWeights 131071) q = 131071 + δ)
    (q_value : weightDegree valueWeights q = 1)
    (q_total : weightDegree totalWeights q = idx.val + 2)
    (q_order : ∀ i, (weightLift germWeights (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q)).natTrailingDegree = 1) :
    let (m, y, L) := ordinaryProfiles idx
    ∃ Q : Poly K, Q ∈ ordinaryBox K (m * 181078) 131071 y L ∧ ¬ q ∣ Q ∧
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
      exact exists_ordinary_interpolant x u₀ v₀ u₁ v₁ q q_ne (m * 181078) 131071 y L m δ (idx.val + 2)
        (by omega) value_le total_le m_pos q_code q_value q_total q_order
        ((Nat.add_le_add_left (Nat.mul_le_mul_right _ node_count) _).trans_lt gate)

end

end ProximityPrize.SubmissionLower.Koala6831Ordinary

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
