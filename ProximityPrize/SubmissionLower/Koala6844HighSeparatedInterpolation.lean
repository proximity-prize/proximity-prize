import ProximityPrize.SubmissionLower.Koala6844HighSeparatedJet


namespace ProximityPrize.SubmissionLower.Koala6844HighSeparated

open MvPolynomial Koala6844HighOrdinary Koala6844HighOrdinaryQuotient
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

private def globalMultiplier (q : Poly K) (D w y s L₀ L₁ δ : ℕ) (code_le : w + δ < D)
    (y_pos : 1 ≤ y) (s_pos : 1 ≤ s) (L₀_pos : 1 ≤ L₀) (L₁_pos : 1 ≤ L₁)
    (q_code : weightDegree (codeWeights w) q = w + δ)
    (q_value : weightDegree valueWeights q = 1) (q_second : weightDegree secondWeights q = 1)
    (q_left : weightDegree leftWeights q = 1) (q_right : weightDegree rightWeights q = 1) :
    separatedBox K (D - w - δ) w (y - 1) (s - 1) (L₀ - 1) (L₁ - 1) →ₗ[K]
      separatedBox K D w y s L₀ L₁ :=
  ((leftMultiply q).comp (separatedBox K (D - w - δ) w (y - 1) (s - 1)
    (L₀ - 1) (L₁ - 1)).subtype).codRestrict _ (fun B => by
      change q * B.val ∈ separatedBox K D w y s L₀ L₁
      apply (separatedBox_iff_weights (by omega) _).mpr
      have ⟨hcode, hy, hs, hleft, hright⟩ :=
        (separatedBox_iff_weights (by omega) B.val).mp B.property
      refine ⟨(weight_mul_le (codeWeights w) q B.val).trans_lt ?_,
        (weight_mul_le valueWeights q B.val).trans ?_, (weight_mul_le secondWeights q B.val).trans ?_,
        (weight_mul_le leftWeights q B.val).trans ?_, (weight_mul_le rightWeights q B.val).trans ?_⟩
      · rw [q_code]; omega
      · rw [q_value]; omega
      · rw [q_second]; omega
      · rw [q_left]; omega
      · rw [q_right]; omega)

theorem exists_separated_interpolant {I : Type*} [Fintype I]
    (x u₀ v₀ u₁ v₁ : I → K) (q : Poly K) (q_ne : q ≠ 0)
    (D w y s L₀ L₁ m δ : ℕ) (code_le : w + δ < D) (y_pos : 1 ≤ y)
    (s_pos : 1 ≤ s) (L₀_pos : 1 ≤ L₀) (L₁_pos : 1 ≤ L₁) (m_pos : 2 ≤ m)
    (q_code : weightDegree (codeWeights w) q = w + δ)
    (q_value : weightDegree valueWeights q = 1) (q_second : weightDegree secondWeights q = 1)
    (q_left : weightDegree leftWeights q = 1) (q_right : weightDegree rightWeights q = 1)
    (q_order : ∀ i, (weightLift germWeights (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q)).natTrailingDegree = 1)
    (gate : separatedColumns (D - w - δ) w (y - 1) (s - 1) (L₀ - 1) (L₁ - 1) +
      Fintype.card I * (separatedColumns m 1 (m - 1) s L₀ L₁ -
        separatedColumns (m - 1) 1 (m - 2) (s - 1) (L₀ - 1) (L₁ - 1)) <
      separatedColumns D w y s L₀ L₁) :
    ∃ Q : Poly K, Q ∈ separatedBox K D w y s L₀ L₁ ∧ ¬ q ∣ Q ∧
      ∀ i, ∃ B : Poly K, ∀ d ∈
        (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) Q -
          centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q * B).support,
        m ≤ d 0 + d 1 + d 2 := by
  classical
  let mult := globalMultiplier q D w y s L₀ L₁ δ code_le y_pos s_pos L₀_pos L₁_pos
    q_code q_value q_second q_left q_right
  let germ i := Koala6844HighSeparated.truncateGerm D w y s L₀ L₁ m (by omega)
    (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i)
  let row i := centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q
  have row_s (i : I) : weightDegree secondWeights (row i) ≤ 1 :=
    (center_weight_le secondWeights (by decide) (by decide) (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q).trans q_second.le
  have row_left (i : I) : weightDegree leftWeights (row i) ≤ 1 :=
    (center_weight_le leftWeights (by decide) (by decide) (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q).trans q_left.le
  have row_right (i : I) : weightDegree rightWeights (row i) ≤ 1 :=
    (center_weight_le rightWeights (by decide) (by decide) (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q).trans q_right.le
  let mul i := Koala6844HighSeparated.truncateMultiplier m s L₀ L₁ m_pos s_pos
    L₀_pos L₁_pos (row i) (row_s i) (row_left i) (row_right i)
  have injective_local (i : I) : Function.Injective (mul i) :=
    Koala6844HighSeparated.truncateMultiplier_injective m s L₀ L₁ m_pos s_pos L₀_pos L₁_pos
      (row i) (row_s i) (row_left i) (row_right i) (q_order i)
  have injective_global : Function.Injective mult := by
    intro B R equal
    apply Subtype.ext
    exact mul_left_cancel₀ q_ne (congrArg Subtype.val equal)
  have local_cutoff : m - 1 - 1 = m - 2 := by omega
  have gate' : Module.finrank K mult.range +
      (∑ _ : I, (Module.finrank K (Koala6844HighSeparated.LocalBox K m s L₀ L₁) -
        Module.finrank K (Koala6844HighSeparated.LocalBox K (m - 1) (s - 1) (L₀ - 1) (L₁ - 1)))) <
      Module.finrank K (separatedBox K D w y s L₀ L₁) := by
    rw [LinearMap.finrank_range_of_inj injective_global]
    simp only [Koala6844HighSeparated.LocalBox, separatedBox_finrank, local_cutoff, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    exact gate
  obtain ⟨Q, proper, contacts⟩ := exists_relative_interpolant mult.range germ mul injective_local gate'
  refine ⟨Q.val, Q.property, ?_, ?_⟩
  · rintro ⟨B, hB⟩
    apply proper
    have small : B ∈ separatedBox K (D - w - δ) w (y - 1) (s - 1) (L₀ - 1) (L₁ - 1) := by
      by_cases hB₀ : B = 0
      · rw [hB₀]
        exact Submodule.zero_mem _
      have hQ := (separatedBox_iff_weights (by omega) Q.val).mp Q.property
      rw [hB, weight_mul_eq _ q_ne hB₀, weight_mul_eq _ q_ne hB₀, weight_mul_eq _ q_ne hB₀,
        weight_mul_eq _ q_ne hB₀, weight_mul_eq _ q_ne hB₀, q_code, q_value, q_second, q_left, q_right] at hQ
      exact (separatedBox_iff_weights (by omega) B).mpr ⟨by omega, by omega, by omega, by omega, by omega⟩
    exact ⟨⟨B, small⟩, Subtype.ext hB.symm⟩
  · intro i
    obtain ⟨B, hB⟩ := contacts i
    have same : truncate m (row i * B.val) =
        truncate m (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) Q.val) := congrArg Subtype.val hB
    exact ⟨B.val, by simpa only [row, germ_weight] using high_of_truncate_eq m _ _ same.symm⟩

theorem exists_long_interpolant {I : Type*} [Fintype I] (x u₀ v₀ u₁ v₁ : I → K)
    (q : Poly K) (q_ne : q ≠ 0) (δ : ℕ) (large : 9800 ≤ δ) (small : δ ≤ 31612)
    (node_count : Fintype.card I ≤ 262144)
    (q_code : weightDegree (codeWeights 131071) q = 131071 + δ)
    (q_value : weightDegree valueWeights q = 1) (q_second : weightDegree secondWeights q = 1)
    (q_left : weightDegree leftWeights q = 1) (q_right : weightDegree rightWeights q = 1)
    (q_order : ∀ i, (weightLift germWeights (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q)).natTrailingDegree = 1) :
    ∃ Q : Poly K, Q ∈ separatedBox K (16 * 180958) 131071 22 22 178 162 ∧ ¬ q ∣ Q ∧
      ∀ i, ∃ B : Poly K, ∀ d ∈
        (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) Q -
          centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q * B).support,
        16 ≤ d 0 + d 1 + d 2 := by
  exact exists_separated_interpolant x u₀ v₀ u₁ v₁ q q_ne (16 * 180958) 131071 22 22 178 162 16 δ
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    q_code q_value q_second q_left q_right q_order
    ((Nat.add_le_add_left (Nat.mul_le_mul_right _ node_count) _).trans_lt
      (longSeparatedDimensionGate δ large))

end

end ProximityPrize.SubmissionLower.Koala6844HighSeparated
