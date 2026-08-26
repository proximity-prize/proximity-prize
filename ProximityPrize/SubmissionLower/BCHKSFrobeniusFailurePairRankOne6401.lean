import ProximityPrize.SubmissionLower.BCHKSFrobeniusDualGRSKernel6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusFailurePairRankOne6401
open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
noncomputable def failurePairCross
    {F : Type*} [Field F]
    (W₀ W₁ V₀ V₁ : Polynomial F) : Polynomial F :=
  W₀ * V₁ - V₀ * W₁
theorem failurePairCross_natDegree_le
    {F : Type*} [Field F]
    (W₀ W₁ V₀ V₁ : Polynomial F) (d : Nat)
    (hW₀ : W₀.natDegree ≤ d) (hW₁ : W₁.natDegree ≤ d)
    (hV₀ : V₀.natDegree ≤ d) (hV₁ : V₁.natDegree ≤ d) :
    (failurePairCross W₀ W₁ V₀ V₁).natDegree ≤ d + d := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hW₀ hV₁)
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hV₀ hW₁)
theorem failurePairCross_eval_eq_zero
    {F ι : Type*} [Field F]
    (sigma : F →+* F) (alpha : ι → F) (E : ι → F)
    (W₀ W₁ V₀ V₁ : Polynomial F)
    (hE : ∀ i, E i ≠ 0)
    (hW : TwoLaneFailureRelation sigma alpha E W₀ W₁)
    (hV : TwoLaneFailureRelation sigma alpha E V₀ V₁) :
    ∀ i, (failurePairCross W₀ W₁ V₀ V₁).eval (alpha i) = 0 := by
  intro i
  have hw := hW i
  have hv := hV i
  have hsigmaE : sigma (E i) ≠ 0 := by
    simpa using sigma.injective.ne (hE i)
  simp only [failurePairCross, Polynomial.eval_sub, Polynomial.eval_mul]
  apply sub_eq_zero.mpr
  have hmul :
      (W₀.eval (alpha i) * V₁.eval (alpha i)) * E i * sigma (E i) =
        (V₀.eval (alpha i) * W₁.eval (alpha i)) * E i * sigma (E i) := by
    calc
      (W₀.eval (alpha i) * V₁.eval (alpha i)) * E i * sigma (E i) =
          (W₀.eval (alpha i) * sigma (E i)) *
            (V₁.eval (alpha i) * E i) := by ring
      _ = (W₁.eval (alpha i) * E i) *
            (V₀.eval (alpha i) * sigma (E i)) := by rw [hw, hv]
      _ = (V₀.eval (alpha i) * W₁.eval (alpha i)) * E i * sigma (E i) := by
        ring
  exact mul_right_cancel₀ (hE i) (mul_right_cancel₀ hsigmaE hmul)
theorem failurePairCross_eq_zero_of_two_mul_degree_lt_card
    {F : Type*} [Field F] {t : Nat}
    (sigma : F →+* F) (alpha : Fin t ↪ F) (E : Fin t → F)
    (W₀ W₁ V₀ V₁ : Polynomial F) (d : Nat)
    (hE : ∀ i, E i ≠ 0)
    (hW₀ : W₀.natDegree ≤ d) (hW₁ : W₁.natDegree ≤ d)
    (hV₀ : V₀.natDegree ≤ d) (hV₁ : V₁.natDegree ≤ d)
    (hW : TwoLaneFailureRelation sigma alpha E W₀ W₁)
    (hV : TwoLaneFailureRelation sigma alpha E V₀ V₁)
    (hmass : d + d < t) :
    failurePairCross W₀ W₁ V₀ V₁ = 0 := by
  let D := failurePairCross W₀ W₁ V₀ V₁
  let roots : Finset F := Finset.univ.map alpha
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' D roots
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
    exact failurePairCross_eval_eq_zero sigma alpha E
      W₀ W₁ V₀ V₁ hE hW hV i
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact (failurePairCross_natDegree_le W₀ W₁ V₀ V₁ d
      hW₀ hW₁ hV₀ hV₁).trans_lt hmass
theorem failurePair_cross_window_exact6401 :
    (keySecondLaneRows6401 - 1) + (keySecondLaneRows6401 - 1) = 45014 ∧
      45014 < keyErrors6401 := by
  norm_num [keySecondLaneRows6401, keyFirstLaneRows6401,
    keyRedundancy6401, keyErrors6401,
    ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401.n6401,
    ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401.ownerDegreeCap6401,
    ProximityPrize.SubmissionLower.bchksErrors6401]
theorem benchmark_failurePairCross_eq_zero6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin keyErrors6401 ↪ F)
    (E : Fin keyErrors6401 → F)
    (W₀ W₁ V₀ V₁ : Polynomial F)
    (hE : ∀ i, E i ≠ 0)
    (hW₀ : W₀.natDegree ≤ keySecondLaneRows6401 - 1)
    (hW₁ : W₁.natDegree ≤ keySecondLaneRows6401 - 1)
    (hV₀ : V₀.natDegree ≤ keySecondLaneRows6401 - 1)
    (hV₁ : V₁.natDegree ≤ keySecondLaneRows6401 - 1)
    (hW : TwoLaneFailureRelation sigma alpha E W₀ W₁)
    (hV : TwoLaneFailureRelation sigma alpha E V₀ V₁) :
    failurePairCross W₀ W₁ V₀ V₁ = 0 := by
  apply failurePairCross_eq_zero_of_two_mul_degree_lt_card
    sigma alpha E W₀ W₁ V₀ V₁
      (keySecondLaneRows6401 - 1) hE hW₀ hW₁ hV₀ hV₁ hW hV
  exact failurePair_cross_window_exact6401.1.symm ▸
    failurePair_cross_window_exact6401.2
end BCHKSFrobeniusFailurePairRankOne6401
end ProximityPrize.SubmissionLower
