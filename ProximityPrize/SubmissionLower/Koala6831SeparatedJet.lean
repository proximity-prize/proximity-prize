import ProximityPrize.SubmissionLower.Koala6831OrdinaryJet

namespace ProximityPrize.SubmissionLower.Koala6831Separated

open MvPolynomial Koala6831Ordinary Koala6831Quotient
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

def secondWeights : Fin 5 → ℕ := ![0, 0, 1, 0, 0]
def leftWeights : Fin 5 → ℕ := ![0, 1, 0, 1, 0]
def rightWeights : Fin 5 → ℕ := ![0, 0, 1, 0, 1]

@[simp] theorem second_weight (d : Fin 5 →₀ ℕ) :
    Finsupp.weight secondWeights d = d 2 := by simp [weight_five, secondWeights]

@[simp] theorem left_weight (d : Fin 5 →₀ ℕ) :
    Finsupp.weight leftWeights d = d 1 + d 3 := by simp [weight_five, leftWeights]

@[simp] theorem right_weight (d : Fin 5 →₀ ℕ) :
    Finsupp.weight rightWeights d = d 2 + d 4 := by simp [weight_five, rightWeights]

theorem separatedBox_iff_weights {D w y s L₀ L₁ : ℕ} (positive : 0 < D) (P : Poly K) :
    P ∈ separatedBox K D w y s L₀ L₁ ↔
      weightDegree (codeWeights w) P < D ∧ weightDegree valueWeights P ≤ y ∧
        weightDegree secondWeights P ≤ s ∧ weightDegree leftWeights P ≤ L₀ ∧
        weightDegree rightWeights P ≤ L₁ := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro supp
    refine ⟨?_, Finset.sup_le ?_, Finset.sup_le ?_, Finset.sup_le ?_, Finset.sup_le ?_⟩
    · have hcode : weightDegree (codeWeights w) P ≤ D - 1 := by
        apply Finset.sup_le
        intro d hd
        have h : d 0 + w * (d 1 + d 2) < D := (supp hd).1
        rw [code_weight]
        omega
      omega
    · intro d hd
      exact (value_weight d).trans_le (supp hd).2.1
    · intro d hd
      exact (second_weight d).trans_le (supp hd).2.2.1
    · intro d hd
      exact (left_weight d).trans_le (supp hd).2.2.2.1
    · intro d hd
      exact (right_weight d).trans_le (supp hd).2.2.2.2
  · intro ⟨hD, hy, hs, hL₀, hL₁⟩ d hd
    change d 0 + w * (d 1 + d 2) < D ∧ d 1 + d 2 ≤ y ∧ d 2 ≤ s ∧
      d 1 + d 3 ≤ L₀ ∧ d 2 + d 4 ≤ L₁
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [code_weight] using (le_weightedTotalDegree (codeWeights w) hd).trans_lt hD
    · simpa only [value_weight] using (le_weightedTotalDegree valueWeights hd).trans hy
    · simpa only [second_weight] using (le_weightedTotalDegree secondWeights hd).trans hs
    · simpa only [left_weight] using (le_weightedTotalDegree leftWeights hd).trans hL₀
    · simpa only [right_weight] using (le_weightedTotalDegree rightWeights hd).trans hL₁

theorem center_weight_le (w : Fin 5 → ℕ) (left : w 3 ≤ w 1) (right : w 4 ≤ w 2)
    (x u₀ v₀ u₁ v₁ : K) (P : Poly K) :
    weightDegree w (centerAtNode x u₀ v₀ u₁ v₁ P) ≤ weightDegree w P := by
  let v : Fin 5 → Poly K :=
    ![X 0 + C x, X 1 + C u₀ + X 3 * C v₀,
      X 2 + C u₁ + X 4 * C v₁, X 3, X 4]
  change weightDegree w (aeval v P) ≤ weightDegree w P
  apply weight_eval_le w w
  have seed_bound (i : Fin 5) (a : K) : weightDegree w ((X i : Poly K) * C a) ≤ w i := by
    simpa only [weight_X, weight_C, add_zero] using weight_mul_le w (X i) (C a)
  have shift_bound (i : Fin 5) (a : K) : weightDegree w ((X i : Poly K) + C a) ≤ w i := by
    simpa only [weight_X, weight_C, max_zero] using weight_add_le w (X i) (C a)
  intro i
  fin_cases i
  · change weightDegree w (X 0 + C x) ≤ w 0
    exact shift_bound 0 x
  · change weightDegree w (X 1 + C u₀ + X 3 * C v₀) ≤ w 1
    exact (weight_add_le w _ _).trans (max_le (shift_bound 1 u₀) ((seed_bound 3 v₀).trans left))
  · change weightDegree w (X 2 + C u₁ + X 4 * C v₁) ≤ w 2
    exact (weight_add_le w _ _).trans (max_le (shift_bound 2 u₁) ((seed_bound 4 v₁).trans right))
  · change weightDegree w (X 3 : Poly K) ≤ w 3
    rw [weight_X]
  · change weightDegree w (X 4 : Poly K) ≤ w 4
    rw [weight_X]

abbrev LocalBox (K : Type*) [Field K] (m s L₀ L₁ : ℕ) :=
  separatedBox K m 1 (m - 1) s L₀ L₁

theorem truncate_mem_box (m s L₀ L₁ : ℕ) (P : Poly K)
    (hs : weightDegree secondWeights P ≤ s) (hL₀ : weightDegree leftWeights P ≤ L₀)
    (hL₁ : weightDegree rightWeights P ≤ L₁) :
    truncate m P ∈ LocalBox K m s L₀ L₁ := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro d hd
  obtain ⟨hdP, low⟩ := support_truncate m P hd
  have hds := (le_weightedTotalDegree secondWeights hdP).trans hs
  have hd₀ := (le_weightedTotalDegree leftWeights hdP).trans hL₀
  have hd₁ := (le_weightedTotalDegree rightWeights hdP).trans hL₁
  simp only [germ_weight] at low
  simp only [second_weight] at hds
  simp only [left_weight] at hd₀
  simp only [right_weight] at hd₁
  exact ⟨by omega, by omega, hds, hd₀, hd₁⟩

def truncateMultiplier (m s L₀ L₁ : ℕ) (m_pos : 2 ≤ m)
    (s_pos : 1 ≤ s) (L₀_pos : 1 ≤ L₀) (L₁_pos : 1 ≤ L₁) (row : Poly K)
    (row_s : weightDegree secondWeights row ≤ 1)
    (row_L₀ : weightDegree leftWeights row ≤ 1) (row_L₁ : weightDegree rightWeights row ≤ 1) :
    LocalBox K (m - 1) (s - 1) (L₀ - 1) (L₁ - 1) →ₗ[K] LocalBox K m s L₀ L₁ :=
  ((truncate m).comp ((leftMultiply row).comp
    (LocalBox K (m - 1) (s - 1) (L₀ - 1) (L₁ - 1)).subtype)).codRestrict _
    (fun B => by
      change truncate m (row * B.val) ∈ LocalBox K m s L₀ L₁
      have hB := (separatedBox_iff_weights (by omega) B.val).mp B.property
      exact truncate_mem_box m s L₀ L₁ _ ((weight_mul_le _ _ _).trans
        ((Nat.add_le_add row_s hB.2.2.1).trans (by omega)))
        ((weight_mul_le _ _ _).trans ((Nat.add_le_add row_L₀ hB.2.2.2.1).trans (by omega)))
        ((weight_mul_le _ _ _).trans ((Nat.add_le_add row_L₁ hB.2.2.2.2).trans (by omega))))

theorem truncateMultiplier_injective (m s L₀ L₁ : ℕ) (m_pos : 2 ≤ m)
    (s_pos : 1 ≤ s) (L₀_pos : 1 ≤ L₀) (L₁_pos : 1 ≤ L₁) (row : Poly K)
    (row_s : weightDegree secondWeights row ≤ 1)
    (row_L₀ : weightDegree leftWeights row ≤ 1) (row_L₁ : weightDegree rightWeights row ≤ 1)
    (order : (weightLift germWeights row).natTrailingDegree = 1) :
    Function.Injective (truncateMultiplier m s L₀ L₁ m_pos s_pos L₀_pos L₁_pos row row_s row_L₀ row_L₁) := by
  intro B R equal
  apply Subtype.ext
  have hrow : weightLift germWeights row ≠ 0 := by
    intro hz
    simp [hz] at order
  have same : truncate m (row * B.val) = truncate m (row * R.val) := congrArg Subtype.val equal
  have divides := power_dvd_lift_of_high m _ (high_of_truncate_eq m _ _ same)
  rw [map_sub, map_mul, map_mul] at divides
  have small (P : LocalBox K (m - 1) (s - 1) (L₀ - 1) (L₁ - 1)) :
      (weightLift germWeights P.val).degree < (↑(m - 1) : WithBot ℕ) := by
    have nat_lt : (weightLift germWeights P.val).natDegree < m - 1 := by
      rw [weightLift_natDegree]
      exact ((separatedBox_iff_weights (by omega) P.val).mp P.property).1
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast nat_lt)
  have eq_hom := local_multiplier_injective m hrow order (small B) (small R) divides
  apply sub_eq_zero.mp
  by_contra nonzero
  exact weightLift_ne_zero germWeights nonzero (by rw [map_sub, eq_hom, sub_self])

def truncateGerm (D w y s L₀ L₁ m : ℕ) (D_pos : 0 < D) (x u₀ v₀ u₁ v₁ : K) :
    separatedBox K D w y s L₀ L₁ →ₗ[K] LocalBox K m s L₀ L₁ :=
  ((truncate m).comp ((centerAtNode x u₀ v₀ u₁ v₁).toLinearMap.comp
    (separatedBox K D w y s L₀ L₁).subtype)).codRestrict _
    (fun P => by
      change truncate m (centerAtNode x u₀ v₀ u₁ v₁ P.val) ∈ LocalBox K m s L₀ L₁
      have hP := (separatedBox_iff_weights D_pos P.val).mp P.property
      exact truncate_mem_box m s L₀ L₁ _
        ((center_weight_le secondWeights (by decide) (by decide) x u₀ v₀ u₁ v₁ P.val).trans hP.2.2.1)
        ((center_weight_le leftWeights (by decide) (by decide) x u₀ v₀ u₁ v₁ P.val).trans hP.2.2.2.1)
        ((center_weight_le rightWeights (by decide) (by decide) x u₀ v₀ u₁ v₁ P.val).trans hP.2.2.2.2))

end

end ProximityPrize.SubmissionLower.Koala6831Separated
