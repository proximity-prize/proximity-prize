import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusThreeShiftPrimitive6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusExtremeKernelCounter6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
def counterDenominatorDegree6401 : ℕ := 22507
def counterLowTermDegree6401 : ℕ := 153578
def counterMultiplierRoom6401 : ℕ := 31775
def counterLocatorDegree6401 : ℕ := 185354
theorem counter_locator_gap_exact6401 :
    counterDenominatorDegree6401 + ownerDegreeCap6401 =
        counterLowTermDegree6401 ∧
      counterLowTermDegree6401 + counterMultiplierRoom6401 =
        counterLocatorDegree6401 - 1 ∧
      counterLocatorDegree6401 = a6401 := by
  norm_num [counterDenominatorDegree6401, ownerDegreeCap6401,
    counterLowTermDegree6401, counterMultiplierRoom6401,
    counterLocatorDegree6401, a6401]
def extremeSlots6401 : Fin 3 → Fin 3 → ℕ := ![
  ![153579, 54283, 54283],
  ![185354, 22508, 54283],
  ![185354, 54283, 22508]]
def extremeDepth6401 (s : Fin 3) : ℕ :=
  extremeSlots6401 s 1 + q6401 * extremeSlots6401 s 2 + 1
def extremeVariables6401 (s : Fin 3) : ℕ :=
  extremeSlots6401 s 0 * extremeDepth6401 s +
    extremeSlots6401 s 1 * (extremeDepth6401 s - 1) +
    extremeSlots6401 s 2 * (extremeDepth6401 s - q6401)
def extremeConstraints6401 (s : Fin 3) : ℕ :=
  n6401 * extremeDepth6401 s
def extremePairDenominatorCap6401 (s t : Fin 3) : ℕ :=
  extremeDepth6401 s + extremeDepth6401 t - q6401 - 3
def extremePairMismatchCap6401 (s t : Fin 3) : ℕ :=
  extremePairDenominatorCap6401 s t + 1
theorem extreme_rectangles_exact6401 :
    extremeDepth6401 0 = 115661137356823 ∧
      extremeDepth6401 1 = 115661137325048 ∧
      extremeDepth6401 2 = 47957940448248 ∧
      (∀ s : Fin 3,
        extremeVariables6401 s = extremeConstraints6401 s + 1) ∧
      extremePairMismatchCap6401 0 1 = 231320143975436 ∧
      extremePairMismatchCap6401 0 2 = 163616947098636 ∧
      extremePairMismatchCap6401 1 2 = 163616947066861 := by
  native_decide
theorem extreme_cleared_root_degrees_exact6401 :
    (∀ s : Fin 3,
      extremeSlots6401 s 0 - 1 + 2 * counterDenominatorDegree6401 <
        n6401) ∧
    (∀ s : Fin 3,
      extremeSlots6401 s 1 - 1 + counterDenominatorDegree6401 +
          counterLocatorDegree6401 < n6401) ∧
    (∀ s : Fin 3,
      extremeSlots6401 s 2 - 1 + counterDenominatorDegree6401 +
          counterLocatorDegree6401 < n6401) := by
  native_decide
theorem locator_multiplier_sum_eq_zero
    {F : Type*} [Field F]
    (A0 h j G L1 L2 : Polynomial F)
    (hA0 : A0.natDegree ≤ 185353)
    (hh : h.natDegree ≤ counterMultiplierRoom6401)
    (hj : j.natDegree ≤ counterMultiplierRoom6401)
    (hGdegree : G.natDegree = counterLocatorDegree6401)
    (hL1 : L1.natDegree ≤ counterLowTermDegree6401)
    (hL2 : L2.natDegree ≤ counterLowTermDegree6401)
    (hidentity :
      A0 = -(h + j) * G - h * L1 - j * L2) :
    h + j = 0 := by
  by_contra hsum
  have hGne : G ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hGdegree
    norm_num [counterLocatorDegree6401] at hGdegree
  have hleftDegree : ((h + j) * G).natDegree ≥ 185354 := by
    rw [Polynomial.natDegree_mul hsum hGne, hGdegree]
    norm_num [counterLocatorDegree6401]
  have hhL1 : (h * L1).natDegree ≤ 185353 :=
    Polynomial.natDegree_mul_le.trans <| by
      norm_num [counterMultiplierRoom6401,
        counterLowTermDegree6401] at hh hL1 ⊢
      omega
  have hjL2 : (j * L2).natDegree ≤ 185353 :=
    Polynomial.natDegree_mul_le.trans <| by
      norm_num [counterMultiplierRoom6401,
        counterLowTermDegree6401] at hj hL2 ⊢
      omega
  have hrightDegree :
      (-(A0 + h * L1 + j * L2)).natDegree ≤ 185353 := by
    rw [Polynomial.natDegree_neg]
    exact (Polynomial.natDegree_add_le _ _).trans <|
      max_le
        ((Polynomial.natDegree_add_le _ _).trans <| max_le hA0 hhL1)
        hjL2
  have heq : (h + j) * G = -(A0 + h * L1 + j * L2) := by
    rw [hidentity]
    ring
  rw [heq] at hleftDegree
  omega
theorem multiplier_natDegree_eq_zero_of_saturated_component
    {F : Type*} [Field F]
    (h B A : Polynomial F) (cap : ℕ)
    (hh : h ≠ 0) (hB : B ≠ 0)
    (hBdegree : B.natDegree = cap)
    (hfactor : A = h * B)
    (hAdegree : A.natDegree ≤ cap) :
    h.natDegree = 0 := by
  rw [hfactor, Polynomial.natDegree_mul hh hB, hBdegree] at hAdegree
  omega
theorem not_dvd_mul_add_one_of_not_isUnit
    {F : Type*} [Field F] (lambda Q : Polynomial F)
    (hlambda : ¬ IsUnit lambda) :
    ¬ lambda ∣ lambda * Q + 1 := by
  intro hdvd
  have hone : lambda ∣ (1 : Polynomial F) := by
    have hmul : lambda ∣ lambda * Q := dvd_mul_right lambda Q
    simpa using dvd_sub hdvd hmul
  exact hlambda (isUnit_iff_dvd_one.mpr hone)
theorem counterLambda_natDegree_and_not_isUnit
    {F : Type*} [Field F] (c : F) :
    (Polynomial.X ^ counterDenominatorDegree6401 - Polynomial.C c).natDegree =
        counterDenominatorDegree6401 ∧
      ¬ IsUnit
        (Polynomial.X ^ counterDenominatorDegree6401 - Polynomial.C c) := by
  have hdegree :
      (Polynomial.X ^ counterDenominatorDegree6401 - Polynomial.C c).natDegree =
        counterDenominatorDegree6401 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · simp [counterDenominatorDegree6401]
    · simp [counterDenominatorDegree6401]
  refine ⟨hdegree, ?_⟩
  intro hunit
  have hdegreeZero := Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [hdegree] at hdegreeZero
  norm_num [counterDenominatorDegree6401] at hdegreeZero
theorem no_lowDegree_projection_of_rationalSlope6401
    {F ι : Type*} [Field F] [Fintype ι]
    [DecidableEq F] [DecidableEq ι]
    (alpha : ι ↪ F) (A : Finset ι)
    (lambda Q : Polynomial F)
    (hlambdaDegree : lambda.natDegree ≤ counterDenominatorDegree6401)
    (hQdegree : Q.natDegree ≤ ownerDegreeCap6401)
    (hlambdaNonunit : ¬ IsUnit lambda)
    (hlambdaAt : ∀ i ∈ A, lambda.eval (alpha i) ≠ 0)
    (hcard : a6401 ≤ A.card) :
    ¬ ∃ T : Polynomial F,
      T.natDegree ≤ ownerDegreeCap6401 ∧
      ∀ i ∈ A,
        T.eval (alpha i) = Q.eval (alpha i) + (lambda.eval (alpha i))⁻¹ := by
  rintro ⟨T, hTdegree, hagree⟩
  let D : Polynomial F := lambda * (T - Q) - 1
  have hTQdegree : (T - Q).natDegree ≤ ownerDegreeCap6401 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hTdegree hQdegree)
  have hDdegree : D.natDegree ≤ counterLowTermDegree6401 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans <| by
        norm_num [counterDenominatorDegree6401,
          ownerDegreeCap6401] at hlambdaDegree hTQdegree
        norm_num [counterLowTermDegree6401]
        omega
    · norm_num [counterLowTermDegree6401]
  have hDzero : D = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      D (A.map alpha)
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      have hne := hlambdaAt i hi
      have hagreei := hagree i hi
      simp only [D, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_one]
      rw [hagreei]
      field_simp [hne]
      ring
    · rw [Finset.card_map]
      exact hDdegree.trans_lt <|
        lt_of_lt_of_le
          (by norm_num [counterLowTermDegree6401, a6401]) hcard
  have hone : lambda * (T - Q) = 1 := sub_eq_zero.mp hDzero
  apply hlambdaNonunit
  apply isUnit_iff_dvd_one.mpr
  exact ⟨T - Q, hone.symm⟩
theorem zeroOwner_agrees_with_locatorQuotient6401
    {F ι : Type*} [Field F]
    (alpha : ι → F) (A : Finset ι)
    (G lambda : Polynomial F)
    (hG : ∀ i ∈ A, G.eval (alpha i) = 0) :
    ∀ i ∈ A,
      Polynomial.eval (alpha i) (0 : Polynomial F) =
        G.eval (alpha i) / lambda.eval (alpha i) + (0 : F) := by
  intro i hi
  simp [hG i hi]
end BCHKSTwoFrobeniusExtremeKernelCounter6401
end ProximityPrize.SubmissionLower
