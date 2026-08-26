import ProximityPrize.SubmissionLower.BCHKSAugmentedSparseAudit6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSMixedJetGaoAudit6400
open BCHKSLocalValuation6400
open BCHKSDerivativeLowering6400
theorem quotient_localVanish_pred_global
    {A : Type*} [CommSemiring A] [IsDomain A]
    (R F J : Polynomial (Polynomial A)) (nu : ℕ)
    (hR : R ≠ 0) (hF : F ≠ 0) (hJ : J ≠ 0)
    (hfac : R = F * J)
    (hvan : LocalVanish R nu)
    (hForder : localOrder F ≤ 1) :
    LocalVanish J (nu - 1) := by
  have hRorder : nu ≤ localOrder R :=
    (localVanish_iff_le_localOrder hR nu).mp hvan
  have hadd : localOrder R = localOrder F + localOrder J := by
    rw [hfac, localOrder_mul hF hJ]
  apply (localVanish_iff_le_localOrder hJ (nu - 1)).mpr
  omega
theorem rawGaoComponent_localVanish
    {A : Type*} [CommRing A] [IsDomain A]
    (M J : Polynomial (Polynomial A)) (nu : ℕ)
    (hJ : LocalVanish J (nu - 1)) :
    LocalVanish (M * J) (nu - 1) := by
  have hM : LocalVanish M 0 := by
    intro s t hst
    omega
  simpa using localVanish_mul hM hJ
theorem rawGaoPair_fixed_localJets
    {A : Type*} [CommRing A] [IsDomain A]
    (R F J M : Polynomial (Polynomial A)) (nu : ℕ)
    (hR : R ≠ 0) (hF : F ≠ 0) (hJ : J ≠ 0)
    (hfac : R = F * J)
    (hvan : LocalVanish R nu)
    (hForder : localOrder F ≤ 1) :
    LocalVanish (M * J) (nu - 1) ∧
      LocalVanish J (nu - 1) := by
  have hquot := quotient_localVanish_pred_global
    R F J nu hR hF hJ hfac hvan hForder
  exact ⟨rawGaoComponent_localVanish M J nu hquot, hquot⟩
def mixedJetLayerMass
    {I : Type*} [DecidableEq I]
    (S : Finset I) (nu : I → ℕ) (b : ℕ) : ℕ :=
  ∑ i ∈ S, (nu i - 1 - b)
def mixedJetMass
    {I : Type*} [DecidableEq I]
    (S : Finset I) (nu : I → ℕ) (d : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (d - 1), mixedJetLayerMass S nu b
theorem full_layer_mass_le_actual_add_deficiency
    {I : Type*} [DecidableEq I]
    (S : Finset I) (nu : I → ℕ) (d delta b : ℕ)
    (hnu : ∀ i ∈ S, nu i ≤ d)
    (hdelta : (∑ i ∈ S, (d - nu i)) = delta) :
    (∑ i ∈ S, (d - 1 - b)) ≤
      mixedJetLayerMass S nu b + delta := by
  rw [← hdelta]
  unfold mixedJetLayerMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have := hnu i hi
  omega
theorem full_mixed_mass_le_actual_add_deficiency
    {I : Type*} [DecidableEq I]
    (S : Finset I) (nu : I → ℕ) (d delta : ℕ)
    (hnu : ∀ i ∈ S, nu i ≤ d)
    (hdelta : (∑ i ∈ S, (d - nu i)) = delta) :
    (∑ b ∈ Finset.range (d - 1),
        ∑ i ∈ S, (d - 1 - b)) ≤
      mixedJetMass S nu d + (d - 1) * delta := by
  unfold mixedJetMass
  calc
    (∑ b ∈ Finset.range (d - 1),
        ∑ i ∈ S, (d - 1 - b)) ≤
        ∑ b ∈ Finset.range (d - 1),
          (mixedJetLayerMass S nu b + delta) := by
      apply Finset.sum_le_sum
      intro b hb
      exact full_layer_mass_le_actual_add_deficiency
        S nu d delta b hnu hdelta
    _ = (∑ b ∈ Finset.range (d - 1),
          mixedJetLayerMass S nu b) + (d - 1) * delta := by
      rw [Finset.sum_add_distrib]
      simp
theorem full_mixed_mass_formula (a n : ℕ) :
    (∑ b ∈ Finset.range n, a * (n - b)) =
      a * (∑ b ∈ Finset.range (n + 1), b) := by
  rw [← Finset.mul_sum]
  congr 1
  have hreflect := Finset.sum_range_reflect (fun b : ℕ => b) (n + 1)
  simpa [Finset.sum_range_succ] using hreflect
theorem retained_layer_fits_H_columns
    (a k d delta w eps b : ℕ)
    (hka : k ≤ a)
    (hpartition :
      a * (d - 1 - b) + (b + 1) * a = d * a)
    (hweight : w + delta + 1 + eps = d * a) :
    a * (d - 1 - b) - delta - eps = 0 ∨
      (a * (d - 1 - b) - delta - eps) + k * (b + 1) ≤
        w + 1 := by
  by_cases hzero : a * (d - 1 - b) - delta - eps = 0
  · exact Or.inl hzero
  right
  have hpos : delta + eps < a * (d - 1 - b) := by
    have : 0 < a * (d - 1 - b) - delta - eps :=
      Nat.pos_of_ne_zero hzero
    omega
  have hmul : k * (b + 1) ≤ (b + 1) * a := by
    calc
      k * (b + 1) ≤ a * (b + 1) := Nat.mul_le_mul_right (b + 1) hka
      _ = (b + 1) * a := Nat.mul_comm _ _
  omega
theorem effective_columns_worst_at_max_weight
    (d eps C Cmax T Tmin : ℕ)
    (hC : C + 2 * d * eps ≤ Cmax)
    (hT : Tmin ≤ T + (d - 1) * eps) :
    C + 2 * Tmin ≤ Cmax + 2 * T := by
  by_cases hd : d = 0
  · subst d
    simp at hT
    omega
  have hdid : d = (d - 1) + 1 := by omega
  nlinarith
def mixedGaoDegreeCap6400 : ℕ := 52
def mixedGaoMaxWeight6400 : ℕ := 9584634
def mixedGaoLatticePoints6400 : ℕ := 327369817
def mixedGaoUnrestrictedColumns6400 : ℕ := 645154946
def mixedGaoRowsPerComponent6400 : ℕ := 243023721
def mixedGaoExpensiveRows6400 : ℕ := 159107504
def mixedGaoCheapAggregate6400 : ℕ := 41123015925294
def mixedGaoPureRadicalCover6400 : ℕ := 285798288073592
def mixedGaoFullCoreBadCover6400 : ℕ := 221377387298816
def mixedGaoTotalCover6400 : ℕ := 269276963357709414
lemma mixedGao_degree52_exact6400 :
    mixedGaoMaxWeight6400 = 52 * 185364 - 54293 - 1 ∧
    mixedGaoLatticePoints6400 =
      (52 + 1) * (mixedGaoMaxWeight6400 + 1) -
        131071 * 52 * (52 + 1) / 2 ∧
    mixedGaoUnrestrictedColumns6400 =
      2 * mixedGaoLatticePoints6400 -
        (mixedGaoMaxWeight6400 + 1) - (52 + 1) ∧
    mixedGaoRowsPerComponent6400 =
      185364 * (52 * 51 / 2) - 54293 * 51 ∧
    mixedGaoExpensiveRows6400 =
      mixedGaoUnrestrictedColumns6400 -
        2 * mixedGaoRowsPerComponent6400 ∧
    mixedGaoCheapAggregate6400 =
      2 * mixedGaoRowsPerComponent6400 * (84608 - 1) ∧
    mixedGaoTotalCover6400 =
      mixedGaoExpensiveRows6400 * (1688975429 - 1) +
        mixedGaoCheapAggregate6400 +
        mixedGaoPureRadicalCover6400 +
        mixedGaoFullCoreBadCover6400 := by
  norm_num [mixedGaoMaxWeight6400, mixedGaoLatticePoints6400,
    mixedGaoUnrestrictedColumns6400, mixedGaoRowsPerComponent6400,
    mixedGaoExpensiveRows6400, mixedGaoCheapAggregate6400,
    mixedGaoTotalCover6400, mixedGaoPureRadicalCover6400,
    mixedGaoFullCoreBadCover6400]
lemma mixedGao_degree52_fieldBudget6400 :
    mixedGaoTotalCover6400 < bchksWeightedNumerator6400 ∧
    bchksWeightedNumerator6400 - mixedGaoTotalCover6400 =
      5702036642290586 ∧
    2 ^ (128 : ℕ) *
        (mixedGaoTotalCover6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [mixedGaoTotalCover6400, bchksWeightedNumerator6400,
    bchksListBound6400]
def mixedGaoDegree53Total6400 : ℕ := 279311810313111492
lemma mixedGao_degree53_boundary6400 :
    bchksWeightedNumerator6400 < mixedGaoDegree53Total6400 ∧
    mixedGaoDegree53Total6400 - bchksWeightedNumerator6400 =
      4332810313111492 := by
  norm_num [mixedGaoDegree53Total6400, bchksWeightedNumerator6400]
end BCHKSMixedJetGaoAudit6400
end ProximityPrize.SubmissionLower
