import ProximityPrize.SubmissionLower.BCHKSSparseCofactorAudit6400
import ProximityPrize.SubmissionLower.BCHKSCofactorLocalBridge6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSAugmentedSparseAudit6400
open BCHKSLocalValuation6400
open BCHKSDerivativeLowering6400
theorem localOrder_quotient_ge_pred
    {A : Type*} [CommSemiring A] [IsDomain A]
    (R F J : Polynomial (Polynomial A)) (nu : ℕ)
    (hR : R ≠ 0) (hF : F ≠ 0) (hJ : J ≠ 0)
    (hfac : R = F * J)
    (horder : localOrder R = nu)
    (hForder : localOrder F ≤ 1) :
    nu - 1 ≤ localOrder J := by
  have hadd : localOrder R = localOrder F + localOrder J := by
    rw [hfac, localOrder_mul hF hJ]
  omega
theorem quotient_localVanish_pred
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
theorem localVanish_mono
    {A : Type*} [CommSemiring A]
    {P : Polynomial (Polynomial A)} {m n : ℕ}
    (hP : LocalVanish P m) (hnm : n ≤ m) :
    LocalVanish P n := by
  intro s t hst
  exact hP s t (lt_of_lt_of_le hst hnm)
theorem normalizedKernelComponent_localVanish
    {A : Type*} [CommRing A] [IsDomain A]
    (F J dF dJ : Polynomial (Polynomial A)) (c : A) (s t : ℕ)
    (hF : LocalVanish F s) (hJ : LocalVanish J t)
    (hdF : LocalVanish dF (s - 1))
    (hdJ : LocalVanish dJ (t - 1)) :
    LocalVanish
      (F * dJ - Polynomial.C (Polynomial.C c) * (J * dF))
      (s + t - 1) := by
  have hleft0 : LocalVanish (F * dJ) (s + (t - 1)) :=
    localVanish_mul hF hdJ
  have hleft : LocalVanish (F * dJ) (s + t - 1) :=
    localVanish_mono hleft0 (by omega)
  have hright0 : LocalVanish (J * dF) (t + (s - 1)) :=
    localVanish_mul hJ hdF
  have hconst :
      LocalVanish (Polynomial.C (Polynomial.C c) :
        Polynomial (Polynomial A)) 0 := by
    intro u v huv
    omega
  have hright1 : LocalVanish
      (Polynomial.C (Polynomial.C c) * (J * dF))
      (t + (s - 1)) := by
    simpa using localVanish_mul hconst hright0
  have hright : LocalVanish
      (Polynomial.C (Polynomial.C c) * (J * dF))
      (s + t - 1) :=
    localVanish_mono hright1 (by omega)
  exact localVanish_sub hleft hright
theorem sum_le_card_add_sum_pred
    {I : Type*} [DecidableEq I] (S : Finset I) (nu : I → ℕ) :
    (∑ i ∈ S, nu i) ≤ S.card + ∑ i ∈ S, (nu i - 1) := by
  calc
    (∑ i ∈ S, nu i) ≤
        ∑ i ∈ S, (1 + (nu i - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      omega
    _ = S.card + ∑ i ∈ S, (nu i - 1) := by
      rw [Finset.sum_add_distrib]
      simp
theorem eq_zero_of_natDegree_lt_sum_rootMultiplicity
    {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (P : Polynomial F) (omega : I ↪ F) (S : Finset I) (mu : I → ℕ)
    (hdegree : P.natDegree < ∑ i ∈ S, mu i)
    (hmult : ∀ i ∈ S, mu i ≤ P.rootMultiplicity (omega i)) :
    P = 0 := by
  by_contra hP
  have hroots := BCHKSWeightedSubstitution.sum_le_natDegree_of_rootMultiplicity
    P omega S mu hmult
  omega
theorem degree27_jetMass_add_deficiency_ge
    (sumNu jetMass delta : ℕ)
    (hsum : sumNu + delta = 27 * 185364)
    (hpred : sumNu ≤ 185364 + jetMass) :
    26 * 185364 ≤ jetMass + delta := by
  norm_num at hsum ⊢
  omega
def bchksAugmentedDegree6400 : ℕ := 27
def bchksAugmentedWeight6400 : ℕ := 4950534
def bchksAugmentedLatticePoints6400 : ℕ := 89070142
def bchksAugmentedTopColumnCap6400 : ℕ := 171778103
def bchksAugmentedJetMass6400 : ℕ := 4765171
def bchksAugmentedExpensiveColumnCap6400 : ℕ := 162247761
def bchksAugmentedJetDegreeCover6400 : ℕ := 257319234
def bchksAugmentedMinorCover6400 : ℕ := 274032481834335942
def bchksAugmentedTotalCover6400 : ℕ := 274318294773534132
lemma bchksAugmented_topEdgeColumns6400 :
    bchksAugmentedWeight6400 = 27 * 185364 - 54293 - 1 ∧
      bchksAugmentedLatticePoints6400 =
        (bchksAugmentedDegree6400 + 1) *
            (bchksAugmentedWeight6400 + 1) -
          131071 * bchksAugmentedDegree6400 *
            (bchksAugmentedDegree6400 + 1) / 2 ∧
      bchksAugmentedTopColumnCap6400 =
        2 * bchksAugmentedLatticePoints6400 -
          (bchksAugmentedWeight6400 + 1) -
          (bchksAugmentedDegree6400 + 1) -
          (bchksAugmentedWeight6400 -
              131071 * bchksAugmentedDegree6400 + 1) ∧
      bchksAugmentedTopColumnCap6400 =
        2 * bchksAugmentedDegree6400 *
            bchksAugmentedWeight6400 -
          131071 * bchksAugmentedDegree6400 ^ 2 +
          bchksAugmentedDegree6400 - 1 := by
  norm_num [bchksAugmentedWeight6400, bchksAugmentedDegree6400,
    bchksAugmentedLatticePoints6400,
    bchksAugmentedTopColumnCap6400]
lemma bchksAugmented_jetMass6400 :
    bchksAugmentedJetMass6400 = 26 * 185364 - 54293 ∧
      bchksAugmentedExpensiveColumnCap6400 =
        bchksAugmentedTopColumnCap6400 -
          2 * bchksAugmentedJetMass6400 := by
  norm_num [bchksAugmentedJetMass6400,
    bchksAugmentedExpensiveColumnCap6400,
    bchksAugmentedTopColumnCap6400]
theorem bchksAugmented_effectiveColumns_le6400
    (delta w jetMass C : ℕ)
    (hdelta : 54293 ≤ delta)
    (hweight : w + delta + 1 ≤ 27 * 185364)
    (hjet : 26 * 185364 ≤ jetMass + delta)
    (hcolumns :
      C + 131071 * 27 ^ 2 + 1 = 2 * 27 * w + 27) :
    C ≤ 2 * jetMass + bchksAugmentedExpensiveColumnCap6400 := by
  dsimp [bchksAugmentedExpensiveColumnCap6400]
  norm_num at hweight hjet hcolumns
  omega
lemma bchksAugmented_gaoCharacteristic6400 :
    (2 * bchksAugmentedDegree6400 - 1) *
        bchksAugmentedWeight6400 < 2130706433 := by
  norm_num [bchksAugmentedDegree6400, bchksAugmentedWeight6400]
lemma bchksAugmented_minorLedger6400 :
    bchksAugmentedJetDegreeCover6400 =
        2 * bchksAugmentedJetMass6400 * bchksAugmentedDegree6400 ∧
      bchksAugmentedMinorCover6400 =
        bchksAugmentedExpensiveColumnCap6400 *
            (bchksCofactorZCap6400 - 1) +
          bchksAugmentedJetDegreeCover6400 ∧
      bchksAugmentedTotalCover6400 =
        bchksCofactorRadicalCover6400 +
          bchksAugmentedMinorCover6400 := by
  norm_num [bchksAugmentedJetDegreeCover6400,
    bchksAugmentedJetMass6400, bchksAugmentedDegree6400,
    bchksAugmentedMinorCover6400,
    bchksAugmentedExpensiveColumnCap6400, bchksCofactorZCap6400,
    bchksAugmentedTotalCover6400, bchksCofactorRadicalCover6400]
lemma bchksAugmented_fieldBudget6400 :
    bchksAugmentedTotalCover6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksAugmentedTotalCover6400 =
        660705226465868 ∧
      2 ^ (128 : ℕ) *
          (bchksAugmentedTotalCover6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksAugmentedTotalCover6400, bchksWeightedNumerator6400,
    bchksListBound6400]
def bchksAugmentedPureRadicalCover6400 : ℕ := 285798288073592
def bchksAugmentedFullCoreBadCover6400 : ℕ := 221377387298816
def bchksAugmentedUnconditionalCandidateTotal6400 : ℕ :=
  274539657509708350
lemma bchksAugmented_unconditionalCandidateLedger6400 :
    bchksAugmentedPureRadicalCover6400 =
        2 * bchksCofactorProduct6400 ∧
      bchksAugmentedFullCoreBadCover6400 =
        131072 * (bchksCofactorZCap6400 - 1) ∧
      bchksAugmentedUnconditionalCandidateTotal6400 =
        bchksAugmentedMinorCover6400 +
          bchksAugmentedPureRadicalCover6400 +
          bchksAugmentedFullCoreBadCover6400 ∧
      bchksAugmentedUnconditionalCandidateTotal6400 <
        bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 -
          bchksAugmentedUnconditionalCandidateTotal6400 =
        439342490291650 ∧
      2 ^ (128 : ℕ) *
          (bchksAugmentedUnconditionalCandidateTotal6400 +
            bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksAugmentedPureRadicalCover6400,
    bchksCofactorProduct6400, bchksAugmentedFullCoreBadCover6400,
    bchksCofactorZCap6400,
    bchksAugmentedUnconditionalCandidateTotal6400,
    bchksAugmentedMinorCover6400, bchksWeightedNumerator6400,
    bchksListBound6400]
end BCHKSAugmentedSparseAudit6400
end ProximityPrize.SubmissionLower
