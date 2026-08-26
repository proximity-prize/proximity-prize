import ProximityPrize.SubmissionLower.BCHKSAugmentedSparseAudit6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSMixedJetAudit6400
theorem layerMass_le_deficiency_add_jets
    {I : Type*} [DecidableEq I]
    (S : Finset I) (nu : I → ℕ) (d b : ℕ) :
    S.card * (d - (b + 1)) ≤
      (∑ i ∈ S, (d - nu i)) +
        ∑ i ∈ S, (nu i - (b + 1)) := by
  calc
    S.card * (d - (b + 1)) =
        ∑ i ∈ S, (d - (b + 1)) := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ S,
        ((d - nu i) + (nu i - (b + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      omega
    _ = (∑ i ∈ S, (d - nu i)) +
        ∑ i ∈ S, (nu i - (b + 1)) := by
      rw [Finset.sum_add_distrib]
theorem degree53_selectedLayer_le_actualJets
    {I : Type*} [DecidableEq I]
    (S : Finset I) (nu : I → ℕ) (b delta : ℕ)
    (hcard : S.card = 185364)
    (hdef : ∑ i ∈ S, (53 - nu i) = delta) :
    185364 * (53 - (b + 1)) - delta ≤
      ∑ i ∈ S, (nu i - (b + 1)) := by
  have h := layerMass_le_deficiency_add_jets S nu 53 b
  rw [hcard, hdef] at h
  omega
theorem degree53_selectedLayer_le_sourceColumns
    (b delta W : ℕ) (hb : b < 52)
    (hW : W + delta + 1 = 53 * 185364)
    (hWmin : 53 * 131071 ≤ W) :
    185364 * (53 - (b + 1)) - delta ≤
      W - 131071 * (b + 1) + 1 := by
  interval_cases b <;> norm_num at hW hWmin ⊢ <;> omega
theorem degree53_mixedRank_profile
    (mixedRank delta : ℕ)
    (hlayers : 185364 * (53 * 52 / 2) - 52 * delta ≤ mixedRank) :
    185364 * (53 * 52 / 2) ≤ mixedRank + 52 * delta := by
  norm_num at hlayers ⊢
  omega
def bchksMixedDegree6400 : ℕ := 53
def bchksMixedWeight6400 : ℕ := 9769998
def bchksMixedLatticePoints6400 : ℕ := 340017345
def bchksMixedTopColumnCap6400 : ℕ := 667441401
def bchksMixedJetRankOneComponent6400 : ℕ := 252608356
def bchksMixedExpensiveColumnCap6400 : ℕ := 162224689
def bchksMixedRuppertDegreeCover6400 : ℕ := 273993513535941892
def bchksMixedJetDegreeCover6400 : ℕ := 26776485736
def bchksMixedMinorCover6400 : ℕ := 273993540312427628
def bchksMixedTotalCover6400 : ℕ := 274500715987800036
lemma bchksMixed_topEdgeColumns6400 :
    bchksMixedWeight6400 = 53 * 185364 - 54293 - 1 ∧
      bchksMixedLatticePoints6400 =
        (bchksMixedDegree6400 + 1) * (bchksMixedWeight6400 + 1) -
          131071 * bchksMixedDegree6400 *
            (bchksMixedDegree6400 + 1) / 2 ∧
      bchksMixedTopColumnCap6400 =
        2 * bchksMixedLatticePoints6400 -
          (bchksMixedWeight6400 + 1) -
          (bchksMixedDegree6400 + 1) -
          (bchksMixedWeight6400 -
              131071 * bchksMixedDegree6400 + 1) ∧
      bchksMixedTopColumnCap6400 =
        2 * bchksMixedDegree6400 * bchksMixedWeight6400 -
          131071 * bchksMixedDegree6400 ^ 2 +
          bchksMixedDegree6400 - 1 := by
  norm_num [bchksMixedWeight6400, bchksMixedDegree6400,
    bchksMixedLatticePoints6400, bchksMixedTopColumnCap6400]
lemma bchksMixed_rankAtBoundary6400 :
    bchksMixedJetRankOneComponent6400 =
        185364 * (53 * 52 / 2) - 54293 * 52 ∧
      bchksMixedExpensiveColumnCap6400 =
        bchksMixedTopColumnCap6400 -
          2 * bchksMixedJetRankOneComponent6400 := by
  norm_num [bchksMixedJetRankOneComponent6400,
    bchksMixedExpensiveColumnCap6400,
    bchksMixedTopColumnCap6400]
theorem bchksMixed_effectiveColumns_le6400
    (delta w mixedRank C : ℕ)
    (hdelta : 54293 ≤ delta)
    (hweight : w + delta + 1 ≤ 53 * 185364)
    (hrank :
      185364 * (53 * 52 / 2) ≤ mixedRank + 52 * delta)
    (hcolumns :
      C + 131071 * 53 ^ 2 + 1 = 2 * 53 * w + 53) :
    C ≤ 2 * mixedRank + bchksMixedExpensiveColumnCap6400 := by
  dsimp [bchksMixedExpensiveColumnCap6400]
  norm_num at hweight hrank hcolumns
  omega
lemma bchksMixed_gaoCharacteristic6400 :
    (2 * bchksMixedDegree6400 - 1) *
        bchksMixedWeight6400 < 2130706433 := by
  norm_num [bchksMixedDegree6400, bchksMixedWeight6400]
lemma bchksMixed_minorLedger6400 :
    bchksMixedRuppertDegreeCover6400 =
        bchksMixedExpensiveColumnCap6400 *
          (bchksCofactorZCap6400 - 1) ∧
      bchksMixedJetDegreeCover6400 =
        2 * bchksMixedJetRankOneComponent6400 *
          bchksMixedDegree6400 ∧
      bchksMixedMinorCover6400 =
        bchksMixedRuppertDegreeCover6400 +
          bchksMixedJetDegreeCover6400 ∧
      bchksMixedTotalCover6400 =
        bchksMixedMinorCover6400 +
          BCHKSAugmentedSparseAudit6400.bchksAugmentedPureRadicalCover6400 +
          BCHKSAugmentedSparseAudit6400.bchksAugmentedFullCoreBadCover6400 := by
  norm_num [bchksMixedRuppertDegreeCover6400,
    bchksMixedExpensiveColumnCap6400, bchksCofactorZCap6400,
    bchksMixedJetDegreeCover6400,
    bchksMixedJetRankOneComponent6400, bchksMixedDegree6400,
    bchksMixedMinorCover6400, bchksMixedTotalCover6400,
    BCHKSAugmentedSparseAudit6400.bchksAugmentedPureRadicalCover6400,
    BCHKSAugmentedSparseAudit6400.bchksAugmentedFullCoreBadCover6400]
lemma bchksMixed_fieldBudget6400 :
    bchksMixedTotalCover6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksMixedTotalCover6400 =
        478284012199964 ∧
      2 ^ (128 : ℕ) *
          (bchksMixedTotalCover6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksMixedTotalCover6400, bchksWeightedNumerator6400,
    bchksListBound6400]
lemma bchksMixed_degree54_noGo6400 :
    (2 * 54 - 1) * 9955362 < 2130706433 ∧
      bchksWeightedNumerator6400 < 284625642192064232 := by
  norm_num [bchksWeightedNumerator6400]
end BCHKSMixedJetAudit6400
end ProximityPrize.SubmissionLower
