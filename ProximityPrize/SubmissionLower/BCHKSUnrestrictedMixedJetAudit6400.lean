import ProximityPrize.SubmissionLower.BCHKSWeightedAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSUnrestrictedMixedJetAudit6400

/-!
Implementation-oriented mixed-jet audit using the unrestricted sparse Gao
source.

Use pairs `(G,H)` with `N(XG), N(YH) ⊆ N`.  For a specialized linear
factor `F=Y-P` and `R=FJ`, the raw logarithmic pair
`(G,H)=(J*F_X,J*F_Y)=(-P'J,J)` is already in this source.  It has received
local order at least `nu_i-1`, so the mixed-jet construction applies without
a good-edge normalization or the sparse Busé--Chèze kernel theorem.

The cheap jet-row degree is aggregated over every factor.  If all factor
Y-degrees are at most 52 and their sum is at most `DY-1`, monotonicity of the
boundary jet rank gives the safe charge
`2*T(52)*(DY-1)`.
-/

/-- Self-contained mixed-layer profile inequality. -/
theorem layerMass_le_deficiency_add_jets
    {I : Type*} [DecidableEq I]
    (S : Finset I) (nu : I → ℕ) (d b : ℕ) :
    S.card * (d - (b + 1)) ≤
      (∑ i ∈ S, (d - nu i)) +
        ∑ i ∈ S, (nu i - (b + 1)) := by
  calc
    S.card * (d - (b + 1)) =
        ∑ i ∈ S, (d - (b + 1)) := by simp
    _ ≤ ∑ i ∈ S,
        ((d - nu i) + (nu i - (b + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      omega
    _ = (∑ i ∈ S, (d - nu i)) +
        ∑ i ∈ S, (nu i - (b + 1)) := by
      rw [Finset.sum_add_distrib]

def bchksUnrestrictedYCap6400 : ℕ := 84608
def bchksUnrestrictedZCap6400 : ℕ := 1688975429
def bchksUnrestrictedPureRadicalCover6400 : ℕ := 285798288073592
def bchksUnrestrictedFullCoreBadCover6400 : ℕ := 221377387298816

def bchksUnrestrictedDegree6400 : ℕ := 52
def bchksUnrestrictedWeight6400 : ℕ := 9584634
def bchksUnrestrictedLatticePoints6400 : ℕ := 327369817
def bchksUnrestrictedColumnCap6400 : ℕ := 645154946
def bchksUnrestrictedJetRankOneComponent6400 : ℕ := 243023721
def bchksUnrestrictedExpensiveColumnCap6400 : ℕ := 159107504
def bchksUnrestrictedRuppertDegreeCover6400 : ℕ := 268728664666411712
def bchksUnrestrictedAggregateJetCover6400 : ℕ := 41123015925294
def bchksUnrestrictedMinorCover6400 : ℕ := 268769787682337006
def bchksUnrestrictedTotalCover6400 : ℕ := 269276963357709414

/-- Exact unrestricted source dimension `2N-N_X-N_Y`. -/
lemma bchksUnrestricted_columns6400 :
    bchksUnrestrictedWeight6400 = 52 * 185364 - 54293 - 1 ∧
      bchksUnrestrictedLatticePoints6400 =
        (bchksUnrestrictedDegree6400 + 1) *
            (bchksUnrestrictedWeight6400 + 1) -
          131071 * bchksUnrestrictedDegree6400 *
            (bchksUnrestrictedDegree6400 + 1) / 2 ∧
      bchksUnrestrictedColumnCap6400 =
        2 * bchksUnrestrictedLatticePoints6400 -
          (bchksUnrestrictedWeight6400 + 1) -
          (bchksUnrestrictedDegree6400 + 1) ∧
      bchksUnrestrictedColumnCap6400 +
          131071 * bchksUnrestrictedDegree6400 *
            (bchksUnrestrictedDegree6400 + 1) =
        (2 * bchksUnrestrictedDegree6400 + 1) *
            bchksUnrestrictedWeight6400 +
          bchksUnrestrictedDegree6400 := by
  norm_num [bchksUnrestrictedWeight6400,
    bchksUnrestrictedDegree6400,
    bchksUnrestrictedLatticePoints6400,
    bchksUnrestrictedColumnCap6400]

lemma bchksUnrestricted_rankAtBoundary6400 :
    bchksUnrestrictedJetRankOneComponent6400 =
        185364 * (52 * 51 / 2) - 54293 * 51 ∧
      bchksUnrestrictedExpensiveColumnCap6400 =
        bchksUnrestrictedColumnCap6400 -
          2 * bchksUnrestrictedJetRankOneComponent6400 := by
  norm_num [bchksUnrestrictedJetRankOneComponent6400,
    bchksUnrestrictedExpensiveColumnCap6400,
    bchksUnrestrictedColumnCap6400]

/-- Exact degree-52 capacity of the smaller H-source block at every mixed
Y-layer. -/
theorem degree52_selectedLayer_le_sourceColumns
    (b delta W : ℕ) (hb : b < 51)
    (hW : W + delta + 1 = 52 * 185364)
    (hWmin : 52 * 131071 ≤ W) :
    185364 * (52 - (b + 1)) - delta ≤
      W - 131071 * (b + 1) + 1 := by
  interval_cases b <;> norm_num at hW hWmin ⊢ <;> omega

/-- For the unrestricted source, one deficiency unit saves 105 source
columns and can remove at most 102 selected rows across both components.
The worst case is again the first non-alignment deficiency `54293`. -/
theorem bchksUnrestricted_effectiveColumns_le6400
    (delta w mixedRank C : ℕ)
    (hdelta : 54293 ≤ delta)
    (hweight : w + delta + 1 ≤ 52 * 185364)
    (hrank :
      185364 * (52 * 51 / 2) ≤ mixedRank + 51 * delta)
    (hcolumns :
      C + 131071 * 52 * 53 = (2 * 52 + 1) * w + 52) :
    C ≤ 2 * mixedRank + bchksUnrestrictedExpensiveColumnCap6400 := by
  dsimp [bchksUnrestrictedExpensiveColumnCap6400]
  norm_num at hweight hrank hcolumns
  omega

lemma bchksUnrestricted_gaoCharacteristic6400 :
    (2 * bchksUnrestrictedDegree6400 - 1) *
        bchksUnrestrictedWeight6400 < 2130706433 := by
  norm_num [bchksUnrestrictedDegree6400, bchksUnrestrictedWeight6400]

/-- The boundary selected rank is monotone through degree 52.  This is the
per-unit-Y-degree coefficient used to aggregate cheap rows across factors. -/
theorem boundaryJetRank_le_degree52
    (d T : ℕ) (hd : d ≤ 52)
    (hT : T ≤ 185364 * (d * (d - 1) / 2) - 54293 * (d - 1)) :
    2 * T ≤ 2 * bchksUnrestrictedJetRankOneComponent6400 := by
  dsimp [bchksUnrestrictedJetRankOneComponent6400]
  interval_cases d <;> norm_num at hT ⊢ <;> omega

theorem aggregateJetCover_le6400
    (degreeMass cheapCover : ℕ)
    (hmass : degreeMass ≤ bchksUnrestrictedYCap6400 - 1)
    (hcheap : cheapCover ≤
      2 * bchksUnrestrictedJetRankOneComponent6400 * degreeMass) :
    cheapCover ≤ bchksUnrestrictedAggregateJetCover6400 := by
  dsimp [bchksUnrestrictedAggregateJetCover6400,
    bchksUnrestrictedJetRankOneComponent6400,
    bchksUnrestrictedYCap6400] at hmass hcheap ⊢
  omega

lemma bchksUnrestricted_coverLedger6400 :
    bchksUnrestrictedRuppertDegreeCover6400 =
        bchksUnrestrictedExpensiveColumnCap6400 *
          (bchksUnrestrictedZCap6400 - 1) ∧
      bchksUnrestrictedAggregateJetCover6400 =
        2 * bchksUnrestrictedJetRankOneComponent6400 *
          (bchksUnrestrictedYCap6400 - 1) ∧
      bchksUnrestrictedMinorCover6400 =
        bchksUnrestrictedRuppertDegreeCover6400 +
          bchksUnrestrictedAggregateJetCover6400 ∧
      bchksUnrestrictedTotalCover6400 =
        bchksUnrestrictedMinorCover6400 +
          bchksUnrestrictedPureRadicalCover6400 +
          bchksUnrestrictedFullCoreBadCover6400 := by
  norm_num [bchksUnrestrictedRuppertDegreeCover6400,
    bchksUnrestrictedExpensiveColumnCap6400, bchksUnrestrictedZCap6400,
    bchksUnrestrictedAggregateJetCover6400,
    bchksUnrestrictedJetRankOneComponent6400, bchksUnrestrictedYCap6400,
    bchksUnrestrictedMinorCover6400, bchksUnrestrictedTotalCover6400,
    bchksUnrestrictedPureRadicalCover6400,
    bchksUnrestrictedFullCoreBadCover6400]

lemma bchksUnrestricted_fieldBudget6400 :
    bchksUnrestrictedTotalCover6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksUnrestrictedTotalCover6400 =
        5702036642290586 ∧
      2 ^ (128 : ℕ) *
          (bchksUnrestrictedTotalCover6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksUnrestrictedTotalCover6400, bchksWeightedNumerator6400,
    bchksListBound6400]

/-- Degree 53 is characteristic-safe but is the first miss for the
unrestricted source with the correctly aggregated cheap-row charge. -/
lemma bchksUnrestricted_degree53_noGo6400 :
    (2 * 53 - 1) * 9769998 < 2130706433 ∧
      bchksWeightedNumerator6400 < 279311810313111492 := by
  norm_num [bchksWeightedNumerator6400]

end BCHKSUnrestrictedMixedJetAudit6400
end ProximityPrize.SubmissionLower
