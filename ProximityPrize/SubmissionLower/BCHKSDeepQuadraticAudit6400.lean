import ProximityPrize.SubmissionLower.BCHKSGlobalRadicalAudit6400
import ProximityPrize.SubmissionLower.BCHKSQuadraticOwnerClosure6400
namespace ProximityPrize.SubmissionLower
def bchksDeepRepeatedZMass6400 : ℕ := 3686750650
def bchksDeepQuadraticFactorCount6400 : ℕ := 61646
def bchksDeepQuadraticParityObstruction6400 : ℕ := 3865801382067900
def bchksDeepQuadraticCoordinateLedgers6400 : ℕ := 1932919124787200
def bchksDeepQuadraticBranchFibres6400 : ℕ := 9466483052
def bchksDeepQuadraticAddon6400 : ℕ := 5798729973338152
def bchksDeepRadicalQuadraticTotal6400 : ℕ := 268528908868039177
def bchksDeepResidualQuadraticXMargin6400 : ℕ := 349525
def bchksDeepResidualQuadraticParityObstruction6400 : ℕ :=
  10308884794028700
def bchksDeepResidualQuadraticAddon6400 : ℕ := 12241813385298952
def bchksDeepResidualQuadraticTotal6400 : ℕ := 274971992279999977
lemma bchksDeepRepeatedZMass_eq6400 :
    bchksDeepRepeatedZMass6400 =
      (bchksSixteenthDerivativeZCap6400 - 1) / 17 := by
  norm_num [bchksDeepRepeatedZMass6400,
    bchksSixteenthDerivativeZCap6400]
lemma bchksDeepQuadraticFactorCount_eq6400 :
    bchksDeepQuadraticFactorCount6400 =
      (bchksSixteenthDerivativeYCap6400 - 1) / (17 * 2) := by
  norm_num [bchksDeepQuadraticFactorCount6400,
    bchksSixteenthDerivativeYCap6400]
lemma bchksDeepQuadraticLedger_eq6400 :
    bchksDeepQuadraticParityObstruction6400 =
        (4 * 131071 - 1) * 2 * bchksDeepRepeatedZMass6400 ∧
      bchksDeepQuadraticCoordinateLedgers6400 =
        2 * 262144 * bchksDeepRepeatedZMass6400 ∧
      bchksDeepQuadraticBranchFibres6400 =
        bchksDeepQuadraticFactorCount6400 * 2 * (76780 + 1) ∧
      bchksDeepQuadraticAddon6400 =
        bchksDeepQuadraticParityObstruction6400 +
          bchksDeepQuadraticCoordinateLedgers6400 +
          bchksDeepQuadraticBranchFibres6400 := by
  norm_num [bchksDeepQuadraticParityObstruction6400,
    bchksDeepRepeatedZMass6400,
    bchksDeepQuadraticCoordinateLedgers6400,
    bchksDeepQuadraticBranchFibres6400,
    bchksDeepQuadraticFactorCount6400,
    bchksDeepQuadraticAddon6400]
lemma bchksDeepRadicalQuadraticBudget6400 :
    bchksDeepRadicalQuadraticTotal6400 =
        bchksSixteenthDerivativeTwoLedgerCover6400 +
          bchksDeepQuadraticAddon6400 ∧
      bchksDeepRadicalQuadraticTotal6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksDeepRadicalQuadraticTotal6400 =
        6450091131960823 ∧
      2 ^ (128 : ℕ) *
          (bchksDeepRadicalQuadraticTotal6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksDeepRadicalQuadraticTotal6400,
    bchksSixteenthDerivativeTwoLedgerCover6400,
    bchksDeepQuadraticAddon6400, bchksWeightedNumerator6400,
    bchksListBound6400]
theorem bchksDeepResidualQuadratic_weight_lt6400
    (e w t : ℕ) (he : 17 ≤ e) (ht : t ≤ 262144)
    (hfail : (e - 1) * w + 868689 <
      87382 + (e - 1) * (131071 + 87382 + t)) :
    w < 480597 := by
  have hepos : 0 < e - 1 := by omega
  have hright :
      87382 + (e - 1) * (131071 + 87382 + t) <
        868689 + (e - 1) * 480597 := by
    have hmul :
        (e - 1) * (131071 + 87382 + t) ≤
          (e - 1) * 480597 := by
      exact Nat.mul_le_mul_left (e - 1) (by omega)
    omega
  have hprod : (e - 1) * w < (e - 1) * 480597 := by
    omega
  exact (Nat.mul_lt_mul_left hepos).mp hprod
lemma bchksDeepResidualQuadraticXMargin_eq6400 :
    bchksDeepResidualQuadraticXMargin6400 = 480596 - 131071 := by
  norm_num [bchksDeepResidualQuadraticXMargin6400]
lemma bchksDeepResidualQuadraticLedger_eq6400 :
    bchksDeepResidualQuadraticParityObstruction6400 =
        (4 * bchksDeepResidualQuadraticXMargin6400 - 1) * 2 *
          bchksDeepRepeatedZMass6400 ∧
      bchksDeepResidualQuadraticAddon6400 =
        bchksDeepResidualQuadraticParityObstruction6400 +
          bchksDeepQuadraticCoordinateLedgers6400 +
          bchksDeepQuadraticBranchFibres6400 ∧
      bchksDeepResidualQuadraticTotal6400 =
        bchksSixteenthDerivativeTwoLedgerCover6400 +
          bchksDeepResidualQuadraticAddon6400 := by
  norm_num [bchksDeepResidualQuadraticParityObstruction6400,
    bchksDeepResidualQuadraticXMargin6400,
    bchksDeepRepeatedZMass6400,
    bchksDeepResidualQuadraticAddon6400,
    bchksDeepQuadraticCoordinateLedgers6400,
    bchksDeepQuadraticBranchFibres6400,
    bchksDeepResidualQuadraticTotal6400,
    bchksSixteenthDerivativeTwoLedgerCover6400]
lemma bchksDeepResidualQuadraticBudget6400 :
    bchksDeepResidualQuadraticTotal6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 -
          bchksDeepResidualQuadraticTotal6400 = 7007720000023 ∧
      2 ^ (128 : ℕ) *
          (bchksDeepResidualQuadraticTotal6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksDeepResidualQuadraticTotal6400,
    bchksWeightedNumerator6400, bchksListBound6400]
lemma bchksDeepCubicE17Threshold6400 :
    92520 + (3 - 2) * 131071 = 223591 ∧
      87382 + 16 * (131071 + 87382 + 223591) ≤
        16 * (3 * 131071) + 868689 ∧
      16 * (3 * 131071) + 868689 <
        87382 + 16 * (131071 + 87382 + 223592) := by
  norm_num
lemma bchksDeepCubicLimitingThreshold6400 :
    (3 - 1) * 131071 - 87382 = 174760 := by
  norm_num
end ProximityPrize.SubmissionLower
