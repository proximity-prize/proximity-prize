import ProximityPrize.SubmissionLower.BCHKSDeepHigherDegreeAudit6400
import ProximityPrize.SubmissionLower.BCHKSWeightedSecant6400
namespace ProximityPrize.SubmissionLower
def bchksSparseMultiplicity6400 : ℕ := 178697
def bchksSparseMargin6400 : ℕ := 54294
def bchksSparseXCap6400 : ℕ := 33123936414
def bchksSparseYCap6400 : ℕ := 252718
def bchksSparseZCap6400 : ℕ := 5066984874
def bchksSparseVariableCount6400 : ℕ :=
  21207593096675855572131529
def bchksSparseConstraintCount6400 : ℕ :=
  21207593096675839816761344
def bchksSparseSlack6400 : ℕ := 15755370185
def bchksSparseProduct6400 : ℕ := 1280513216149941
def bchksSparseBaseCover6400 : ℕ := 43868890455
def bchksSparseRadicalCover6400 : ℕ := 2561070301190337
def bchksSparseDegreeCap6400 : ℕ := 16
def bchksSparseWeightCap6400 : ℕ := 4183700
def bchksSparseLatticePoints6400 : ℕ := 53297261
def bchksSparseColumnCap6400 : ℕ := 102410787
def bchksSparseDistinctZMass6400 : ℕ := 2533492436
def bchksSparseMinorCover6400 : ℕ := 259456954229307132
def bchksSparseTotalCover6400 : ℕ := 262018024530497469
lemma bchksSparse_exactMargin6400 :
    bchksSparseXCap6400 + bchksSparseMargin6400 =
      bchksSparseMultiplicity6400 * 185364 ∧
    bchksSparseMargin6400 = 185364 - 131071 + 1 := by
  norm_num [bchksSparseXCap6400, bchksSparseMargin6400,
    bchksSparseMultiplicity6400]
lemma bchksSparse_variableFormula6400 :
    6 * bchksSparseVariableCount6400 =
      bchksSparseYCap6400 *
        (6 * bchksSparseXCap6400 * bchksSparseZCap6400 -
          3 * (bchksSparseXCap6400 +
            131071 * bchksSparseZCap6400) *
              (bchksSparseYCap6400 - 1) +
          131071 * (bchksSparseYCap6400 - 1) *
            (2 * bchksSparseYCap6400 - 1)) := by
  norm_num [bchksSparseVariableCount6400, bchksSparseYCap6400,
    bchksSparseXCap6400, bchksSparseZCap6400]
lemma bchksSparse_constraintFormula6400 :
    6 * bchksSparseConstraintCount6400 =
      262144 * bchksSparseMultiplicity6400 *
        (6 * bchksSparseMultiplicity6400 * bchksSparseZCap6400 -
          3 * (bchksSparseMultiplicity6400 + bchksSparseZCap6400) *
            (bchksSparseMultiplicity6400 - 1) +
          (bchksSparseMultiplicity6400 - 1) *
            (2 * bchksSparseMultiplicity6400 - 1)) := by
  norm_num [bchksSparseConstraintCount6400,
    bchksSparseMultiplicity6400, bchksSparseZCap6400]
lemma bchksSparse_interpolationFeasible6400 :
    bchksSparseConstraintCount6400 + bchksSparseSlack6400 =
      bchksSparseVariableCount6400 := by
  norm_num [bchksSparseConstraintCount6400, bchksSparseSlack6400,
    bchksSparseVariableCount6400]
theorem bchksSparse_residualWeight_le6400
    (d e w ell t : ℕ)
    (hd : 1 ≤ d) (he : 2 ≤ e) (hd16 : d ≤ 16)
    (hell : ell ≤ 87382) (ht : t ≤ (d - 1) * 262144)
    (hfail : (e - 1) * w + bchksSparseMargin6400 <
      ell + (e - 1) * (131071 + ell + t)) :
    w ≤ bchksSparseWeightCap6400 := by
  let B := 131071 + 87382 + (d - 1) * 262144
  have hr : 1 ≤ e - 1 := by omega
  have hinner : 131071 + ell + t ≤ B := by
    dsimp [B]
    omega
  have hright :
      ell + (e - 1) * (131071 + ell + t) ≤
        87382 + (e - 1) * B := by
    exact Nat.add_le_add hell (Nat.mul_le_mul_left (e - 1) hinner)
  have hfail' :
      (e - 1) * w + 54294 < 87382 + (e - 1) * B := by
    exact hfail.trans_le (by simpa [bchksSparseMargin6400] using hright)
  have hB : B ≤ 4150613 := by
    dsimp [B]
    omega
  by_contra hnot
  have hw : B + 33088 ≤ w := by
    push Not at hnot
    dsimp [bchksSparseWeightCap6400] at hnot
    omega
  have hmul := Nat.mul_le_mul_left (e - 1) hw
  have hgap : 33088 ≤ (e - 1) * 33088 := by
    have := Nat.mul_le_mul_right 33088 hr
    simpa [Nat.mul_comm] using this
  have : (e - 1) * B + 33088 ≤ (e - 1) * w := by
    rw [Nat.mul_add] at hmul
    omega
  omega
lemma bchksSparse_triangleColumns6400 :
    bchksSparseLatticePoints6400 =
        (bchksSparseDegreeCap6400 + 1) *
            (bchksSparseWeightCap6400 + 1) -
          131071 * bchksSparseDegreeCap6400 *
            (bchksSparseDegreeCap6400 + 1) / 2 ∧
      bchksSparseColumnCap6400 =
        2 * bchksSparseLatticePoints6400 -
          (bchksSparseWeightCap6400 + 1) -
          2 * (bchksSparseDegreeCap6400 + 1) ∧
      bchksSparseColumnCap6400 =
        (2 * bchksSparseDegreeCap6400 + 1) *
            bchksSparseWeightCap6400 -
          131071 * bchksSparseDegreeCap6400 *
            (bchksSparseDegreeCap6400 + 1) - 1 := by
  norm_num [bchksSparseLatticePoints6400, bchksSparseDegreeCap6400,
    bchksSparseWeightCap6400, bchksSparseColumnCap6400]
lemma bchksSparse_gaoCharacteristic6400 :
    (2 * bchksSparseDegreeCap6400 - 1) *
        bchksSparseWeightCap6400 < 2130706433 := by
  norm_num [bchksSparseDegreeCap6400, bchksSparseWeightCap6400]
theorem bchksSparse_columns_le_of_degree_le16
    (d w C : ℕ) (hd : 1 ≤ d) (hd16 : d ≤ 16)
    (hw : w ≤ bchksSparseWeightCap6400)
    (hC : C + 131071 * d * (d + 1) + 1 = (2 * d + 1) * w) :
    C ≤ bchksSparseColumnCap6400 := by
  dsimp [bchksSparseWeightCap6400, bchksSparseColumnCap6400] at hw ⊢
  interval_cases d <;> norm_num at hC ⊢ <;> omega
lemma bchksSparse_coverLedger6400 :
    bchksSparseProduct6400 =
        (bchksSparseYCap6400 - 1) * (bchksSparseZCap6400 - 1) ∧
      bchksSparseBaseCover6400 =
        (bchksSparseYCap6400 - 1) * bchksStableFiberCap6400 +
          (262144 * (bchksSparseZCap6400 - 1) +
              bchksStableChargeGap6400 - 1) /
            bchksStableChargeGap6400 ∧
      bchksSparseRadicalCover6400 =
        2 * bchksSparseProduct6400 + bchksSparseBaseCover6400 ∧
      bchksSparseDistinctZMass6400 =
        (bchksSparseZCap6400 - 1) / 2 ∧
      bchksSparseMinorCover6400 =
        bchksSparseColumnCap6400 * bchksSparseDistinctZMass6400 ∧
      bchksSparseTotalCover6400 =
        bchksSparseRadicalCover6400 + bchksSparseMinorCover6400 := by
  norm_num [bchksSparseProduct6400, bchksSparseYCap6400,
    bchksSparseZCap6400, bchksSparseBaseCover6400,
    bchksStableFiberCap6400, bchksStableChargeGap6400,
    bchksSparseRadicalCover6400, bchksSparseDistinctZMass6400,
    bchksSparseMinorCover6400, bchksSparseColumnCap6400,
    bchksSparseTotalCover6400]
lemma bchksSparse_fieldBudget6400 :
    bchksSparseTotalCover6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksSparseTotalCover6400 =
        12960975469502531 ∧
      2 ^ (128 : ℕ) *
          (bchksSparseTotalCover6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksSparseTotalCover6400, bchksWeightedNumerator6400,
    bchksListBound6400]
lemma bchksSparse_degree17_noGo6400 :
    bchksWeightedNumerator6400 < 295172250830397597 := by
  norm_num [bchksWeightedNumerator6400]
end ProximityPrize.SubmissionLower
