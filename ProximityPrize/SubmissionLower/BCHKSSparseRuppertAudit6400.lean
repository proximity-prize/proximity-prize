import ProximityPrize.SubmissionLower.BCHKSDeepHigherDegreeAudit6400
import ProximityPrize.SubmissionLower.BCHKSWeightedSecant6400

namespace ProximityPrize.SubmissionLower

/-!
Arithmetic audit for a sparse Ruppert/Gao rank-drop cover.

The point is deliberately shallower than the j16 interpolant.  One
`Y`-derivative is enough for the global-radical bridge to force every
uncharged owner factor to have exponent at least two.  The resulting field
headroom pays for a sparse reducibility minor through factor `Y` degree 16.

What is compiled here is the exact interpolation, repair, characteristic,
lattice-column, and field ledger.  The remaining algebraic implementation
is a sparse PDE rank-drop theorem: a specialization acquiring a polynomial
linear factor must lower the generic Ruppert/Gao rank.  Generic geometric
line-orbit factors require the separate weighted-secant branch.
-/

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

/-- With exponent at least two, the failed hybrid repair and
`t <= (d-1)n` give the uniform degree-16 weight cap. -/
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

/-- Exact lattice count and sparse Ruppert source-column count for the
triangle `x+131071*y <= 4183700`, `0<=y<=16`. -/
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

/-- The rectangular Gao characteristic condition is tiny compared with the
KoalaBear characteristic.  This replaces the unusable total-degree-square
hypothesis in the published sparse-pencil theorem. -/
lemma bchksSparse_gaoCharacteristic6400 :
    (2 * bchksSparseDegreeCap6400 - 1) *
        bchksSparseWeightCap6400 < 2130706433 := by
  norm_num [bchksSparseDegreeCap6400, bchksSparseWeightCap6400]

/-- The degree-16 column count dominates every lower degree at the common
weight cap.  `C` is written by its division-free lattice formula. -/
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

/-- The next degree misses this exact optimized sparse-minor ledger.  This is
a technique no-go, not an impossibility theorem for degree seventeen. -/
lemma bchksSparse_degree17_noGo6400 :
    bchksWeightedNumerator6400 < 295172250830397597 := by
  norm_num [bchksWeightedNumerator6400]

end ProximityPrize.SubmissionLower
