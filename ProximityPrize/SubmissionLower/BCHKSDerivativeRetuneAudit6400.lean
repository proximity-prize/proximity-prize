import ProximityPrize.SubmissionLower.BCHKSDerivativeLowering6400
import ProximityPrize.SubmissionLower.BCHKSStableParameters6400

namespace ProximityPrize.SubmissionLower

/-!
Exact arithmetic for a one-step derivative-lowering buffer.

The interpolant starts with an `(X+kY)` cap exactly `87382` below the root
budget.  One application of the sharp-line derivative transform can therefore
increase the cap by `87382` and still remain at the `m*a` root threshold.

This file does **not** claim that a minimal interpolant has the required
margin after repeated transformations.  It isolates the strongest sound
one-step parameter point and the remaining selection barrier.
-/

def bchksDerivativeMultiplicity6400 : ℕ := 204660
def bchksDerivativeXSmallCap6400 : ℕ := 37936508858
def bchksDerivativeYCap6400 : ℕ := 289435
def bchksDerivativeZCap6400 : ℕ := 7537729905

def bchksDerivativeVariableCount6400 : ℕ :=
  41382300391667053678045550

def bchksDerivativeConstraintCount6400 : ℕ :=
  41382300391667035212349440

def bchksDerivativeDimensionSlack6400 : ℕ := 18465696110
def bchksDerivativeConditionalCover6400 : ℕ := 58617607092

lemma bchksDerivative_exact_margin6400 :
    bchksDerivativeXSmallCap6400 + 87382 =
      bchksDerivativeMultiplicity6400 * 185364 := by
  norm_num [bchksDerivativeXSmallCap6400,
    bchksDerivativeMultiplicity6400]

lemma bchksDerivativeVariableCount_formula6400 :
    6 * bchksDerivativeVariableCount6400 =
      bchksDerivativeYCap6400 *
        (6 * bchksDerivativeXSmallCap6400 * bchksDerivativeZCap6400 -
          3 * (bchksDerivativeXSmallCap6400 +
            131071 * bchksDerivativeZCap6400) *
              (bchksDerivativeYCap6400 - 1) +
          131071 * (bchksDerivativeYCap6400 - 1) *
            (2 * bchksDerivativeYCap6400 - 1)) := by
  norm_num [bchksDerivativeVariableCount6400,
    bchksDerivativeYCap6400, bchksDerivativeXSmallCap6400,
    bchksDerivativeZCap6400]

lemma bchksDerivativeConstraintCount_formula6400 :
    6 * bchksDerivativeConstraintCount6400 =
      262144 * bchksDerivativeMultiplicity6400 *
        (6 * bchksDerivativeMultiplicity6400 * bchksDerivativeZCap6400 -
          3 * (bchksDerivativeMultiplicity6400 +
            bchksDerivativeZCap6400) *
              (bchksDerivativeMultiplicity6400 - 1) +
          (bchksDerivativeMultiplicity6400 - 1) *
            (2 * bchksDerivativeMultiplicity6400 - 1)) := by
  norm_num [bchksDerivativeConstraintCount6400,
    bchksDerivativeMultiplicity6400, bchksDerivativeZCap6400]

lemma bchksDerivativeInterpolationFeasible6400 :
    bchksDerivativeConstraintCount6400 <
      bchksDerivativeVariableCount6400 := by
  norm_num [bchksDerivativeConstraintCount6400,
    bchksDerivativeVariableCount6400]

lemma bchksDerivativeDimensionSlack_eq6400 :
    bchksDerivativeConstraintCount6400 +
        bchksDerivativeDimensionSlack6400 =
      bchksDerivativeVariableCount6400 := by
  norm_num [bchksDerivativeConstraintCount6400,
    bchksDerivativeDimensionSlack6400,
    bchksDerivativeVariableCount6400]

lemma bchksDerivativeConditionalCover_eq6400 :
    bchksDerivativeConditionalCover6400 =
      (bchksDerivativeYCap6400 - 1) * bchksStableFiberCap6400 +
        (262144 * (bchksDerivativeZCap6400 - 1) +
          bchksStableChargeGap6400 - 1) / bchksStableChargeGap6400 := by
  norm_num [bchksDerivativeConditionalCover6400,
    bchksDerivativeYCap6400, bchksDerivativeZCap6400,
    bchksStableFiberCap6400, bchksStableChargeGap6400]

lemma bchksDerivativeConditionalCover_lt_numerator6400 :
    bchksDerivativeConditionalCover6400 < bchksNumerator6400 := by
  norm_num [bchksDerivativeConditionalCover6400, bchksNumerator6400]

lemma bchksDerivativeFieldBudget6400 :
    2 ^ (128 : ℕ) *
        (bchksDerivativeConditionalCover6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksDerivativeConditionalCover6400, bchksListBound6400]

/-- Globally charging the line increment to every `Y` degree changes the
effective `Y` weight from `k` to `k+87382=218453`, which lies on the wrong
side of the Johnson quadratic.  Thus that coarse selection rule cannot be
the missing argument. -/
lemma bchksDerivative_effectiveWeight_asymptotic_noGo6400 :
    185364 ^ 2 < 262144 * (131071 + 87382) := by norm_num

end ProximityPrize.SubmissionLower
