import ProximityPrize.SubmissionLower.BCHKSParameters6400

namespace ProximityPrize.SubmissionLower

/-!
Exact arithmetic for the specialization-stable factor-cover experiment.

The interpolation parameters in this file are a genuine feasible uniform
Guruswami--Sudan point at agreement `185364`: `DX = m * 185364`, and the
coefficient space is strictly larger than the uniform multiplicity constraint
space.  They were selected to minimize the *conditional* stable-cover ledger
rather than the universal Hensel-resultant ledger.

The final cover estimate is intentionally only arithmetic.  It becomes
applicable if every selected outer-factor slice can be divided into

* pure slices, where the received affine value is the only specialized root;
* nonroot slices, whose agreement incidences can be charged to roots in `Z`.

Generic factorization does not imply that dichotomy: a slice can contain the
received linear factor together with other roots.  The companion certificate
file keeps that missing mixed-slice theorem explicit.
-/

def bchksStableMultiplicity6400 : ℕ := 48516
def bchksStableXCap6400 : ℕ := 8993119824
def bchksStableYCap6400 : ℕ := 68613
def bchksStableZCap6400 : ℕ := 1786469529

def bchksStableVariableCount6400 : ℕ :=
  551163607685668446795724

def bchksStableConstraintCount6400 : ℕ :=
  551163607685668343382016

def bchksStableDimensionSlack6400 : ℕ := 103413708

/-- At most this many positive-`Y` factors can occur. -/
def bchksStableFactorCount6400 : ℕ := 68612

/-- Sum of the available `Z` root mass, using strict cap conventions. -/
def bchksStableRootMass6400 : ℕ := 1786469528

/-- Agreements left after removing at most `K-1=131071` pure coordinates. -/
def bchksStableChargeGap6400 : ℕ := 54293

/-- A nonaligned affine-line fibre has at most `errors+1` challenges. -/
def bchksStableFiberCap6400 : ℕ := 76781

/-- Safe ceiling for the number of challenges chargeable to nonzero
coordinate polynomials. -/
def bchksStableChargedChallengeCap6400 : ℕ := 8625647284

/-- Conditional total challenge cap: pure-factor fibres plus root charges. -/
def bchksStableCoverCap6400 : ℕ := 13893745256

lemma bchksStableXCap_eq6400 :
    bchksStableXCap6400 =
      bchksStableMultiplicity6400 * 185364 := by
  norm_num [bchksStableXCap6400, bchksStableMultiplicity6400]

/-- Closed-form value of the interpolation coefficient count.  This is the
sum `Σ(j<DY) (DX-131071*j)(DZ-j)`, evaluated without expanding a
sixty-eight-thousand-term sum in the kernel. -/
lemma bchksStableVariableCount_formula6400 :
    6 * bchksStableVariableCount6400 =
      bchksStableYCap6400 *
        (6 * bchksStableXCap6400 * bchksStableZCap6400 -
          3 * (bchksStableXCap6400 +
            131071 * bchksStableZCap6400) *
              (bchksStableYCap6400 - 1) +
          131071 * (bchksStableYCap6400 - 1) *
            (2 * bchksStableYCap6400 - 1)) := by
  norm_num [bchksStableVariableCount6400, bchksStableYCap6400,
    bchksStableXCap6400, bchksStableZCap6400]

/-- Closed-form value of the uniform order-`m` interpolation constraints. -/
lemma bchksStableConstraintCount_formula6400 :
    6 * bchksStableConstraintCount6400 =
      262144 * bchksStableMultiplicity6400 *
        (6 * bchksStableMultiplicity6400 * bchksStableZCap6400 -
          3 * (bchksStableMultiplicity6400 + bchksStableZCap6400) *
            (bchksStableMultiplicity6400 - 1) +
          (bchksStableMultiplicity6400 - 1) *
            (2 * bchksStableMultiplicity6400 - 1)) := by
  norm_num [bchksStableConstraintCount6400,
    bchksStableMultiplicity6400, bchksStableZCap6400]

lemma bchksStableInterpolationFeasible6400 :
    bchksStableConstraintCount6400 < bchksStableVariableCount6400 := by
  norm_num [bchksStableConstraintCount6400, bchksStableVariableCount6400]

lemma bchksStableDimensionSlack_eq6400 :
    bchksStableConstraintCount6400 + bchksStableDimensionSlack6400 =
      bchksStableVariableCount6400 := by
  norm_num [bchksStableConstraintCount6400, bchksStableDimensionSlack6400,
    bchksStableVariableCount6400]

lemma bchksStableFactorCount_eq6400 :
    bchksStableFactorCount6400 = bchksStableYCap6400 - 1 := by
  norm_num [bchksStableFactorCount6400, bchksStableYCap6400]

lemma bchksStableRootMass_eq6400 :
    bchksStableRootMass6400 = bchksStableZCap6400 - 1 := by
  norm_num [bchksStableRootMass6400, bchksStableZCap6400]

lemma bchksStableChargeGap_eq6400 :
    bchksStableChargeGap6400 = 185364 - 131071 := by
  norm_num [bchksStableChargeGap6400]

lemma bchksStableFiberCap_eq6400 :
    bchksStableFiberCap6400 = bchksErrors6400 + 1 := by
  norm_num [bchksStableFiberCap6400, bchksErrors6400]

/-- The safe charged-challenge cap is the ceiling of total root mass divided
by the per-challenge gap. -/
lemma bchksStableChargedChallengeCap_eq6400 :
    bchksStableChargedChallengeCap6400 =
      (262144 * bchksStableRootMass6400 +
          bchksStableChargeGap6400 - 1) /
        bchksStableChargeGap6400 := by
  norm_num [bchksStableChargedChallengeCap6400,
    bchksStableRootMass6400, bchksStableChargeGap6400]

lemma bchksStableCoverCap_eq6400 :
    bchksStableCoverCap6400 =
      bchksStableFactorCount6400 * bchksStableFiberCap6400 +
        bchksStableChargedChallengeCap6400 := by
  norm_num [bchksStableCoverCap6400, bchksStableFactorCount6400,
    bchksStableFiberCap6400, bchksStableChargedChallengeCap6400]

/-- If the missing stable-cover theorem is supplied, its entire challenge
cap is tiny compared with the existing `10^17` numerator. -/
lemma bchksStableCoverCap_lt_numerator6400 :
    bchksStableCoverCap6400 < bchksNumerator6400 := by
  norm_num [bchksStableCoverCap6400, bchksNumerator6400]

lemma bchksStableCoverFieldBudget6400 :
    2 ^ (128 : ℕ) *
        (bchksStableCoverCap6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksStableCoverCap6400, bchksListBound6400]

end ProximityPrize.SubmissionLower
