import ProximityPrize.SubmissionLower.BCHKSSeedCurveBoostNoGo6401

/-!
# Degree-three spherical arithmetic at 76,855 errors

The source-faithful curve boost from the score-6401 radius asks for scalar
list decoding at the slightly inflated radius `delta*b/(b-1)`.  With
`b=1183`, this radius permits 76,855 errors.  The same rational degree-three
spherical certificate remains valid there and gives the list cap
`5,300,631,529`.

All numerical hypotheses of that wider spherical certificate and its boost
ledger fit.  What is not supplied is the genuinely new weak curve-decoding
seed at the *target* radius with output 1,183; the known unconditional seed
is at the smaller score-63.99 radius.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSSphericalL3Radius76855Audit6401

open ProximityPrize.Benchmark
open scoped NNReal

def wideSphereN : ℕ := 262144
def wideSphereDim : ℕ := wideSphereN - 1
def wideSphereErrors : ℕ := 76855
def wideSphereAgreements : ℕ := wideSphereN - wideSphereErrors
def wideSphereK : ℕ := 131071

def wideMaxInner : ℚ :=
  (wideSphereN * wideSphereK - wideSphereAgreements ^ 2 : ℕ) /
    (wideSphereAgreements * wideSphereErrors : ℕ)

def wideLevenRoot : ℚ :=
  -(1 + wideMaxInner) / (1 + wideSphereDim * wideMaxInner)

def wideGegen0 : ℚ :=
  -(wideMaxInner + 2 * wideLevenRoot) / wideSphereDim -
    wideMaxInner * wideLevenRoot ^ 2
def wideGegen1 : ℚ :=
  3 / (wideSphereDim + 2) +
    2 * wideMaxInner * wideLevenRoot + wideLevenRoot ^ 2
def wideGegen2 : ℚ :=
  -(wideMaxInner + 2 * wideLevenRoot) *
    (wideSphereDim - 1) / wideSphereDim
def wideGegen3 : ℚ :=
  (wideSphereDim - 1) / (wideSphereDim + 2)

def wideLevenRatio : ℚ :=
  wideSphereDim * (1 - wideMaxInner) *
      (2 + (wideSphereDim + 1) * wideMaxInner) /
    (1 - wideSphereDim * wideMaxInner ^ 2)

def wideListBound : ℕ := 5300631529
def targetSeedOutput : ℕ := 1183

noncomputable def inflatedTargetListRadius : ℝ≥0 :=
  bchksRadius6401 * targetSeedOutput / (targetSeedOutput - 1)

/-- Exact rational data for the wider spherical code. -/
theorem wideSphere_exactParameters :
    wideSphereDim = 262143 ∧
    wideSphereAgreements = 185289 ∧
    wideMaxInner = 27462703 / 14240386095 ∧
    wideLevenRoot = -7133924399 / 3606697869312 ∧
    wideLevenRatio =
      78739654429757002464362496 / 14854768530131939 := by
  norm_num [wideSphereDim, wideSphereN, wideSphereAgreements,
    wideSphereErrors, wideMaxInner, wideSphereK, wideLevenRoot,
    wideLevenRatio]

/-- These are exactly the interval and positive-Gegenbauer conditions used
by the degree-three LP proof. -/
theorem wideSphere_L3_hypotheses :
    0 < wideMaxInner ∧ wideMaxInner < 1 ∧
    0 < 1 - wideSphereDim * wideMaxInner ^ 2 ∧
    wideLevenRoot < -(wideMaxInner / 2) ∧
    0 < wideGegen0 ∧ 0 < wideGegen1 ∧
    0 < wideGegen2 ∧ 0 < wideGegen3 := by
  norm_num [wideSphereDim, wideSphereN, wideSphereAgreements,
    wideSphereErrors, wideMaxInner, wideSphereK, wideLevenRoot,
    wideGegen0, wideGegen1, wideGegen2, wideGegen3]

/-- The strict rational comparison yields the integer cap 5,300,631,529. -/
theorem wideSphere_L3_ratio_cap :
    wideLevenRatio < wideListBound + 1 := by
  norm_num [wideLevenRatio, wideListBound, wideSphereDim, wideSphereN,
    wideSphereAgreements, wideSphereErrors, wideMaxInner, wideSphereK]

/-- With output `1183`, the target-radius boost asks for a list theorem in
the 76,855-error Hamming cell. -/
theorem inflatedTargetListRadius_floor :
    ⌊inflatedTargetListRadius *
        (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ = wideSphereErrors := by
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [← NNReal.coe_le_coe]
    norm_num [inflatedTargetListRadius, targetSeedOutput,
      bchksRadius6401, IRSProfile.Index, wideSphereErrors,
      div_eq_mul_inv]
  · rw [← NNReal.coe_lt_coe]
    norm_num [inflatedTargetListRadius, targetSeedOutput,
      bchksRadius6401, IRSProfile.Index, wideSphereErrors,
      div_eq_mul_inv]

/-- The spherical list charge is tiny relative to the field numerator.  A
target-radius seed may consume the displayed remainder and the full boosted
ledger still fits. -/
theorem wideSphere_boostLedger :
    (wideListBound + 1) ^ 2 < (2130706433 : ℕ) ^ 6 ∧
    262144 * wideListBound = 1389528751538176 ∧
    274980728111395087 - (262144 + 1) * wideListBound =
      273591194059225382 ∧
    (262144 + 1) * wideListBound + 273591194059225382 =
      274980728111395087 := by
  norm_num [wideListBound]

/-- The desired seed output is far smaller than the known 63.99 output, but
radius monotonicity goes in the wrong direction: weakening the output does
not upgrade the seed radius. -/
theorem targetSeedOutput_small_but_radiusGap :
    targetSeedOutput ≤
        BCHKSSeedCurveBoostNoGo6401.weakCurveOutput6401 ∧
    bchksRadius6399 < bchksRadius6401 := by
  norm_num [targetSeedOutput,
    BCHKSSeedCurveBoostNoGo6401.weakCurveOutput6401,
    bchksRadius6399, bchksRadius6401]

end BCHKSSphericalL3Radius76855Audit6401
end ProximityPrize.SubmissionLower
