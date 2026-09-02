/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Transfer gates from the accepted lower 67.77 development

The accepted `67.76 -> 67.77` lower change introduced a characteristic-free
incidence argument for a component that is linear in the residual `R`
coordinate.  After eliminating `R`, its bivariate resultant cost is

`fY * (bZ + bR * gZ) + fZ * (bY + bR * gY)`.

In particular, this route does not require the former mixed-degree gate
`2 * implicitY * algebraic < p`.  That distinction is numerically essential:
the old residual profile passed the gate by `16,490,063`, while the accepted
67.77 residual profile fails it by `106,376,317`.

For an upper attack this closes a tempting false loophole.  Merely crossing
the characteristic with a mixed degree does not evade the lower incidence
geometry when the carrier is regular and linear in `R`.  A prospective attack
must instead force the resultant-identity/affine-pencil branch, lose
regularity, or leave the linear-`R` model.

The same accepted change added an eighth quotient stage and a role-separated
long helper kernel.  The arithmetic below records their exact scale.  It does
not import the lower proof and is not an upper score certificate.
-/

namespace ProximityPrize.SubmissionUpper.Accepted6777LinearRGate

def fieldCharacteristic : ℕ := 2130706433
def rowDegree : ℕ := 131071

def oldResidualSlope : ℕ := 23
def oldResidualWeighted : ℕ := 13985356
def oldResidualLength : ℕ := 4893

def newResidualSlope : ℕ := 23
def newResidualWeighted : ℕ := 14347822
def newResidualLength : ℕ := 5047

def implicitY (s weighted : ℕ) : ℕ := ((2 * s - 1) * weighted - 1) / rowDegree
def algebraicZ (s length : ℕ) : ℕ := (2 * s - 1) * length
def oldMixedGateValue : ℕ :=
  2 * implicitY oldResidualSlope oldResidualWeighted *
    algebraicZ oldResidualSlope oldResidualLength
def newMixedGateValue : ℕ :=
  2 * implicitY newResidualSlope newResidualWeighted *
    algebraicZ newResidualSlope newResidualLength

/-- The characteristic gate crossed between the two accepted profiles. -/
theorem mixed_characteristic_transition_receipt :
    implicitY oldResidualSlope oldResidualWeighted = 4801 ∧
      algebraicZ oldResidualSlope oldResidualLength = 220185 ∧
      oldMixedGateValue = 2114216370 ∧
      fieldCharacteristic - oldMixedGateValue = 16490063 ∧
      implicitY newResidualSlope newResidualWeighted = 4925 ∧
      algebraicZ newResidualSlope newResidualLength = 227115 ∧
      newMixedGateValue = 2237082750 ∧
      newMixedGateValue - fieldCharacteristic = 106376317 := by
  norm_num [implicitY, algebraicZ, oldMixedGateValue, newMixedGateValue,
    oldResidualSlope, oldResidualWeighted, oldResidualLength,
    newResidualSlope, newResidualWeighted, newResidualLength,
    rowDegree, fieldCharacteristic]

/-- Exact regrouping of the bivariate cost after eliminating a linear `R`
component.  No characteristic parameter occurs in this identity. -/
def linearRResultantCost
    (fY fZ gY gZ bY bR bZ : ℕ) : ℕ :=
  fY * (bZ + bR * gZ) + fZ * (bY + bR * gY)

theorem linearR_resultant_cost_regroup
    (fY fZ gY gZ bY bR bZ : ℕ) :
    linearRResultantCost fY fZ gY gZ bY bR bZ =
      bY * fZ + bR * (fY * gZ + fZ * gY) + bZ * fY := by
  simp only [linearRResultantCost]
  ring

def sourceCShortRankGap : ℕ := 646245243669294
def sourceCLongRankGap : ℕ := 1296392225018202
def sourceCMultiplicity : ℕ := 241
def eighthFactorial : ℕ := 40320

/-- The long helper's certified coefficient-count/rank gap is just over twice
the short Source-C gap.  It is paid only in the factor-switch fallback, rather
than throughout the grid. -/
theorem long_helper_scale_receipt :
    2 * sourceCShortRankGap < sourceCLongRankGap ∧
      sourceCLongRankGap - 2 * sourceCShortRankGap = 3901737679614 ∧
      8 < sourceCMultiplicity ∧
      eighthFactorial < fieldCharacteristic := by
  norm_num [sourceCShortRankGap, sourceCLongRankGap, sourceCMultiplicity,
    eighthFactorial, fieldCharacteristic]

def oldAgreement : ℕ := 181628
def newAgreement : ℕ := 181618
def oldRadiusNumerator : ℕ := 10306082
def newRadiusNumerator : ℕ := 10307341
def challengeThreshold : ℕ := 274980728111395088
def newAlignmentBudget : ℕ := 274980725868189680
def newListBudget : ℕ := 2243205407

theorem accepted_score_delta_receipt :
    oldAgreement - newAgreement = 10 ∧
      newRadiusNumerator - oldRadiusNumerator = 1259 ∧
      newAlignmentBudget + newListBudget + 1 = challengeThreshold := by
  norm_num [oldAgreement, newAgreement, oldRadiusNumerator,
    newRadiusNumerator, newAlignmentBudget, newListBudget,
    challengeThreshold]

#print axioms mixed_characteristic_transition_receipt
#print axioms linearR_resultant_cost_regroup
#print axioms long_helper_scale_receipt
#print axioms accepted_score_delta_receipt

end ProximityPrize.SubmissionUpper.Accepted6777LinearRGate
