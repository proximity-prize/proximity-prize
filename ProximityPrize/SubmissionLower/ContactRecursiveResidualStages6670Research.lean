import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research

/-!
# Numerical residual stages for the stacked 67.40 profile

This module specializes the accepted unequal-regular and tight-singular
arithmetic APIs to the two residual pairs at `a = 181982`.  The first stage is
oriented with profile B as its singular pivot; the second uses the A/B GCD box
as pivot.  It proves only numerical caps and generic stage-composition
wrappers.  No seed-cell geometry is asserted.
-/

namespace ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6670Research

open scoped BigOperators
open ContactNearPencil6600ArithmeticResearch
open ContactSingularLedger6600Research
open ContactTightSingularLedgerResearch
open ContactAsymmetricResidualStageResearch
open ContactRecursiveResidualStages6656Research

set_option maxHeartbeats 2000000

def n : ℕ := 262144
def w : ℕ := 131071
def agreements : ℕ := 181982
def errors : ℕ := 80162
def gap : ℕ := 50911

/-- Stage 1 unequal regular parameters: quotient B vs quotient A. -/
def residualStageOne : UnequalStageParameters where
  n := 262144
  w := 131071
  errors := 80162
  gap := 50911
  leftY := 105
  leftR := 23
  leftZ := 1450
  rightY := 62
  rightR := 14
  rightZ := 20000

/-- Singular pivot for residual cell 1: profile B. -/
def pivotB : TightParameters where
  n := 262144
  w := 131071
  a := 181982
  D := 13830632
  L := 1450
  s := 23

/-- Stage 2 unequal regular parameters: quotient GCD12 vs quotient C. -/
def residualStageTwo : UnequalStageParameters where
  n := 262144
  w := 131071
  errors := 80162
  gap := 50911
  leftY := 62
  leftR := 9
  leftZ := 900
  rightY := 62
  rightR := 14
  rightZ := 50000

/-- Singular pivot for residual cell 2: meet box GCD12. -/
def pivotGcd12 : TightParameters where
  n := 262144
  w := 131071
  a := 181982
  D := 8189190
  L := 900
  s := 9

def firstResidualSingularCeiling : ℕ :=
  pivotB.tightNumerator / pivotB.gap ^ 2 + 1

def secondResidualSingularCeiling : ℕ :=
  pivotGcd12.tightNumerator / pivotGcd12.gap ^ 2 + 1

theorem residual_stage_one_values :
    residualStageOne.stageAgreement = ⟨27524911, 5898195, 5242840001⟩ ∧
      residualStageOne.mixedCost = ⟨480300, 2189900, 2896⟩ ∧
      residualStageOne.regularNumerator = 5415939872563840536 ∧
      residualStageOne.regularCountCap = 106380543940677 := by
  norm_num [residualStageOne, UnequalStageParameters.stageAgreement,
    UnequalStageParameters.mixedCost, UnequalStageParameters.regularNumerator,
    UnequalStageParameters.regularCountCap, dot]

theorem pivot_B_values :
    pivotB.errors = 80162 ∧
      pivotB.gap = 50911 ∧
      pivotB.kappa = 45 ∧
      pivotB.implicitYCap = 4748 ∧
      pivotB.algebraicCap = 65250 ∧
      pivotB.agreement = ⟨1244650217, 131071, 17104765501⟩ ∧
      pivotB.aggregateCost = ⟨65250, 619614000, 4748⟩ ∧
      pivotB.coreNumerator = 31934681778476418618 ∧
      pivotB.tightNumerator = 31935115292005293618 ∧
      pivotB.countCap = 627273384769603 := by
  norm_num [pivotB, TightParameters.errors, TightParameters.gap,
    TightParameters.kappa, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.agreement,
    TightParameters.aggregateCost, TightParameters.coreNumerator,
    TightParameters.tightNumerator, TightParameters.countCap, dot]

theorem residual_stage_two_values :
    residualStageTwo.stageAgreement = ⟨16252805, 3538917, 13107100001⟩ ∧
      residualStageTwo.mixedCost = ⟨462600, 3155800, 1426⟩ ∧
      residualStageTwo.regularNumerator = 4899171995628737916 ∧
      residualStageTwo.regularCountCap = 96230126998659 := by
  norm_num [residualStageTwo, UnequalStageParameters.stageAgreement,
    UnequalStageParameters.mixedCost, UnequalStageParameters.regularNumerator,
    UnequalStageParameters.regularCountCap, dot]

theorem pivot_Gcd12_values :
    pivotGcd12.errors = 80162 ∧
      pivotGcd12.gap = 50911 ∧
      pivotGcd12.kappa = 17 ∧
      pivotGcd12.implicitYCap = 1062 ∧
      pivotGcd12.algebraicCap = 15300 ∧
      pivotGcd12.agreement = ⟨278394805, 131071, 4010772601⟩ ∧
      pivotGcd12.aggregateCost = ⟨15300, 32497200, 1062⟩ ∧
      pivotGcd12.coreNumerator = 1674897270797538792 ∧
      pivotGcd12.tightNumerator = 1674921106309518792 ∧
      pivotGcd12.countCap = 32899002304207 := by
  norm_num [pivotGcd12, TightParameters.errors, TightParameters.gap,
    TightParameters.kappa, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.agreement,
    TightParameters.aggregateCost, TightParameters.coreNumerator,
    TightParameters.tightNumerator, TightParameters.countCap, dot]

theorem firstResidualSingularCeiling_exact :
    firstResidualSingularCeiling = 627273384769604 := by
  norm_num [firstResidualSingularCeiling, pivotB,
    TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap, dot]

theorem secondResidualSingularCeiling_exact :
    secondResidualSingularCeiling = 32899002304208 := by
  norm_num [secondResidualSingularCeiling, pivotGcd12,
    TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap, dot]

end ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6670Research
