import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research

/-!
# Numerical residual stages for the stacked 67.30 profile

This module specializes the accepted unequal-regular and tight-singular
arithmetic APIs to the two residual pairs at `a = 182078`.  The first stage is
oriented with profile B as its singular pivot; the second uses the A/B GCD box
as pivot.  It proves only numerical caps and generic stage-composition
wrappers.  No seed-cell geometry is asserted.
-/

namespace ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6670Research

open scoped BigOperators
open ContactParameters6600Research
open ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def prime : ℕ := 2130706433

/-- First residual pair, oriented with profile B as the singular pivot and
profile A as the external proper cut. -/
def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 181878, 83, 18, 3100, 69, 15, 25000⟩

/-- Second residual pair, oriented with the A/B GCD box as singular pivot and
profile C as the external proper cut. -/
def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 181878, 69, 15, 3100, 69, 15, 800000⟩

/-- Tight singular ledger for the profile-B pivot. -/
def pivotB : TightParameters :=
  ⟨262144, 131071, 181878, 10912680, 3100, 18⟩

/-- Tight singular ledger for the A/B GCD pivot. -/
def pivotGcd12 : TightParameters :=
  ⟨262144, 131071, 181878, 9093900, 3100, 15⟩

def firstResidualSingularCeiling : ℕ := 641479726848507
def secondResidualSingularCeiling : ℕ := 366990261075598

theorem residual_stage_values :
    residualStageOne.agreement = ⟨21757787, 4587485, 6553550001⟩ ∧
      residualStageOne.mixedCost = ⟨496500, 2288900, 2487⟩ ∧
      residualStageOne.regularNumerator = 4928579668855395954 ∧
      residualStageOne.regularCountCap = 97005917862802 ∧
      residualStageTwo.agreement = ⟨18087799, 3801059, 209713600001⟩ ∧
      residualStageTwo.mixedCost = ⟨6408100, 55237260, 1587⟩ ∧
      residualStageTwo.regularNumerator = 86335693385787379674 ∧
      residualStageTwo.regularCountCap = 1699287369570873 := by
  norm_num [residualStageOne, residualStageTwo,
    UnequalParameters.agreement, UnequalParameters.leftAgreement,
    UnequalParameters.rightAgreement, UnequalParameters.mixedCost,
    UnequalParameters.regularCountCap, UnequalParameters.regularNumerator,
    UnequalParameters.errors, UnequalParameters.gap, dot]

theorem pivot_implicit_values :
    pivotB.kappa = 35 ∧
      pivotB.implicitYCap = 2914 ∧
      pivotB.algebraicCap = 108500 ∧
      pivotB.tightNumerator = 32591660481992045888 ∧
      pivotB.countCap = 641479726848506 ∧
      pivotGcd12.kappa = 29 ∧
      pivotGcd12.implicitYCap = 2012 ∧
      pivotGcd12.algebraicCap = 89900 ∧
      pivotGcd12.tightNumerator = 18645674194467887604 ∧
      pivotGcd12.countCap = 366990261075597 := by
  norm_num [pivotB, pivotGcd12, TightParameters.countCap,
    TightParameters.tightNumerator, TightParameters.coreNumerator,
    TightParameters.aggregateCost, TightParameters.agreement,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.kappa, TightParameters.errors, TightParameters.gap, dot]

/-- The strict singular ceilings are exactly one above the tight count caps. -/
theorem residual_singular_ceilings :
    pivotB.countCap + 1 = firstResidualSingularCeiling ∧
      pivotGcd12.countCap + 1 = secondResidualSingularCeiling := by
  rw [pivot_implicit_values.2.2.2.2.1, pivot_implicit_values.2.2.2.2.2.2.2.2.2]
  norm_num [firstResidualSingularCeiling, secondResidualSingularCeiling]

/-- Numerical compatibility of each tight pivot with the left box of its
oriented unequal stage, together with the common positive gap. -/
theorem pivot_projection_gates :
    0 < residualStageOne.gap ∧ pivotB.gap = residualStageOne.gap ∧
      (pivotB.D - 1) / pivotB.w ≤ residualStageOne.leftY ∧
      pivotB.s ≤ residualStageOne.leftR ∧
      pivotB.L ≤ residualStageOne.leftZ ∧
    0 < residualStageTwo.gap ∧ pivotGcd12.gap = residualStageTwo.gap ∧
      (pivotGcd12.D - 1) / pivotGcd12.w ≤ residualStageTwo.leftY ∧
      pivotGcd12.s ≤ residualStageTwo.leftR ∧
      pivotGcd12.L ≤ residualStageTwo.leftZ := by
  norm_num [residualStageOne, residualStageTwo, pivotB, pivotGcd12,
    UnequalParameters.gap, TightParameters.gap]

theorem pivot_characteristic_gates :
    1 ≤ pivotB.s ∧ pivotB.s < prime ∧
      1 ≤ pivotB.w ∧ pivotB.w < prime ∧
      pivotB.w < pivotB.kappa * pivotB.D ∧
      pivotB.kappa * pivotB.D < prime ∧
      1 ≤ pivotB.algebraicCap ∧
      pivotB.algebraicCap < prime ∧
      pivotB.implicitYCap < prime ∧
      2 * pivotB.implicitYCap * pivotB.algebraicCap < prime ∧
      pivotB.w < pivotB.a ∧
      pivotB.a ≤ pivotB.n ∧
    1 ≤ pivotGcd12.s ∧ pivotGcd12.s < prime ∧
      1 ≤ pivotGcd12.w ∧ pivotGcd12.w < prime ∧
      pivotGcd12.w < pivotGcd12.kappa * pivotGcd12.D ∧
      pivotGcd12.kappa * pivotGcd12.D < prime ∧
      1 ≤ pivotGcd12.algebraicCap ∧
      pivotGcd12.algebraicCap < prime ∧
      pivotGcd12.implicitYCap < prime ∧
      2 * pivotGcd12.implicitYCap * pivotGcd12.algebraicCap < prime ∧
      pivotGcd12.w < pivotGcd12.a ∧
      pivotGcd12.a ≤ pivotGcd12.n := by
  norm_num [pivotB, pivotGcd12, prime, TightParameters.kappa,
    TightParameters.implicitYCap, TightParameters.algebraicCap]

end ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6670Research
