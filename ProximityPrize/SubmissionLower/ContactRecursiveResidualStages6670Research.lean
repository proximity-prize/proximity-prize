import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research

/-!
# Numerical residual stages for the stacked 67.10 profile

This module specializes the accepted unequal-regular and tight-singular
arithmetic APIs to the two residual pairs at `a = 182278`.  The first stage is
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
  ⟨262144, 131071, 182268, 94, 21, 900, 48, 10, 20000⟩

/-- Second residual pair, oriented with the A/B GCD box as singular pivot and
profile C as the external proper cut. -/
def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 182268, 48, 10, 900, 52, 10, 42000⟩

/-- Tight singular ledger for the profile-B pivot. -/
def pivotB : TightParameters :=
  ⟨262144, 131071, 182268, 12394224, 900, 21⟩

/-- Tight singular ledger for the A/B GCD pivot. -/
def pivotGcd12 : TightParameters :=
  ⟨262144, 131071, 182268, 6379380, 900, 10⟩

def firstResidualSingularCeiling : ℕ := 288040349938195
def secondResidualSingularCeiling : ℕ := 31812929513254

theorem residual_stage_values :
    residualStageOne.agreement = ⟨24641349, 5373911, 5242840001⟩ ∧
      residualStageOne.mixedCost = ⟨52200, 1923200, 5452⟩ ∧
      residualStageOne.regularNumerator = 5269857839873135584 ∧
      residualStageOne.regularCountCap = 2010526830 ∧
      residualStageTwo.agreement = ⟨13631385, 2490349, 11009964001⟩ ∧
      residualStageTwo.mixedCost = ⟨55800, 2062800, 2976⟩ ∧
      residualStageTwo.regularNumerator = 5067736861494160392 ∧
      residualStageTwo.regularCountCap = 1933414760 := by
  norm_num [residualStageOne, residualStageTwo,
    UnequalParameters.agreement, UnequalParameters.leftAgreement,
    UnequalParameters.rightAgreement, UnequalParameters.mixedCost,
    UnequalParameters.regularCountCap, UnequalParameters.regularNumerator,
    UnequalParameters.errors, UnequalParameters.gap, dot]

theorem pivot_implicit_values :
    pivotB.kappa = 41 ∧
      pivotB.implicitYCap = 3877 ∧
      pivotB.algebraicCap = 36900 ∧
      pivotB.tightNumerator = 14746801795785766534 ∧
      pivotB.countCap = 288040349938194 ∧
      pivotGcd12.kappa = 19 ∧
      pivotGcd12.implicitYCap = 924 ∧
      pivotGcd12.algebraicCap = 17100 ∧
      pivotGcd12.tightNumerator = 1628726552290037508 ∧
      pivotGcd12.countCap = 31812929513253 := by
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

/-- All characteristic-side gates required by the tight implicit-pair
aggregation for both pivots. -/
theorem pivot_implicit_characteristic_gates :
    1 ≤ pivotB.s ∧ pivotB.s < prime ∧
      1 ≤ pivotB.w ∧ pivotB.w < prime ∧
      pivotB.w < pivotB.kappa * pivotB.D ∧
      pivotB.kappa * pivotB.D < prime ∧
      1 ≤ pivotB.algebraicCap ∧ pivotB.algebraicCap < prime ∧
      pivotB.implicitYCap < prime ∧
      2 * pivotB.implicitYCap * pivotB.algebraicCap < prime ∧
      pivotB.w < pivotB.a ∧ pivotB.a ≤ pivotB.n ∧
    1 ≤ pivotGcd12.s ∧ pivotGcd12.s < prime ∧
      1 ≤ pivotGcd12.w ∧ pivotGcd12.w < prime ∧
      pivotGcd12.w < pivotGcd12.kappa * pivotGcd12.D ∧
      pivotGcd12.kappa * pivotGcd12.D < prime ∧
      1 ≤ pivotGcd12.algebraicCap ∧ pivotGcd12.algebraicCap < prime ∧
      pivotGcd12.implicitYCap < prime ∧
      2 * pivotGcd12.implicitYCap * pivotGcd12.algebraicCap < prime ∧
      pivotGcd12.w < pivotGcd12.a ∧ pivotGcd12.a ≤ pivotGcd12.n := by
  norm_num [pivotB, pivotGcd12, prime, TightParameters.kappa,
    TightParameters.implicitYCap, TightParameters.algebraicCap]

/-- Characteristic gates used by the unequal rectangular projection bounds. -/
theorem residual_projection_characteristic_gates :
    1 ≤ residualStageOne.leftR ∧
      residualStageOne.leftY < prime ∧
      residualStageOne.leftR < prime ∧
      residualStageOne.leftZ < prime ∧
      residualStageOne.rightY < prime ∧
      residualStageOne.rightR < prime ∧
      residualStageOne.rightZ < prime ∧
      residualStageOne.mixedCost.y < prime ∧
      residualStageOne.mixedCost.r < prime ∧
      residualStageOne.mixedCost.z < prime ∧
      1 ≤ residualStageOne.w ∧ residualStageOne.w < prime ∧
      residualStageOne.w < residualStageOne.a ∧
      residualStageOne.a ≤ residualStageOne.n ∧
    1 ≤ residualStageTwo.leftR ∧
      residualStageTwo.leftY < prime ∧
      residualStageTwo.leftR < prime ∧
      residualStageTwo.leftZ < prime ∧
      residualStageTwo.rightY < prime ∧
      residualStageTwo.rightR < prime ∧
      residualStageTwo.rightZ < prime ∧
      residualStageTwo.mixedCost.y < prime ∧
      residualStageTwo.mixedCost.r < prime ∧
      residualStageTwo.mixedCost.z < prime ∧
      1 ≤ residualStageTwo.w ∧ residualStageTwo.w < prime ∧
      residualStageTwo.w < residualStageTwo.a ∧
      residualStageTwo.a ≤ residualStageTwo.n := by
  norm_num [residualStageOne, residualStageTwo, prime,
    UnequalParameters.mixedCost]

theorem residual_stage_ceilings :
    residualStageOne.regularCountCap + pivotB.countCap + 1 =
        2010526830 + firstResidualSingularCeiling ∧
      residualStageTwo.regularCountCap + pivotGcd12.countCap + 1 =
        1933414760 + secondResidualSingularCeiling := by
  rw [residual_stage_values.2.2.2.1,
    residual_stage_values.2.2.2.2.2.2.2,
    pivot_implicit_values.2.2.2.2.1,
    pivot_implicit_values.2.2.2.2.2.2.2.2.2]
  norm_num [firstResidualSingularCeiling, secondResidualSingularCeiling]

/-! ## Generic target-specific stage composition -/

theorem residual_stage_one_count_lt
    {I : Type} [Fintype I]
    (total regular exceptions : ℕ) (count : I → ℕ)
    (cost : I → ContactParameters6600Research.DegreeVector)
    (hcover : total ≤ regular + ((∑ i, count i) + exceptions))
    (hregular : regular * residualStageOne.gap ≤ residualStageOne.regularNumerator)
    (hy : (∑ i, (cost i).y) ≤ pivotB.algebraicCap)
    (hr : (∑ i, (cost i).r) ≤
      2 * pivotB.implicitYCap * pivotB.algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ pivotB.implicitYCap)
    (hcount : ∀ i, count i * pivotB.gap ≤
      (pivotB.n - pivotB.w) * dot pivotB.agreement (cost i) +
        (pivotB.errors + 1) * pivotB.gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * pivotB.algebraicCap ^ 2) :
    total < 2010526830 + firstResidualSingularCeiling := by
  have h :=
    ContactRecursiveResidualStages6656Research.complete_stage_count_lt
      residualStageOne pivotB
      pivot_projection_gates.1 pivot_projection_gates.2.1
      total regular exceptions count cost hcover hregular hy hr hz hcount
      hexceptions
  rw [residual_stage_ceilings.1] at h
  exact h

theorem residual_stage_two_count_lt
    {I : Type} [Fintype I]
    (total regular exceptions : ℕ) (count : I → ℕ)
    (cost : I → ContactParameters6600Research.DegreeVector)
    (hcover : total ≤ regular + ((∑ i, count i) + exceptions))
    (hregular : regular * residualStageTwo.gap ≤ residualStageTwo.regularNumerator)
    (hy : (∑ i, (cost i).y) ≤ pivotGcd12.algebraicCap)
    (hr : (∑ i, (cost i).r) ≤
      2 * pivotGcd12.implicitYCap * pivotGcd12.algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ pivotGcd12.implicitYCap)
    (hcount : ∀ i, count i * pivotGcd12.gap ≤
      (pivotGcd12.n - pivotGcd12.w) * dot pivotGcd12.agreement (cost i) +
        (pivotGcd12.errors + 1) * pivotGcd12.gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * pivotGcd12.algebraicCap ^ 2) :
    total < 1933414760 + secondResidualSingularCeiling := by
  have h :=
    ContactRecursiveResidualStages6656Research.complete_stage_count_lt
      residualStageTwo pivotGcd12
      pivot_projection_gates.2.2.2.2.2.1
      pivot_projection_gates.2.2.2.2.2.2.1
      total regular exceptions count cost hcover hregular hy hr hz hcount
      hexceptions
  rw [residual_stage_ceilings.2] at h
  exact h

end ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6670Research
