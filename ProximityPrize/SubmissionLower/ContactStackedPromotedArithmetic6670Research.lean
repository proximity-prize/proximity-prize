import ProximityPrize.Benchmark.TargetLower

/-!
# Exact split-budget arithmetic for the stacked score-67.30 target

This file freezes only the six independently rounded components of the
`a = 182078` recursive-GCD ledger.  The fixed regular component uses the
cumulative fixed-cell surface, active-YZ tail, and sharp Taylor direction;
the fixed singular
component and both residual singular components use the tight
implicit-pair parameterization; both residual regular components use the
unequal-contact product bound.

No geometry occurs in this module; it only proves arithmetic positivity for the
three-cell partition once those bounds have been supplied.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

def promotedBudget : ℕ := 274980726811395087

def fixedRegularCost : ℕ := 212964177019120016
def fixedSingularCost : ℕ := 17040508075070
def firstResidualRegularCost : ℕ := 96625554990674
def firstResidualSingularCeiling : ℕ := 639622355847463
def secondResidualRegularCost : ℕ := 1692624412238996
def secondResidualSingularCeiling : ℕ := 17040508075070

def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ :=
  firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ :=
  secondResidualRegularCost + secondResidualSingularCeiling

def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem total_and_slack_exact :
    totalCost = 215427130358347289 ∧
      promotedBudget - totalCost = 59553596453047798 := by
  norm_num [totalCost, fixedCost, firstResidualCeiling,
    secondResidualCeiling, fixedRegularCost, fixedSingularCost,
    firstResidualRegularCost, firstResidualSingularCeiling,
    secondResidualRegularCost, secondResidualSingularCeiling,
    promotedBudget]

theorem total_lt_promotedBudget
    (card firstCount secondCount fixedCount : ℕ)
    (hpart : card = firstCount + secondCount + fixedCount)
    (hfirst : firstCount < firstResidualCeiling)
    (hsecond : secondCount < secondResidualCeiling)
    (hfixed : fixedCount ≤ fixedCost) :
    card ≤ promotedBudget := by
  have hslack : totalCost ≤ promotedBudget := by
    norm_num [total_and_slack_exact.1, total_and_slack_exact.2, promotedBudget]
  unfold totalCost at hslack
  omega

end ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research
