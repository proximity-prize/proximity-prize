import ProximityPrize.Benchmark.TargetLower

/-!
# Exact split-budget arithmetic for the stacked score-67.11 target

This file freezes only the six independently rounded components of the
`a = 182268` recursive-GCD ledger.  The fixed regular component uses the
cumulative fixed-cell surface, active-YZ tail, and sharp Taylor direction;
the fixed singular
component and both residual singular components use the tight
implicit-pair parameterization; both residual regular components use the
unequal-contact product bound.

No geometry occurs in this module; it only proves arithmetic positivity for the
three-cell partition once those bounds have been supplied.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

def promotedBudget : ℕ := 274980727411395087

def fixedRegularCost : ℕ := 271299482742257601
def fixedSingularCost : ℕ := 31812929513254
def firstResidualRegularCost : ℕ := 71157206728370
def firstResidualSingularCeiling : ℕ := 288040349938195
def secondResidualRegularCost : ℕ := 60719748906090
def secondResidualSingularCeiling : ℕ := 31812929513254

def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ :=
  firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ :=
  secondResidualRegularCost + secondResidualSingularCeiling

def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem total_and_slack_exact :
    totalCost = 271783025906856764 ∧
      promotedBudget - totalCost = 3197701504538323 := by
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
