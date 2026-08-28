import ProximityPrize.Benchmark.TargetLower

/-!
# Exact promoted-budget arithmetic for the stacked score-66.70 target

This file freezes only the six independently rounded components of the
`a = 182668` recursive-GCD ledger.  The fixed regular component uses the
accepted active-YZ tail and equal-weight Taylor direction; the fixed singular
component and both residual singular components use the tight
implicit-core-plus-exceptions ledger.

The geometric providers and profile-specific identifications are deliberately
kept in separate modules.  This arithmetic consumer only joins an exact
three-cell partition once those bounds have been supplied.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

def promotedBudget : ℕ := 137490364055697543

def fixedRegularCost : ℕ := 137394274994425942
def fixedSingularCost : ℕ := 8763101791996
def firstResidualRegularCost : ℕ := 12254368989649
def firstResidualSingularCeiling : ℕ := 28953301794005
def secondResidualRegularCost : ℕ := 2958631319067
def secondResidualSingularCeiling : ℕ := 13449567524592

def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ :=
  firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ :=
  secondResidualRegularCost + secondResidualSingularCeiling

def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem total_and_slack_exact :
    totalCost = 137460653965845251 ∧
      promotedBudget - totalCost = 29710089852292 := by
  norm_num [totalCost, fixedCost, firstResidualCeiling,
    secondResidualCeiling, fixedRegularCost, fixedSingularCost,
    firstResidualRegularCost, firstResidualSingularCeiling,
    secondResidualRegularCost, secondResidualSingularCeiling, promotedBudget]

/-- Arithmetic consumer for the exact disjoint recursive-GCD partition. -/
theorem total_lt_promotedBudget
    (total firstResidual secondResidual fixed : ℕ)
    (hpartition : total = firstResidual + secondResidual + fixed)
    (hfirst : firstResidual < firstResidualCeiling)
    (hsecond : secondResidual < secondResidualCeiling)
    (hfixed : fixed ≤ fixedCost) :
    total < promotedBudget := by
  rw [hpartition]
  have hsum :
      firstResidual + secondResidual + fixed < totalCost := by
    change firstResidual + secondResidual + fixed <
      fixedCost + firstResidualCeiling + secondResidualCeiling
    omega
  exact hsum.trans (by
    rw [total_and_slack_exact.1]
    norm_num [promotedBudget])

end ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

#print axioms ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research.total_and_slack_exact
#print axioms ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research.total_lt_promotedBudget
