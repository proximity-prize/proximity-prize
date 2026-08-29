import ProximityPrize.Benchmark.TargetLower

/-!
# Exact split-budget arithmetic for the stacked score-67.40 target

This file freezes only the six independently rounded components of the
`a = 181982` recursive-GCD ledger.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

def promotedBudget : ℕ := 274980727111395087

def fixedRegularCost : ℕ := 272670075349801548
def fixedSingularCost : ℕ := 32899002304208
def firstResidualRegularCost : ℕ := 106380543940677
def firstResidualSingularCeiling : ℕ := 627273384769604
def secondResidualRegularCost : ℕ := 96230126998659
def secondResidualSingularCeiling : ℕ := 32899002304208

def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ := firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ := secondResidualRegularCost + secondResidualSingularCeiling
def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem promotedBudget_eq :
    promotedBudget = 274980727111395087 := rfl

theorem totalCost_lt_promotedBudget :
    totalCost < promotedBudget := by
  decide

theorem promotedBudget_slack :
    promotedBudget - totalCost = 1414969701276183 := by
  decide

end ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research
