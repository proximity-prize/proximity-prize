import ProximityPrize.Benchmark.TargetLower

/-!
# Exact split-budget arithmetic for the stacked score-67.18 target
-/

namespace ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

def promotedBudget : ℕ := 274980727511395087

def fixedRegularCost : ℕ := 272023227082052303
def fixedSingularCost : ℕ := 24731934873070
def firstResidualRegularCost : ℕ := 79361072258730
def firstResidualSingularCeiling : ℕ := 287984100301317
def secondResidualRegularCost : ℕ := 53819495787524
def secondResidualSingularCeiling : ℕ := 30911739274586

def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ :=
  firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ :=
  secondResidualRegularCost + secondResidualSingularCeiling

def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem total_and_slack_exact :
    totalCost = 272500035424547530 ∧
      promotedBudget - totalCost = 2480692086847557 := by
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
