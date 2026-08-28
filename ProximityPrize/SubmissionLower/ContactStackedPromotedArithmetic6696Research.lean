import ProximityPrize.Benchmark.TargetLower

/-!
# Exact promoted-budget arithmetic for the stacked score-66.96 target

This file freezes only the six independently rounded components of the
`a = 182414` recursive-GCD ledger.  The fixed regular component uses the
accepted active-YZ tail and equal-weight Taylor direction; the fixed singular
component and both residual singular components use the tight
implicit-core-plus-exceptions ledger.

The geometric providers and profile-specific identifications are deliberately
kept in separate modules.  This arithmetic consumer only joins an exact
three-cell partition once those bounds have been supplied.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6696Research

def promotedBudget : ℕ := 274980727623867933

def fixedRegularCost : ℕ := 247630321222852759
def fixedSingularCost : ℕ := 18023438793552
def firstResidualRegularCost : ℕ := 64331733997583
def firstResidualSingularCeiling : ℕ := 189926330250373
def secondResidualRegularCost : ℕ := 835044267066492
def secondResidualSingularCeiling : ℕ := 23141679224390

def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ :=
  firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ :=
  secondResidualRegularCost + secondResidualSingularCeiling

def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem total_and_slack_exact :
    totalCost = 248760788672185149 ∧
      promotedBudget - totalCost = 26219938951682784 := by
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

end ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6696Research
