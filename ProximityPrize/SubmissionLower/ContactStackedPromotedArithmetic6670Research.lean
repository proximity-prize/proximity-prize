import ProximityPrize.Benchmark.TargetLower

/-!
# Exact split-budget arithmetic for the stacked score-67.10 target

This file freezes only the six independently rounded components of the
`a = 182278` recursive-GCD ledger.  The fixed regular component uses the
cumulative fixed-cell surface, active-YZ tail, and sharp Taylor direction;
the fixed singular
component and both residual singular components use the tight
implicit-core-plus-exceptions ledger.

The geometric providers and profile-specific identifications are deliberately
kept in separate modules.  This arithmetic consumer only joins an exact
three-cell partition once those bounds have been supplied.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

def promotedBudget : ℕ := 274980727511395087

def fixedRegularCost : ℕ := 271473322645104462
def fixedSingularCost : ℕ := 24704454497073
def firstResidualRegularCost : ℕ := 79359795016101
def firstResidualSingularCeiling : ℕ := 287664115289271
def secondResidualRegularCost : ℕ := 53818862701924
def secondResidualSingularCeiling : ℕ := 30877392328228

def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ :=
  firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ :=
  secondResidualRegularCost + secondResidualSingularCeiling

def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem total_and_slack_exact :
    totalCost = 271949747264937059 ∧
      promotedBudget - totalCost = 3030980246458028 := by
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
