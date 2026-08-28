import ProximityPrize.Benchmark.TargetLower

/-!
# Exact split-budget arithmetic for the stacked score-67.11 target

This file freezes only the six independently rounded components of the
`a = 182268` recursive-GCD ledger.  The fixed regular component uses the
cumulative fixed-cell surface, active-YZ tail, and sharp Taylor direction;
the fixed singular
component and both residual singular components use the tight
implicit-core-plus-exceptions ledger.

The geometric providers and profile-specific identifications are deliberately
kept in separate modules.  This arithmetic consumer only joins an exact
three-cell partition once those bounds have been supplied.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

def promotedBudget : ℕ := 274980727411395087

def fixedRegularCost : ℕ := 271814083171638565
def fixedSingularCost : ℕ := 24736765516208
def firstResidualRegularCost : ℕ := 2010526830
def firstResidualSingularCeiling : ℕ := 288040349938195
def secondResidualRegularCost : ℕ := 1933414760
def secondResidualSingularCeiling : ℕ := 31812929513254

def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ :=
  firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ :=
  secondResidualRegularCost + secondResidualSingularCeiling

def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem total_and_slack_exact :
    totalCost = 272158677160547812 ∧
      promotedBudget - totalCost = 2822050250847275 := by
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
