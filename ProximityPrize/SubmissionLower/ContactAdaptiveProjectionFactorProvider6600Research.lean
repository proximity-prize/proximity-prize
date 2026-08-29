import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6600Research
import ProximityPrize.SubmissionLower.ContactAdaptiveUnitPoleFamilyResearch

/-!
# Factor ledger from adaptive projection families

This is the narrow geometric seam for score 66.  At each proper terminal
outer cut, one shared adaptive `Z/YZ/All` projection family is converted to
the recursive prime budget.  Positivity of the all-coordinate fallback is
then automatic.
-/

namespace ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6600Research

open scoped Classical
open ContactNearPencil6600ArithmeticResearch ContactPolynomialSolutions
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualFactorProvider6600Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactNearPencil6600FlagResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveUnitPoleFamilyResearch

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- At every proper terminal outer cut, the actual regular components admit
one common adaptive unit projection family. -/
def TerminalAdaptiveProjectionFamilies
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w) : Prop :=
  ∀ (D : S.TerminalDescendant) (i : Iota),
    i ∈ D.stage.nodes →
    ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i) →
    ∃ base : ∀ C : RegularComponent Omega D.stage.G
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (regularitySurface phi D.stage.F),
        SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamily base flag
        (residualAgreementFlag D.degree))

/-- The adaptive family discharges both the shared prime-budget hypothesis
and the degree-zero-safe all-cost positivity required by the complete
factor recursion. -/
theorem recursive_scaled_factor_6600_of_adaptive_projection_families
    (hphi : Function.Injective phi)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hprojection : TerminalAdaptiveProjectionFamilies S) :
    Gamma.card * gap ^ 2 ≤ factorRegularLedger flag := by
  apply recursive_scaled_factor_6600_of_prime_flag_budgets
    hphi S hnodes hagreement
  intro D i hi hproper
  obtain ⟨base, ⟨P⟩⟩ := hprojection D i hi hproper
  refine ⟨P.toPrimeFlagBudgetFamily, ?_⟩
  intro C
  exact P.one_le_toPrimeFlagBudgetFamily_allCost C

end

end ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6600Research
