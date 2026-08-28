import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6630Research
import ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6630Research

/-!
# Factor ledger from adaptive YZ projection families at score 66.30

At each proper terminal outer cut, a shared adaptive `Z/YZ/All` family is
converted to the recursive prime budget. Regularity supplies positivity of the
combined `Z + YZ` cost, replacing the expensive all-coordinate fallback.
-/

namespace ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6630Research

open scoped Classical
open ContactNearPencil6630ArithmeticResearch ContactPolynomialSolutions
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactFlagBezout6543Research
open ContactIdentityResidualIteration6630Research
open ContactIdentityResidualCurveIteration6630Research
open ContactIdentityResidualGlobalFlag6630Research
open ContactIdentityResidualFactorProvider6630Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactNearPencil6630FlagResearch
open ContactNearPencil6630FactorLedgerResearch
open ContactAdaptiveUnitPoleFamilyResearch
open ContactRegularComponentYZPositivity6630Research
open ContactTerminalAdaptiveProjection6630Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Terminal adaptive YZ families discharge both the shared prime-budget
hypothesis and the regularity-based `Z + YZ` positivity required by the
complete score-66.30 factor recursion. -/
theorem recursive_scaled_factor_6630_of_adaptive_projection_families_yz
    (hphi : Function.Injective phi)
    {flag : FlagDegree}
    (S : ResidualStage6630 phi Gamma x pchar errors flag w)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hprojection : TerminalAdaptiveProjectionFamiliesYZ6630 S) :
    Gamma.card * gap ^ 2 ≤ factorRegularLedgerYZ flag := by
  apply recursive_scaled_factor_6630_of_prime_flag_budgets_z_yz
    hphi S hnodes hagreement
  intro D i hi hproper
  obtain ⟨base, ⟨P⟩⟩ := hprojection D i hi hproper
  refine ⟨P.family.toPrimeFlagBudgetFamily, ?_⟩
  intro C
  exact P.one_le_zCost_add_yzCost phi D.stage.F rfl
    D.stage.G_dvd_surface C

end

end ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6630Research

#print axioms ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6630Research.recursive_scaled_factor_6630_of_adaptive_projection_families_yz
