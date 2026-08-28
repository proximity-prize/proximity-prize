import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamilyResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch

/-!
# Shared prime-budget affine identities at score 66.30

The geometric residual-support theorem and the numerical flag ledger were
developed independently.  They define extensionally equal score-66.30
agreement flags.  This module records that equality once and exports the
consumer-shaped affine cost and mixed-volume identities.
-/

namespace ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily6630Research

open scoped Classical BigOperators
open ContactRegularComponentCover
open ContactFlagBezout6543Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactNearPencil6630FlagResearch

noncomputable section

set_option autoImplicit false

variable {Omega : Type} [Field Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}

/-- The geometric literal flag is the affine ledger flag. -/
theorem residualAgreementFlag6630_eq_affine (d : ℕ) :
    ContactNearPencil6630FlagResearch.residualAgreementFlag6630 d =
      unitYZFlag + d • agreementDirection6630 := by
  rfl

/-- Residual agreement costs are affine in the score-66.30 residual degree. -/
theorem PrimeFlagBudgetFamily.weightedCost_residualAgreementFlag6630
    {p q : FlagDegree}
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H) p q)
    (C : RegularComponent Omega G T H) (d : ℕ) :
    B.weightedCost
        (ContactNearPencil6630FlagResearch.residualAgreementFlag6630 d) C =
      d * B.weightedCost agreementDirection6630 C +
        B.weightedCost unitYZFlag C := by
  rw [residualAgreementFlag6630_eq_affine]
  simp only [PrimeFlagBudgetFamily.weightedCost, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

theorem flagMixed_residualAgreement6630_direction
    (p : FlagDegree) (d : ℕ) :
    flagMixed p
        (ContactNearPencil6630FlagResearch.residualAgreementFlag6630 d)
        agreementDirection6630 =
      d * flagMixed p agreementDirection6630 agreementDirection6630 +
        flagMixed p agreementDirection6630 unitYZFlag := by
  rw [residualAgreementFlag6630_eq_affine]
  simp [flagMixed, unitYZFlag, agreementDirection6630]
  ring

theorem flagMixed_residualAgreement6630_unitYZ
    (p : FlagDegree) (d : ℕ) :
    flagMixed p
        (ContactNearPencil6630FlagResearch.residualAgreementFlag6630 d)
        unitYZFlag =
      d * flagMixed p agreementDirection6630 unitYZFlag +
        flagMixed p unitYZFlag unitYZFlag := by
  rw [residualAgreementFlag6630_eq_affine]
  simp [flagMixed, unitYZFlag, agreementDirection6630]
  ring

theorem flagMixed_residualAgreement6630_unitZ
    (p : FlagDegree) (d : ℕ) :
    flagMixed p
        (ContactNearPencil6630FlagResearch.residualAgreementFlag6630 d)
        unitZFlag =
      d * flagMixed p agreementDirection6630 unitZFlag +
        flagMixed p unitYZFlag unitZFlag := by
  rw [residualAgreementFlag6630_eq_affine]
  simp [flagMixed, unitYZFlag, unitZFlag, agreementDirection6630]
  ring

end

end ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily6630Research

#print axioms ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily6630Research.PrimeFlagBudgetFamily.weightedCost_residualAgreementFlag6630
#print axioms ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily6630Research.flagMixed_residualAgreement6630_direction
