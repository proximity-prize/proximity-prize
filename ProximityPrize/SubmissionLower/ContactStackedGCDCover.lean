import ProximityPrize.SubmissionLower.ContactRecursiveGCD
import ProximityPrize.SubmissionLower.ContactFlagKernelUniversality
import ProximityPrize.SubmissionLower.ContactStackedParameters
namespace ProximityPrize.SubmissionLower.ContactStackedGCDCover

open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation
open ContactRecursiveGCD
open ContactStackedParameters

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

def RecursiveSpecializationBranch
    (P : Polynomial IRSProfile.Field) (gamma : IRSProfile.Field)
    (QA QB QC : GlobalPoly) : Prop :=
  let phi := (specialization IRSProfile.Field P gamma).toRingHom
  (phi (gcd12 QA QB) ≠ 0 ∧
      phi (quotientA QA QB) = 0 ∧ phi (quotientB QA QB) = 0) ∨
    (phi (gcd12 QA QB) = 0 ∧ phi (gcd123 QA QB QC) ≠ 0 ∧
      phi (middleQuotient QA QB QC) = 0 ∧
      phi (quotientC QA QB QC) = 0) ∨
    (phi (gcd123 QA QB QC) = 0 ∧ phi (gcd12 QA QB) = 0)

theorem recursive_branch_of_three_vanishings
    (P : Polynomial IRSProfile.Field) (gamma : IRSProfile.Field)
    (QA QB QC : GlobalPoly)
    (hA : specialization IRSProfile.Field P gamma QA = 0)
    (hB : specialization IRSProfile.Field P gamma QB = 0)
    (hC : specialization IRSProfile.Field P gamma QC = 0) :
    RecursiveSpecializationBranch P gamma QA QB QC := by
  exact recursive_three_branch_cover
    (specialization IRSProfile.Field P gamma).toRingHom QA QB QC hA hB hC

end

end ProximityPrize.SubmissionLower.ContactStackedGCDCover
