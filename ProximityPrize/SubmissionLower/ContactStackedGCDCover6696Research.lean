import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRecursiveGCDResearch
import ProximityPrize.SubmissionLower.ContactStackedInterpolation6696Research

/-!
# Recursive GCD cover for the three 66.96 interpolants

Only the target boxes are new.  The branch alternative is the generic
three-vanishing GCD cover.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedGCDCover6696Research

open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation
open ContactRecursiveGCDResearch
open ContactStackedParameters6696Research
open ContactStackedInterpolation6696Research

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

/-- The disjoint recursive branch alternative after one selected
specialization. -/
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

/-- Three nonzero boxed interpolants together with their exact recursive
specialization cover. -/
theorem exists_stacked_interpolants_with_recursive_cover
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ QA QB QC : GlobalPoly,
      QA ≠ 0 ∧
      QA ∈ globalCoefficientBox IRSProfile.Field
        (31 * agreements) w 21207 9 ∧
      QB ≠ 0 ∧
      QB ∈ globalCoefficientBox IRSProfile.Field
        (60 * agreements) w 925 18 ∧
      QC ≠ 0 ∧
      QC ∈ globalCoefficientBox IRSProfile.Field
        (34 * agreements) w 801717 8 ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        RecursiveSpecializationBranch P gamma QA QB QC := by
  obtain ⟨QA, QB, QC, hQA, hboxA, hQB, hboxB, hQC, hboxC, huniversal⟩ :=
    exists_stacked_universal_vanishing_interpolants u0 u1
  refine ⟨QA, QB, QC, hQA, hboxA, hQB, hboxB, hQC, hboxC, ?_⟩
  intro gamma P support hP hcard hvalues
  obtain ⟨hA, hB, hC⟩ := huniversal gamma P support hP hcard hvalues
  exact recursive_branch_of_three_vanishings P gamma QA QB QC hA hB hC

end

end ProximityPrize.SubmissionLower.ContactStackedGCDCover6696Research

#print axioms ProximityPrize.SubmissionLower.ContactStackedGCDCover6696Research.recursive_branch_of_three_vanishings
#print axioms ProximityPrize.SubmissionLower.ContactStackedGCDCover6696Research.exists_stacked_interpolants_with_recursive_cover
