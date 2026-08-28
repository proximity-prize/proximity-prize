import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedUnitFamilyActive6630Research
import ProximityPrize.SubmissionLower.ContactRegularComponentYZPositivity6630Research

/-!
# Refined YZ family from the active-differential constructor

This is the small bridge from the repaired nested projection constructor to
the regularity-based `Z + YZ` positivity theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactAdaptiveNestedYZFamily6630Research

open scoped Classical
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveRationalProjection
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveProjectionCoordinateResearch
open ContactAdaptiveAffineProjectionResearch
open ContactFlagAffineFamilyDegree6543Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedUnitFamilyActive6630Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactRegularComponentYZPositivity6630Research
open ContactFlagBezout6543Research

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}

/-- The active nested constructor retains the value of its common `Y+lam Z`
projection, exactly as required by the regularity positivity argument. -/
def adaptiveUnitProjectionFamilyYZ_of_active_nested
    (p q : FlagDegree)
    (base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1)
    (hactive : ∀ C : RegularComponent Omega G T H,
      D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0) ≠ 0 ∨
        D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2) ≠ 0)
    (hZ : ∀ C : RegularComponent Omega G T H,
      LiteralProjectionGate C 2)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (D : AdaptiveNestedProjectionDataActive base hactive hSderiv)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport p)
    (hTsupport : T.support ⊆ flagSupport q) :
    AdaptiveUnitProjectionFamilyYZ base p q where
  family := adaptiveUnitProjectionFamily_of_active_nested p q base hactive hZ
    hSderiv D hG hproper hGsupport hTsupport
  lam := D.lam
  yzValue := by
    intro C
    exact coordinateOfGate_value (affineU Omega C.1 D.lam) (D.uGate C)

/-- Existential consumer seam for the repaired active-differential route. -/
theorem exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
    (p q : FlagDegree)
    (base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1)
    (hactive : ∀ C : RegularComponent Omega G T H,
      D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0) ≠ 0 ∨
        D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2) ≠ 0)
    (hZ : ∀ C : RegularComponent Omega G T H,
      LiteralProjectionGate C 2)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport p)
    (hTsupport : T.support ⊆ flagSupport q) :
    Nonempty (AdaptiveUnitProjectionFamilyYZ base p q) := by
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionDataActive base hactive hSderiv
  exact ⟨adaptiveUnitProjectionFamilyYZ_of_active_nested p q base hactive hZ
    hSderiv D hG hproper hGsupport hTsupport⟩

end


end ProximityPrize.SubmissionLower.ContactAdaptiveNestedYZFamily6630Research

#print axioms ProximityPrize.SubmissionLower.ContactAdaptiveNestedYZFamily6630Research.exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
