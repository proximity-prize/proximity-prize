import ProximityPrize.SubmissionLower.ContactAnchoredReducedWeightedResultants6750Research
import ProximityPrize.SubmissionLower.ContactTangentCoefficientProvider6732Research

namespace ProximityPrize.SubmissionLower.ContactAnchoredReducedDelayedTailAssembly6750Bisect

open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactFirstTailCertificate6731Research ContactProperCutSeedCount
open ContactDelayedTailMultiplicityProvider6732Research
open ContactPrimeSeedIncidence ContactInterpolation
open ContactResidualSupportParametersResearch
open ContactTangentCoefficientProvider6732Research
open ContactFlagBezout6543Research
open ContactAnchoredCongruentCuts6750Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactAdaptiveProjectionCoordinateResearch
open ContactWeakSeparableSeparatorResearch
open ActualCurveCoordinateField CoordinateBoxZeroCount

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

noncomputable def congruentCut_separableLiteralCoordinate
    {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    {G T T' H : MvPolynomial (Fin 3) Omega}
    (hd : G ∣ T - T')
    (base : ∀ C : RegularComponent Omega G T' H,
      SeparableLiteralCoordinate C.1)
    (C : RegularComponent Omega G T H) :
    SeparableLiteralCoordinate C.1 :=
  base (regularComponentEquiv hd C)

theorem congruentCut_adaptiveYZPole
    {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    {G T T' H : MvPolynomial (Fin 3) Omega}
    {surfaceFlag tailFlag : FlagDegree}
    (hd : G ∣ T - T')
    (base : ∀ C : RegularComponent Omega G T' H,
      SeparableLiteralCoordinate C.1)
    (U : AdaptiveUnitProjectionFamily base surfaceFlag tailFlag)
    (C : RegularComponent Omega G T H) :
    ∀ W : Finset (CoordinatePoleMass.Place Omega
        (CoordinateField Omega C.1)),
      (∑ v ∈ W,
        ContactSparsePoleSupportResearch.exponentSetPoleWeight v.val
          (coordinate Omega C.1) (flagSupport unitYZFlag)) ≤
        ((PrimeFlagBudgetFamily.ofCongruentCut hd
          U.toPrimeFlagBudgetFamily).yzCost C : ℤ) := by
  intro W
  let Cr := regularComponentEquiv hd C
  letI : C.1.IsPrime := regularComponent_isPrime Omega G T H C
  letI : Algebra Omega (CoordinateField Omega C.1) :=
    OreLocalization.instAlgebra
  calc
    (∑ v ∈ W,
        ContactSparsePoleSupportResearch.exponentSetPoleWeight v.val
          (coordinate Omega C.1) (flagSupport unitYZFlag)) =
      ∑ v ∈ W, CoordinatePoleMass.poleOrder Omega
        (CoordinateField Omega C.1) v
        (coordinateValue Omega (CoordinateField Omega C.1)
          (U.yzProjection Cr)) := by
      apply Finset.sum_congr rfl
      intro v _
      exact U.yzPole_eq Cr v
    _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
        (U.yzProjection Cr) : ℤ) :=
      @finite_sum_coordinate_pole_le_degree Omega
        (CoordinateField Omega C.1) _ _ OreLocalization.instAlgebra _
        (U.yzProjection Cr) W

theorem congruentCut_adaptiveYZPositive
    {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    {G T T' H : MvPolynomial (Fin 3) Omega}
    {surfaceFlag tailFlag : FlagDegree}
    (hd : G ∣ T - T')
    (base : ∀ C : RegularComponent Omega G T' H,
      SeparableLiteralCoordinate C.1)
    (U : AdaptiveUnitProjectionFamily base surfaceFlag tailFlag)
    (C : RegularComponent Omega G T H)
    (hpositive : 1 ≤ U.toPrimeFlagBudgetFamily.yzCost
      (regularComponentEquiv hd C)) :
    1 ≤ (PrimeFlagBudgetFamily.ofCongruentCut hd
      U.toPrimeFlagBudgetFamily).yzCost C := by
  exact hpositive

end
end ProximityPrize.SubmissionLower.ContactAnchoredReducedDelayedTailAssembly6750Bisect
