import ProximityPrize.SubmissionLower.ContactMovingOuterBudget
import ProximityPrize.SubmissionLower.ContactRegularComponentYZPositivity
import ProximityPrize.SubmissionLower.ContactReducedTaylorProfile

/-!
# Moving budgets on a congruent reduced cut

The three static coordinate-pole costs may be taken from a projection family
on a reduced representative of the cut.  The moving-coordinate cost remains
the already-proved cost on the original cut.  Divisibility of the difference
by the surface factor identifies the actual cut ideals, so the two component
families have literally the same underlying prime ideals.
-/

namespace ProximityPrize.SubmissionLower.ContactMovingReducedBudget

open scoped Classical BigOperators WithZero
open ActualCurveCoordinateField ContactRegularComponentCover CoordinateBoxZeroCount
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactWeakSeparableSeparator
open ContactAdaptiveUnitPoleFamily
open ContactMovingCurveBudget
open ContactMovingCurveFamily
open ContactMovingOuterBudget
open ContactCongruentCuts
open ContactGenericSurface ContactTaylorNumerators
open ContactFlagBezout ContactResidualSupportParameters
open ContactMovingAgreementCertificate
open ContactMovingProjection
open ContactMovingDerivativeFlags
open ContactSharpTaylorFixedMeet
open ContactReducedTaylorProfile
open ContactRegularComponentYZPositivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K

/-- Replace only the three static pole fields of an existing moving budget by
the fields from a projection family on a congruent reduced cut. -/
def mergedBudget [IsAlgClosed K]
    {G T Tred H Q : Poly} {p q : FlagDegree}
    (hd : G ∣ T - Tred)
    {baseRed : ∀ C : RegularComponent K G Tred H,
      SeparableLiteralCoordinate C.1}
    (red : AdaptiveUnitProjectionFamily baseRed p q)
    (old : ∀ C : RegularComponent K G T H, MovingPoleBudget C.1 H Q)
    (C : RegularComponent K G T H) : MovingPoleBudget C.1 H Q where
  zCost := red.toAdaptiveUnitPoleBudget.zCost (regularComponentEquiv hd C)
  yzCost := red.toAdaptiveUnitPoleBudget.yzCost (regularComponentEquiv hd C)
  allCost := red.toAdaptiveUnitPoleBudget.allCost (regularComponentEquiv hd C)
  movingCost := (old C).movingCost
  zPole := red.toAdaptiveUnitPoleBudget.zPole (regularComponentEquiv hd C)
  yzPole := red.toAdaptiveUnitPoleBudget.yzPole (regularComponentEquiv hd C)
  allPole := red.toAdaptiveUnitPoleBudget.allPole (regularComponentEquiv hd C)
  movingPole := (old C).movingPole

theorem mergedBudget_sum_z_le [IsAlgClosed K]
    {G T Tred H Q : Poly} {p q : FlagDegree}
    (hd : G ∣ T - Tred)
    {baseRed : ∀ C : RegularComponent K G Tred H,
      SeparableLiteralCoordinate C.1}
    (red : AdaptiveUnitProjectionFamily baseRed p q)
    (old : ∀ C : RegularComponent K G T H, MovingPoleBudget C.1 H Q) :
    (∑ C, (mergedBudget hd red old C).zCost) ≤ flagMixed p q unitZFlag := by
  simpa only [mergedBudget, (regularComponentEquiv hd).sum_comp
    red.toAdaptiveUnitPoleBudget.zCost] using
      red.toAdaptiveUnitPoleBudget.sum_zCost_le

theorem mergedBudget_sum_yz_le [IsAlgClosed K]
    {G T Tred H Q : Poly} {p q : FlagDegree}
    (hd : G ∣ T - Tred)
    {baseRed : ∀ C : RegularComponent K G Tred H,
      SeparableLiteralCoordinate C.1}
    (red : AdaptiveUnitProjectionFamily baseRed p q)
    (old : ∀ C : RegularComponent K G T H, MovingPoleBudget C.1 H Q) :
    (∑ C, (mergedBudget hd red old C).yzCost) ≤ flagMixed p q unitYZFlag := by
  simpa only [mergedBudget, (regularComponentEquiv hd).sum_comp
    red.toAdaptiveUnitPoleBudget.yzCost] using
      red.toAdaptiveUnitPoleBudget.sum_yzCost_le

theorem mergedBudget_sum_all_le [IsAlgClosed K]
    {G T Tred H Q : Poly} {p q : FlagDegree}
    (hd : G ∣ T - Tred)
    {baseRed : ∀ C : RegularComponent K G Tred H,
      SeparableLiteralCoordinate C.1}
    (red : AdaptiveUnitProjectionFamily baseRed p q)
    (old : ∀ C : RegularComponent K G T H, MovingPoleBudget C.1 H Q) :
    (∑ C, (mergedBudget hd red old C).allCost) ≤ flagMixed p q unitAllFlag := by
  simpa only [mergedBudget, (regularComponentEquiv hd).sum_comp
    red.toAdaptiveUnitPoleBudget.allCost] using
      red.toAdaptiveUnitPoleBudget.sum_allCost_le

theorem mergedBudget_sum_moving_eq [IsAlgClosed K]
    {G T Tred H Q : Poly} {p q : FlagDegree}
    (hd : G ∣ T - Tred)
    {baseRed : ∀ C : RegularComponent K G Tred H,
      SeparableLiteralCoordinate C.1}
    (red : AdaptiveUnitProjectionFamily baseRed p q)
    (old : ∀ C : RegularComponent K G T H, MovingPoleBudget C.1 H Q) :
    (∑ C, (mergedBudget hd red old C).movingCost) =
      ∑ C, (old C).movingCost := by
  rfl

variable {Omega E : Type} [Field Omega] [IsAlgClosed Omega]
variable [Field E] [IsAlgClosed E] [Algebra Omega E]
variable [Algebra (RatFunc Omega) E] [IsScalarTower Omega (RatFunc Omega) E]

end
end ProximityPrize.SubmissionLower.ContactMovingReducedBudget
