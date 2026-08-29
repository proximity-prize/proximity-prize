import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingCurveBudget6719Research
import ProximityPrize.SubmissionLower.ContactMovingCurveFamily6719Research
import ProximityPrize.SubmissionLower.ContactMovingOuterBudget6719Research
import ProximityPrize.SubmissionLower.ContactAdaptiveUnitPoleFamilyResearch
import ProximityPrize.SubmissionLower.ContactRegularComponentYZPositivity6630Research
import ProximityPrize.SubmissionLower.ContactCongruentCuts6643Research
import ProximityPrize.SubmissionLower.ContactReducedTaylorProfileResearch

/-!
# Moving budgets on a congruent reduced cut

The three static coordinate-pole costs may be taken from a projection family
on a reduced representative of the cut.  The moving-coordinate cost remains
the already-proved cost on the original cut.  Divisibility of the difference
by the surface factor identifies the actual cut ideals, so the two component
families have literally the same underlying prime ideals.
-/

namespace ProximityPrize.SubmissionLower.ContactMovingReducedBudget6720Research

open scoped Classical BigOperators WithZero
open ActualCurveCoordinateField ContactRegularComponentCover CoordinateBoxZeroCount
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveUnitPoleFamilyResearch
open ContactMovingCurveBudget6719Research
open ContactMovingCurveFamily6719Research
open ContactMovingOuterBudget6719Research
open ContactCongruentCuts6643Research
open ContactGenericSurface ContactTaylorNumerators
open ContactFlagBezout6543Research ContactResidualSupportParametersResearch
open ContactMovingAgreementCertificate6719Research
open ContactMovingProjection6676Research
open ContactMovingDerivativeFlags6719Research
open ContactSharpTaylorFixedMeet6656Research
open ContactReducedTaylorProfileResearch
open ContactRegularComponentYZPositivity6630Research

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

variable {Omega E : Type} [Field Omega] [IsAlgClosed Omega]
variable [Field E] [IsAlgClosed E] [Algebra Omega E]
variable [Algebra (RatFunc Omega) E] [IsScalarTower Omega (RatFunc Omega) E]

/-- Existing filtered-cut moving bounds, with the static projection family
pulled back from the reduced Taylor representative. -/
theorem exists_actual_cut_budgets_reduced
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K)
    (G T : MvPolynomial (Fin 3) Omega) (a b s d : ℕ) (xI u0 u1 : K)
    (hT : T = agreementPolynomial phi F d xI u0 u1)
    (hF : ResidualSupportData (support a b s) F) (flag : FlagDegree)
    (hG : G ≠ 0) (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag flag G)
    (baseSharp : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      SeparableLiteralCoordinate C.1)
    (unitSharp : AdaptiveUnitProjectionFamily baseSharp flag
      (sharpResidualAgreementFlag (support a b s) d))
    (baseRed : ∀ C : RegularComponent Omega G
      (reducedAgreementPolynomial phi (support a b s) F d xI u0 u1)
      (regularitySurface phi F), SeparableLiteralCoordinate C.1)
    (unitRed : AdaptiveUnitProjectionFamilyYZ baseRed flag
      (reducedResidualAgreementFlag (support a b s) d))
    (pchar : ℕ) [CharP E pchar]
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar) :
    ∃ budget : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      MovingPoleBudget C.1 (regularitySurface phi F) (surfaceMap phi (polyG K F)),
      (∀ C, 1 ≤ (budget C).zCost + (budget C).yzCost) ∧
      (∑ C, (budget C).zCost) ≤
        flagMixed flag (reducedResidualAgreementFlag (support a b s) d) unitZFlag ∧
      (∑ C, (budget C).yzCost) ≤
        flagMixed flag (reducedResidualAgreementFlag (support a b s) d) unitYZFlag ∧
      (∑ C, (budget C).allCost) ≤
        flagMixed flag (reducedResidualAgreementFlag (support a b s) d) unitAllFlag ∧
      (∑ C, (budget C).movingCost) ≤ flagMixed flag
        (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
        (center a b s + d • ContactMovingPositiveLedger6719Research.surfaceFlag a b s) := by
  classical
  let Tred := reducedAgreementPolynomial phi (support a b s) F d xI u0 u1
  have hd : G ∣ T - Tred := by
    rw [hT]
    exact hdiv.trans
      (agreementPolynomial_sub_reduced_dvd phi (support a b s) F d xI u0 u1)
  obtain ⟨old, _hcost, _hz, _hyz, _ha, hm⟩ := exists_actual_cut_budgets (E := E)
    phi F G T a b s d xI u0 u1 hT hF flag hG hdiv hGflag
    baseSharp unitSharp pchar hmix
  let budget := mergedBudget hd unitRed.family old
  refine ⟨budget, ?_, mergedBudget_sum_z_le hd unitRed.family old,
    mergedBudget_sum_yz_le hd unitRed.family old,
    mergedBudget_sum_all_le hd unitRed.family old, ?_⟩
  · intro C
    dsimp only [budget, mergedBudget]
    change 1 ≤ unitRed.family.toPrimeFlagBudgetFamily.zCost
        (regularComponentEquiv hd C) +
      unitRed.family.toPrimeFlagBudgetFamily.yzCost (regularComponentEquiv hd C)
    exact unitRed.one_le_zCost_add_yzCost phi F rfl hdiv
      (regularComponentEquiv hd C)
  simpa only [budget, mergedBudget] using hm

end
end ProximityPrize.SubmissionLower.ContactMovingReducedBudget6720Research
