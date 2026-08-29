import ProximityPrize.SubmissionLower.ContactFirstTailBudget6731Research
import ProximityPrize.SubmissionLower.ContactFirstTailReducedCertificate6732Research
import ProximityPrize.SubmissionLower.ContactMovingReducedBudget6720Research

/-! Moving budgets for the first tail with reduced static pole costs. -/

namespace ProximityPrize.SubmissionLower.ContactFirstTailReducedBudget6732Research

open scoped Classical BigOperators
open ContactGenericSurface ContactTaylorNumerators ContactPrimeSeedIncidence
open ContactProperCutSeedCount ContactRegularComponentCover
open ContactWeakSeparableSeparatorResearch ContactAdaptiveUnitPoleFamilyResearch
open ContactFlagBezout6543Research ContactMovingCurveBudget6719Research
open ContactMovingAgreementCertificate6719Research ContactMovingProjection6676Research
open ContactResidualSupportParametersResearch ContactSharpTaylorFixedMeet6656Research
open ContactRegularComponentYZPositivity6630Research
open ContactFirstTailCertificate6731Research ContactFirstTailBudget6731Research
open ContactReducedTaylorProfileResearch ContactMovingReducedBudget6720Research
open ContactCongruentCuts6643Research
open ContactFirstTailReducedCertificate6732Research

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

variable {K Omega E : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable [Field E] [IsAlgClosed E] [Algebra Omega E] [Algebra (RatFunc Omega) E]
variable [IsScalarTower Omega (RatFunc Omega) E]

theorem exists_firstTail_cut_budgets_reduced
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K)
    (G T : MvPolynomial (Fin 3) Omega) (a b s w : ℕ) (hw : 1 ≤ w)
    (hT : T = globalTailCut phi F (w + 1))
    (hF : ResidualSupportData (support a b s) F) (flag : FlagDegree)
    (hG : G ≠ 0) (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag flag G)
    (baseSharp : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      SeparableLiteralCoordinate C.1)
    (unitSharp : AdaptiveUnitProjectionFamily baseSharp flag
      (sharpResidualAgreementFlag (support a b s) (w + 1)))
    (baseRed : ∀ C : RegularComponent Omega G
      (reducedGlobalTailCut phi (support a b s) F (w + 1))
      (regularitySurface phi F), SeparableLiteralCoordinate C.1)
    (unitRed : AdaptiveUnitProjectionFamilyYZ baseRed flag
      (reducedResidualAgreementFlag (support a b s) (w + 1)))
    (pchar : ℕ) [CharP E pchar]
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < pchar) :
    ∃ budget : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      MovingPoleBudget C.1 (regularitySurface phi F) (surfaceMap phi (polyG K F)),
      (∀ C, 1 ≤ (budget C).zCost + (budget C).yzCost) ∧
      (∑ C, (budget C).zCost) ≤
        flagMixed flag (reducedResidualAgreementFlag (support a b s) (w + 1)) unitZFlag ∧
      (∑ C, (budget C).yzCost) ≤
        flagMixed flag (reducedResidualAgreementFlag (support a b s) (w + 1)) unitYZFlag ∧
      (∑ C, (budget C).allCost) ≤
        flagMixed flag (reducedResidualAgreementFlag (support a b s) (w + 1)) unitAllFlag ∧
      (∑ C, (budget C).movingCost) ≤ flagMixed flag
        (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
        (center a b s + (w + 1) •
          ContactMovingPositiveLedger6719Research.surfaceFlag a b s) := by
  classical
  let Tred := reducedGlobalTailCut phi (support a b s) F (w + 1)
  have hd : G ∣ T - Tred := by
    rw [hT]
    exact hdiv.trans
      (globalTailCut_sub_reduced_dvd phi (support a b s) F (w + 1))
  obtain ⟨old, _hcost, _hz, _hyz, _ha, hm⟩ :=
    exists_firstTail_cut_budgets (E := E) phi F G T a b s w hw hT hF flag
      hG hdiv hGflag baseSharp unitSharp pchar hmix
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
  · simpa only [budget, mergedBudget] using hm

end

end ProximityPrize.SubmissionLower.ContactFirstTailReducedBudget6732Research
