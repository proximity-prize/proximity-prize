import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredThirdResidual6750Research
import ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research

 






namespace ProximityPrize.SubmissionLower
namespace ContactCanonicalHighSourceUniformThirdCap6750Research

open ContactAnchoredHardCellSelector6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredThirdResidual6750Research
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch

set_option autoImplicit false
set_option maxRecDepth 100000

 

theorem thirdCost_antitone_t {t₁ t₂ y r : Nat} (ht : t₁ ≤ t₂) :
    (thirdStage t₂ y r).regularCountCap + (thirdPivot t₂ r).countCap ≤
      (thirdStage t₁ y r).regularCountCap + (thirdPivot t₁ r).countCap := by
  unfold thirdStage thirdPivot
  simp only [UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, UnequalParameters.errors,
    UnequalParameters.gap, TightParameters.countCap,
    TightParameters.tightNumerator, TightParameters.coreNumerator,
    TightParameters.agreement, TightParameters.aggregateCost,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.kappa, TightParameters.errors, TightParameters.gap,
    ContactSingularLedger6600Research.dot,
    ContactAnchoredThirdResidual6750Research.n,
    ContactAnchoredThirdResidual6750Research.w,
    ContactAnchoredThirdResidual6750Research.agreements]
  gcongr

 

theorem HardCell.thirdCost_le_hardThirdCap
    {t y r : Nat} (cell : HardCell t y r) :
    (thirdStage t y r).regularCountCap + (thirdPivot t r).countCap ≤
      ContactRouterUniformCaps6750Research.hardThirdCap := by
  have hcheck : ∀ (yy : Fin 67), 38 ≤ yy.val →
      ∀ (rr : Fin 15), hostileMinR yy.val ≤ rr.val →
        (thirdStage (hardMinT yy.val rr.val) yy.val rr.val).regularCountCap +
            (thirdPivot (hardMinT yy.val rr.val) rr.val).countCap ≤
          ContactRouterUniformCaps6750Research.hardThirdCap := by
    decide
  exact (thirdCost_antitone_t cell.t_lower).trans
    (hcheck ⟨y, Nat.lt_succ_iff.mpr cell.y_upper⟩ cell.y_lower
      ⟨r, Nat.lt_succ_iff.mpr cell.r_upper⟩ cell.r_lower)

end ContactCanonicalHighSourceUniformThirdCap6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactCanonicalHighSourceUniformThirdCap6750Research.HardCell.thirdCost_le_hardThirdCap
