import ProximityPrize.SubmissionLower.Y6
import ProximityPrize.SubmissionLower.M7
namespace ProximityPrize.SubmissionLower.ContactFirstTailBudget6731Research
open scoped Classical BigOperators
open ContactGenericSurface ContactTaylorNumerators ContactPrimeSeedIncidence
open ContactProperCutSeedCount ContactRegularComponentCover
open ContactWeakSeparableSeparatorResearch ContactAdaptiveUnitPoleFamilyResearch
open ContactFlagBezout6543Research ContactMovingCurveBudget6719Research
open ContactMovingCurveFamily6719Research ContactMovingProjection6676Research
open ContactMovingAgreementCertificate6719Research ContactMovingOuterBudget6719Research
open ContactMovingDerivativeFlags6719Research ContactResidualSupportParametersResearch
open ContactSharpTaylorFixedMeet6656Research ContactFirstTailCertificate6731Research
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
variable [IsScalarTower Ω (RatFunc Ω) E]
theorem exists_firstTail_cut_budgets
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Ω) (a b s w:ℕ) (hw:1 ≤ w)
   (hT:T=globalTailCut φ F (w+1))
   (hF:ResidualSupportData (support a b s) F) (flag:FlagDegree)
   (hG:G≠0) (hdiv:G∣surfaceMap φ F) (hGflag:PolynomialInFlag flag G)
   (base:∀ C:RegularComponent Ω G T (regularitySurface φ F),SeparableLiteralCoordinate C.1)
   (unit:AdaptiveUnitProjectionFamily base flag (sharpResidualAgreementFlag (support a b s) (w+1)))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar):
   ∃ budget:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
     (∀ C,(budget C).zCost=unit.toPrimeFlagBudgetFamily.zCost C∧
       (budget C).yzCost=unit.toPrimeFlagBudgetFamily.yzCost C∧
       (budget C).allCost=unit.toPrimeFlagBudgetFamily.allCost C)∧
     (∑ C,(budget C).zCost) ≤ flagMixed flag (paddedCut a b s (w+1)) unitZFlag∧
     (∑ C,(budget C).yzCost) ≤ flagMixed flag (paddedCut a b s (w+1)) unitYZFlag∧
     (∑ C,(budget C).allCost) ≤ flagMixed flag (paddedCut a b s (w+1)) unitAllFlag∧
     (∑ C,(budget C).movingCost) ≤ flagMixed flag
       (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
       (center a b s+(w+1) • ContactMovingPositiveLedger6719Research.surfaceFlag a b s):=by
 classical
 obtain ⟨coeffs,cflags,heq,hcoeff,hclass⟩:=globalTailCut_certificate
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight w hw
 obtain ⟨hHflag,hGcontact⟩:=surfaceMap_HG_flags
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
 have hderiv:regularitySurface φ F∈
     Ideal.span ({G,MvPolynomial.pderiv (1:Fin 3) G}:Set (MvPolynomial (Fin 3) Ω)):=by
   rw [regularitySurface, ←ContactRegularFactorGate.surfaceMap_pderiv_R]
   exact ContactDerivativeRegularity6719Research.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
 have hT':T=filteredCut w coeffs (surfaceMap φ (polyH K F))
     (surfaceMap φ (polyG K F)):=hT.trans heq
 clear hT
 subst T
 obtain ⟨budget,hcost,hz,hyz,ha,hm⟩:=exists_moving_pole_budget_family (E:=E)
   G (regularitySurface φ F) (surfaceMap φ (polyG K F)) w coeffs
   base flag (sharpResidualAgreementFlag (support a b s) (w+1)) unit hG hderiv hGflag
   a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
   (by convert hmix using 1 <;> ring)
 refine ⟨budget,hcost,hz.trans (mixed_sharp_le_padded a b s (w+1) flag unitZFlag),
   hyz.trans (mixed_sharp_le_padded a b s (w+1) flag unitYZFlag),
   ha.trans (mixed_sharp_le_padded a b s (w+1) flag unitAllFlag),hm.trans ?_⟩
 rw [mixed_affine_third,mixed_affine_third]
 exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ w)) _
end
end ProximityPrize.SubmissionLower.ContactFirstTailBudget6731Research
