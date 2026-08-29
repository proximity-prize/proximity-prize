import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingCurveFamily6719Research
import ProximityPrize.SubmissionLower.ContactMovingDerivativeFlags6719Research
import ProximityPrize.SubmissionLower.ContactMovingPositiveLedger6719Research
import ProximityPrize.SubmissionLower.ContactDerivativeRegularity6719Research
import ProximityPrize.SubmissionLower.ContactRegularFactorGate

namespace ProximityPrize.SubmissionLower.ContactMovingOuterBudget6719Research
open scoped Classical BigOperators
open ContactGenericSurface ContactTaylorNumerators ContactPrimeSeedIncidence
open ContactProperCutSeedCount ContactRegularComponentCover
open ContactWeakSeparableSeparatorResearch ContactAdaptiveUnitPoleFamilyResearch
open ContactFlagBezout6543Research ContactMovingCurveBudget6719Research
open ContactMovingCurveFamily6719Research ContactMovingProjection6676Research
open ContactMovingAgreementCertificate6719Research
open ContactMovingDerivativeFlags6719Research ContactResidualSupportParametersResearch
open ContactSharpTaylorFixedMeet6656Research
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
variable [IsScalarTower Ω (RatFunc Ω) E]

def paddedCut (a b s d : ℕ) : FlagDegree :=
  ContactMovingPositiveLedger6719Research.centreFlag a b s +
    d • ContactMovingPositiveLedger6719Research.directionFlag a b s

theorem mixed_add_second (p q r t : FlagDegree) :
    flagMixed p (q+r) t = flagMixed p q t + flagMixed p r t := by
  simp only [flagMixed, add_zOnly, add_yz, add_all]
  ring

theorem mixed_affine_third (p q C R : FlagDegree) (k : ℕ) :
    flagMixed p q (C+k • R) = flagMixed p q C + k*flagMixed p q R := by
  simp only [flagMixed, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

theorem mixed_sharp_le_padded (a b s d : ℕ) (p r : FlagDegree) :
    flagMixed p (sharpResidualAgreementFlag (support a b s) d) r ≤
      flagMixed p (paddedCut a b s d) r := by
  have he : paddedCut a b s d =
      sharpResidualAgreementFlag (support a b s) d + direction a b s := by
    rw [sharp_flag_eq]
    change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
    congr 1 <;> simp [paddedCut, ContactMovingPositiveLedger6719Research.centreFlag,
      ContactMovingPositiveLedger6719Research.directionFlag, direction, unitYZFlag] <;> ring
  rw [he, mixed_add_second]
  exact Nat.le_add_right _ _

theorem exists_actual_cut_budgets
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (G T : MvPolynomial (Fin 3) Ω) (a b s d : ℕ) (xI u0 u1 : K)
    (hT : T = agreementPolynomial φ F d xI u0 u1)
    (hF : ResidualSupportData (support a b s) F) (flag : FlagDegree)
    (hG : G ≠ 0) (hdiv : G ∣ surfaceMap φ F) (hGflag : PolynomialInFlag flag G)
    (base : ∀ C : RegularComponent Ω G T (regularitySurface φ F), SeparableLiteralCoordinate C.1)
    (unit : AdaptiveUnitProjectionFamily base flag (sharpResidualAgreementFlag (support a b s) d))
    (pchar : ℕ) [CharP E pchar]
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar) :
    ∃ budget : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
      (∀ C, (budget C).zCost = unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost = unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost = unit.toPrimeFlagBudgetFamily.allCost C) ∧
      (∑ C, (budget C).zCost) ≤ flagMixed flag (paddedCut a b s d) unitZFlag ∧
      (∑ C, (budget C).yzCost) ≤ flagMixed flag (paddedCut a b s d) unitYZFlag ∧
      (∑ C, (budget C).allCost) ≤ flagMixed flag (paddedCut a b s d) unitAllFlag ∧
      (∑ C, (budget C).movingCost) ≤ flagMixed flag
        (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
        (center a b s + d • ContactMovingPositiveLedger6719Research.surfaceFlag a b s) := by
  classical
  obtain ⟨coeffs, cflags, heq, hcoeff, hclass, _⟩ := exists_actual_agreement_certificate
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight d xI u0 u1
  obtain ⟨hHflag, hGcontact⟩ := surfaceMap_HG_flags
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
  have hderiv : regularitySurface φ F ∈
      Ideal.span ({G, MvPolynomial.pderiv (1 : Fin 3) G} : Set (MvPolynomial (Fin 3) Ω)) := by
    rw [regularitySurface, ← ContactRegularFactorGate.surfaceMap_pderiv_R]
    exact ContactDerivativeRegularity6719Research.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
  have hT' : T = filteredCut (d-1) coeffs (surfaceMap φ (polyH K F))
      (surfaceMap φ (polyG K F)) := hT.trans heq
  clear hT
  subst T
  obtain ⟨budget, hcost, hz, hyz, ha, hm⟩ := exists_moving_pole_budget_family (E := E)
    G (regularitySurface φ F) (surfaceMap φ (polyG K F)) (d-1) coeffs
    base flag (sharpResidualAgreementFlag (support a b s) d) unit hG hderiv hGflag
    a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
    (by convert hmix using 1 <;> ring)
  refine ⟨budget, hcost, hz.trans (mixed_sharp_le_padded a b s d flag unitZFlag),
    hyz.trans (mixed_sharp_le_padded a b s d flag unitYZFlag),
    ha.trans (mixed_sharp_le_padded a b s d flag unitAllFlag), hm.trans ?_⟩
  rw [mixed_affine_third, mixed_affine_third]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le d 1)) _

end
end ProximityPrize.SubmissionLower.ContactMovingOuterBudget6719Research
