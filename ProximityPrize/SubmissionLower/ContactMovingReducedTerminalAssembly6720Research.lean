import ProximityPrize.SubmissionLower.ContactMovingReducedBudget6720Research
import ProximityPrize.SubmissionLower.ContactMovingReducedProperCut6720Research
import ProximityPrize.SubmissionLower.ContactMovingReducedTerminalNormalize6720Research

/-!
# Opaque terminal assembly for the reduced-static moving proof

The merged-budget existential, the proper-cut application, and the terminal
ledger normalization are consumed in this module.  No dependent budget record
or sum proof escapes into the outer descendant theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactMovingReducedTerminalAssembly6720Research

open scoped Classical BigOperators
open ContactGenericSurface ContactRegularComponentCover
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactFlagBezout6543Research ContactResidualSupportParametersResearch
open ContactMovingAgreementCertificate6719Research
open ContactRobustFixedMeet6656Research ContactSharpTaylorFixedMeet6656Research
open ContactReducedTaylorProfileResearch
open ContactAdaptiveUnitPoleFamilyResearch ContactMovingCurveBudget6719Research
open ContactWeakSeparableSeparatorResearch
open ContactRegularComponentYZPositivity6630Research
open ContactCongruentCuts6643Research
open ContactMovingReducedBudget6720Research
open ContactMovingReducedProperCut6720Research
open ContactMovingReducedTerminalNormalize6720Research
open ContactMovingReducedFactorLedger6720Research

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega}
variable {E : Type} [Field E] [IsAlgClosed E] [Algebra Omega E]
variable [Algebra (RatFunc Omega) E] [IsScalarTower Omega (RatFunc Omega) E]

/-- Consume the reduced static budgets and original moving budget in one opaque
step, returning exactly the affine terminal ledger bound. -/
theorem terminal_bound_from_reduced_budgets
    (p : Profile) (a b s d aD : ℕ)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (xI u0I u1I : K) (pchar : ℕ) [CharP Omega pchar] [CharP E pchar]
    (flag : FlagDegree)
    (H : ProperCutStageData (phi := phi) F G T selected Gamma nodes x u0 u1
      pchar p.errors d aD p.degreeIncidence p.unitIncidence flag
      (sharpResidualAgreementFlag (support a b s) d) a b s)
    (hT : T = agreementPolynomial phi F d xI u0I u1I)
    (hG : G ≠ 0)
    (baseSharp : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      SeparableLiteralCoordinate C.1)
    (unitSharp : AdaptiveUnitProjectionFamily baseSharp flag
      (sharpResidualAgreementFlag (support a b s) d))
    (baseRed : ∀ C : RegularComponent Omega G
      (reducedAgreementPolynomial phi (support a b s) F d xI u0I u1I)
      (regularitySurface phi F), SeparableLiteralCoordinate C.1)
    (unitRed : AdaptiveUnitProjectionFamilyYZ baseRed flag
      (reducedResidualAgreementFlag (support a b s) d))
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar)
    (degree : ∀ k ≤ d,
      (nodes.card-k)*(aD-d)*(d-k) ≤ p.degreeIncidence*(aD-k))
    (unit : ∀ k ≤ d,
      (nodes.card-k)*(aD-d) ≤ p.unitIncidence*(aD-k))
    (hgap : aD-d = p.gap) :
    Gamma.card * p.gap ≤
      d * factorDegreeCost p (support a b s) a b s flag +
        factorUnitCost p (support a b s) a b s flag := by
  classical
  let Tred := reducedAgreementPolynomial phi (support a b s) F d xI u0I u1I
  have hd : G ∣ T-Tred := by
    rw [hT]
    exact H.hdiv.trans
      (agreementPolynomial_sub_reduced_dvd phi (support a b s) F d xI u0I u1I)
  let base : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      SeparableLiteralCoordinate C.1 :=
    fun C ↦ baseRed (regularComponentEquiv hd C)
  obtain ⟨budget, hpositive, hz, hyz, hall, hmove⟩ :=
    exists_actual_cut_budgets_reduced (E := E)
      phi F G T a b s d xI u0I u1I hT
      ⟨H.hFs, H.hFys, H.hFtotal⟩ flag hG H.hdiv H.hGflag
      baseSharp unitSharp baseRed unitRed pchar hmix
  let zSum := flagMixed flag
    (reducedResidualAgreementFlag (support a b s) d) unitZFlag
  let yzSum := flagMixed flag
    (reducedResidualAgreementFlag (support a b s) d) unitYZFlag
  let allSum := flagMixed flag
    (reducedResidualAgreementFlag (support a b s) d) unitAllFlag
  let movingSum := flagMixed flag
    (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
    (center a b s + d • ContactMovingPositiveLedger6719Research.surfaceFlag a b s)
  have hz' : (∑ C, (budget C).zCost) ≤ zSum := by
    simpa only [zSum] using hz
  have hyz' : (∑ C, (budget C).yzCost) ≤ yzSum := by
    simpa only [yzSum] using hyz
  have hall' : (∑ C, (budget C).allCost) ≤ allSum := by
    simpa only [allSum] using hall
  have hmove' : (∑ C, (budget C).movingCost) ≤ movingSum := by
    simpa only [movingSum] using hmove
  have hbound : Gamma.card * (aD-d) ≤
      p.degreeIncidence *
        ContactMovingStageZero6719Research.degreeCost a b s
          zSum yzSum allSum movingSum +
      p.unitIncidence *
        ContactMovingStageZero6719Research.unitCost a b s
          zSum yzSum allSum +
      (p.errors+1)*(aD-d)*(zSum+yzSum) :=
    proper_cut_stage_zero (phi := phi)
      F G T selected Gamma nodes x u0 u1 pchar p.errors d aD
      p.degreeIncidence p.unitIncidence flag
      (sharpResidualAgreementFlag (support a b s) d) a b s
      H base budget hpositive zSum yzSum allSum movingSum
      hz' hyz' hall' hmove' degree unit
  exact terminal_bound_of_stage_zero_gap p (support a b s) a b s d
    aD Gamma.card flag hgap hbound

end

end ProximityPrize.SubmissionLower.ContactMovingReducedTerminalAssembly6720Research
