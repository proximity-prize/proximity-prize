import ProximityPrize.SubmissionLower.ContactMovingComponentIncidence6719Research

/-!
# Opaque proper-cut adapter for the reduced-moving outer proof

This module packages the long dependent premise list consumed by the existing
proper-cut theorem.  The four aggregate pole costs stay explicit, so its
conclusion is definitionally the exact stage-zero ledger used downstream.
-/

namespace ProximityPrize.SubmissionLower.ContactMovingReducedProperCut6720Research

open scoped Classical BigOperators
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch
open ContactWeakSeparableSeparatorResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactMovingCurveBudget6719Research
open ContactMovingStageZero6719Research
open ContactMovingComponentIncidence6719Research

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- All geometric and incidence premises for one invocation of the existing
moving proper-cut theorem.  Packaging them prevents its large dependent
application from being re-elaborated in the outer terminal theorem. -/
structure ProperCutStageData
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (pchar e d a U V : ℕ) [CharP Omega pchar]
    (surfaceFlag cutFlag : FlagDegree) (a0 b0 s0 : ℕ) : Prop where
  hphi : Function.Injective phi
  hdiv : G ∣ surfaceMap phi F
  hGflag : PolynomialInFlag surfaceFlag G
  hTflag : PolynomialInFlag cutFlag T
  hFs : wt residualSWeights F ≤
    (ContactMovingAgreementCertificate6719Research.support a0 b0 s0).s
  hFys : wt residualYSWeights F ≤
    (ContactMovingAgreementCertificate6719Research.support a0 b0 s0).ys
  hFtotal : wt residualTotalWeights F ≤
    (ContactMovingAgreementCertificate6719Research.support a0 b0 s0).total
  hinj : Set.InjOn x nodes
  hdegreeSelected : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ d
  hsolution : ∀ gamma ∈ Gamma,
    specialization K (selected gamma) gamma F = 0
  hregular : ∀ gamma ∈ Gamma,
    MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
      (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
        (phi Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0
  hGpoint : ∀ gamma ∈ Gamma,
    MvPolynomial.eval (selectedPoint phi selected gamma) G = 0
  hTpoint : ∀ gamma ∈ Gamma,
    MvPolynomial.eval (selectedPoint phi selected gamma) T = 0
  hagreement : ∀ gamma ∈ Gamma,
    a ≤ (nodes.filter (fun i ↦
      (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card
  hnoPencil : NoLargeSelectedPencil selected Gamma d e
  hchar : d < pchar
  hda : d < a

/-- Opaque specialization of `proper_cut_seed_bound_of_moving_budgets` with
four named aggregate costs and the exact stage-zero conclusion. -/
theorem proper_cut_stage_zero
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (pchar e d a U V : ℕ) [CharP Omega pchar]
    (surfaceFlag cutFlag : FlagDegree) (a0 b0 s0 : ℕ)
    (H : ProperCutStageData (phi := phi) F G T selected Gamma nodes x u0 u1
      pchar e d a U V surfaceFlag cutFlag a0 b0 s0)
    (base : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      SeparableLiteralCoordinate C.1)
    (budget : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      MovingPoleBudget C.1 (regularitySurface phi F) (surfaceMap phi (polyG K F)))
    (positive : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      1 ≤ (budget C).zCost + (budget C).yzCost)
    (zSum yzSum allSum movingSum : ℕ)
    (hz : (∑ C, (budget C).zCost) ≤ zSum)
    (hyz : (∑ C, (budget C).yzCost) ≤ yzSum)
    (hall : (∑ C, (budget C).allCost) ≤ allSum)
    (hmoving : (∑ C, (budget C).movingCost) ≤ movingSum)
    (degree : ∀ k ≤ d,
      (nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (unit : ∀ k ≤ d,
      (nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * degreeCost a0 b0 s0 zSum yzSum allSum movingSum +
      V * unitCost a0 b0 s0 zSum yzSum allSum +
      (e + 1) * (a - d) * (zSum + yzSum) := by
  exact proper_cut_seed_bound_of_moving_budgets
    H.hphi F G T selected Gamma nodes x u0 u1 pchar e d a U V
    surfaceFlag cutFlag a0 b0 s0 H.hdiv H.hGflag H.hTflag
    H.hFs H.hFys H.hFtotal H.hinj H.hdegreeSelected H.hsolution
    H.hregular H.hGpoint H.hTpoint H.hagreement H.hnoPencil H.hchar H.hda
    base budget positive zSum yzSum allSum movingSum
    hz hyz hall hmoving degree unit

end

end ProximityPrize.SubmissionLower.ContactMovingReducedProperCut6720Research
