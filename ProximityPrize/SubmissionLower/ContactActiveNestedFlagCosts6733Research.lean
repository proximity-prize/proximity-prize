import ProximityPrize.SubmissionLower.ContactActiveNestedFlagData6733Research
namespace ProximityPrize.SubmissionLower.ContactActiveNestedFlagCosts6733Research
open ActualCurveCoordinateField ContactRegularComponentCover
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveProjectionCoordinateResearch CoordinateBoxZeroCount
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedUnitFamilyActive6630Research
open ContactAdaptiveUnitPoleFamilyResearch ContactPrimeFlagBudgetFamilyResearch
open ContactFlagBezout6543Research ContactFlagAffineFamilyDegree6543Research
open ContactFlagTriangularProjectionResearch ContactFlagPrincipalCycles6543Research
open ArbitraryRationalProjectionResearch ContactActiveNestedFlagData6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
  SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
  KaehlerDifferential.D Omega (CoordinateField Omega C.1)
      (coordinate Omega C.1 0)≠0∨
    KaehlerDifferential.D Omega (CoordinateField Omega C.1)
      (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
variable (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
variable (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
variable (hG:Irreducible G) (hproper:¬ G∣T)
variable (hGsupport:G.support ⊆ flagSupport surfaceFlag)
variable (hTsupport:T.support ⊆ flagSupport tailFlag)
noncomputable def activeNestedUnitFamily:
    AdaptiveUnitProjectionFamily base surfaceFlag tailFlag:=
  adaptiveUnitProjectionFamily_of_active_nested surfaceFlag tailFlag base hactive
    hZ hSderiv D hG hproper hGsupport hTsupport
theorem activeNestedUnitFamily_zCost (C:RegularComponent Omega G T H):
    (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
      hGsupport hTsupport).toPrimeFlagBudgetFamily.zCost C=
      coordinateDegree Omega (CoordinateField Omega C.1)
        (coordinateOfGate (coordinate Omega C.1 2) (hZ C)):=rfl
theorem activeNestedUnitFamily_uCost (C:RegularComponent Omega G T H):
    (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
      hGsupport hTsupport).toPrimeFlagBudgetFamily.yzCost C=
      coordinateDegree Omega (CoordinateField Omega C.1)
        (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)):=rfl
theorem activeNestedUnitFamily_allCost (C:RegularComponent Omega G T H):
    (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
      hGsupport hTsupport).toPrimeFlagBudgetFamily.allCost C=
      coordinateDegree Omega (CoordinateField Omega C.1)
        (Sum.inr {
          embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
            (affineV Omega C.1 D.mu (D.mu*D.lam))
              (D.allAffineTranscendental C)
          finite:=D.allFinite C
          separable:=D.allSeparable C}):=rfl
theorem activeNestedUnitFamily_zCost_eq_flagCost
    (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
    (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
      hGsupport hTsupport).toPrimeFlagBudgetFamily.zCost a.1=
      coordinateDegree Omega (CoordinateField Omega a.1.1)
        (coordinateOfGate
          (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
            (MvPolynomial.X (zOrder 0)))
          (activeNestedZGate base hactive hZ hSderiv D a)):=by
  rw [activeNestedUnitFamily_zCost]
  rw [coordinateOfGate_degree_of_transcendental _ _ a.2]
  rw [coordinateOfGate_degree_of_transcendental _ _
    (activeNestedZTranscendental base hactive hSderiv D a)]
  rw [elementEmbedding_congr
    (activeNestedZTranscendental base hactive hSderiv D a) a.2
    (by simp [zOrder,flagEvaluation_X_two])]
theorem activeNestedUnitFamily_uCost_eq_flagCost
    (C:RegularComponent Omega G T H):
    (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
      hGsupport hTsupport).toPrimeFlagBudgetFamily.yzCost C=
      coordinateDegree Omega (CoordinateField Omega C.1)
        (coordinateOfGate
          (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
            (MvPolynomial.X (uOrder 0)))
          (activeNestedUGate base hactive hSderiv D C)):=by
  rw [activeNestedUnitFamily_uCost]
  rw [coordinateOfGate_degree_of_transcendental _ _ (D.uTranscendental C)]
  rw [coordinateOfGate_degree_of_transcendental _ _
    (activeNestedUTranscendental base hactive hSderiv D C)]
  rw [elementEmbedding_congr
    (activeNestedUTranscendental base hactive hSderiv D C)
    (D.uTranscendental C) (by simp [uOrder,flagEvaluation_X_zero])]
theorem activeNestedUnitFamily_allCost_eq_flagCost
    (C:RegularComponent Omega G T H):
    (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
      hGsupport hTsupport).toPrimeFlagBudgetFamily.allCost C=
      coordinateDegree Omega (CoordinateField Omega C.1)
        (coordinateOfGate
          (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
            (MvPolynomial.X (vOrder 0)))
          (activeNestedVGate base hactive hSderiv D C)):=by
  rw [activeNestedUnitFamily_allCost]
  change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
      (elementEmbedding Omega (CoordinateField Omega C.1)
        (affineV Omega C.1 D.mu (D.mu*D.lam))
          (D.allAffineTranscendental C)).toRingHom.toAlgebra;
    Module.finrank (RatFunc Omega) (CoordinateField Omega C.1))=_
  rw [coordinateOfGate_degree_of_transcendental _ _
    (activeNestedVTranscendental base hactive hSderiv D C)]
  rw [elementEmbedding_congr
    (activeNestedVTranscendental base hactive hSderiv D C)
    (D.allAffineTranscendental C) (by simp [vOrder,flagEvaluation_X_one])]
end
end ProximityPrize.SubmissionLower.ContactActiveNestedFlagCosts6733Research
