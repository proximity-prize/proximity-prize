import ProximityPrize.SubmissionLower.ContactFirstTailProjection6731Research
namespace ProximityPrize.SubmissionLower.ContactFirstTailActiveData6733Research
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum ContactRegularComponentCover
open ContactGenericSurface ContactIdentityResidualIterationResearch
open ContactProperCutSeedCount ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch
open ContactSharpTaylorFixedMeet6656Research
open ContactWeakSeparableSeparatorResearch
open ContactScalarCoordinateSeparator6630Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactTerminalAdaptiveProjection6600Research
open ContactRegularComponentYZPositivity6630Research
open ContactResidualStageDerivative6600Research
open ContactTerminalAdaptiveProjection6656Research
open ContactFirstTailCertificate6731Research
open ContactFirstTailProjection6731Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
variable {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
theorem exists_firstTail_activeNestedData_of_caps
    (S:ResidualStage phi Gamma x pchar e flag w
      (ContactMovingAgreementCertificate6719Research.support a b s))
    (hproper:¬ S.G∣globalTailCut phi S.F (w+1))
    (hflagChar:flag.yz+flag.all < pchar∧flag.all < pchar∧
      flag.zOnly+flag.yz+flag.all < pchar)
    (hmixed:(1+(w+1)*(2*(b+s+3)-2))*flag.all+
      (flag.yz+flag.all)*((2*(s+2)-1)*(w+1)) < pchar):
    ∃ (base:∀ C:RegularComponent Omega S.G
        (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
        SeparableLiteralCoordinate C.1),
      ∃ (hactive:∀ C:RegularComponent Omega S.G
          (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
          D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
            D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0),
        ∃ (hZ:∀ C:RegularComponent Omega S.G
            (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
            LiteralProjectionGate C 2),
          Nonempty (AdaptiveNestedProjectionDataActive base hactive
            (residualStage_pderiv_one_ne_zero_of_support S)):=by
  classical
  let T:=globalTailCut phi S.F (w+1)
  let H:=regularitySurface phi S.F
  let supp:=ContactMovingAgreementCertificate6719Research.support a b s
  have hsy:supp.s < supp.ys:=by
    change s+2 < b+s+3
    omega
  have hTflag:PolynomialInFlag (sharpResidualAgreementFlag supp (w+1)) T:=
    firstTail_in_sharp_flag S
  obtain ⟨hGY,hGS,hGZ⟩:=
    degree_bounds_of_polynomialInFlag S.flag_support
  obtain ⟨hTY,hTS,_⟩:=
    degree_bounds_of_polynomialInFlag hTflag
  have hTY':T.degreeOf 0 ≤ 1+(w+1)*(2*(b+s+3)-2):=by
    apply hTY.trans_eq
    exact sharpResidualAgreementFlag_ys supp hsy (w+1)
  have hTS':T.degreeOf 1 ≤ (2*(s+2)-1)*(w+1):=by
    apply hTS.trans_eq
    simp only [sharpResidualAgreementFlag,sharpAgreementDirection,supp,
      ContactMovingAgreementCertificate6719Research.support]
  have hGdegree:∀ j:Fin 3,S.G.degreeOf j < pchar:=by
    intro j
    fin_cases j
    · exact hGY.trans_lt hflagChar.1
    · exact hGS.trans_lt hflagChar.2.1
    · exact hGZ.trans_lt hflagChar.2.2
  have hmixedZ:coordinateMixedDegree Omega S.G T 2 < pchar:=by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
      (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
  let choiceData:∀ C:RegularComponent Omega S.G T H,
      ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
    fun C↦regularComponent_exists_separableLiteralCoordinate6630
      phi S.F S.G T pchar S.G_dvd_surface S.irreducible_G hproper
      S.y_dependent hGdegree hmixedZ C
  let base:∀ C:RegularComponent Omega S.G T H,
      SeparableLiteralCoordinate C.1:=fun C↦(choiceData C).choose
  have hbaseIndex:∀ C:RegularComponent Omega S.G T H,
      (base C).index=0∨(base C).index=2:=by
    intro C
    exact (choiceData C).choose_spec
  have hactive:∀ C:RegularComponent Omega S.G T H,
      D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
        D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0:=by
    intro C
    have hb:=base_differential_ne_zero (base C)
    rcases hbaseIndex C with hidx | hidx
    · left
      simpa only [hidx] using hb
    · right
      simpa only [hidx] using hb
  have hZ:∀ C:RegularComponent Omega S.G T H,
      LiteralProjectionGate C 2:=by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
      pchar S.G T S.irreducible_G
      (regularComponent_G_mem Omega S.G T H C)
      (regularComponent_T_mem Omega S.G T H C)
      hproper hGdegree hmixedZ
  exact ⟨base,hactive,hZ,
    exists_adaptiveNestedProjectionDataActive base hactive
      (residualStage_pderiv_one_ne_zero_of_support S)⟩
end
end ProximityPrize.SubmissionLower.ContactFirstTailActiveData6733Research
