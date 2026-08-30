import ProximityPrize.SubmissionLower.ContactActiveNestedCertificate6733Research
import ProximityPrize.SubmissionLower.ContactFirstTailActiveData6733Research
import ProximityPrize.SubmissionLower.ContactProperDelayedTailCertificate6732Research
import ProximityPrize.SubmissionLower.ContactTwoTailFixedSelected6733Research
namespace ProximityPrize.SubmissionLower.ContactProperStageActiveProvider6733Research
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactGenericInitialPoint
open ActualCurveCoordinateField ContactRegularComponentCover
open CoordinateBoxZeroCount
open ContactGenericSurface ContactIdentityResidualIterationResearch
open ContactProperCutSeedCount ContactPrimeSeedIncidence
open ContactFlagBezout6543Research ContactPrimeFlagBudgetFamilyResearch
open ContactMovingAgreementCertificate6719Research
open ContactSharpTaylorFixedMeet6656Research
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveProjectionCoordinateResearch
open ContactActiveNestedFlagCosts6733Research
open ContactActiveNestedFixedPowers6733Research
open ContactActiveNestedCertificate6733Research
open ContactFirstTailCertificate6731Research
open ContactFirstTailProjection6731Research
open ContactFirstTailActiveData6733Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactTwoTailProviderAssembly6732Research
open ContactTwoTailResultantProvider6732Research
open ContactProperDelayedTailCertificate6732Research
open ContactTwoTailFixedSelected6733Research
open ContactTwoTailParameters6733Research
open ContactTerminalAdaptiveProjection6656Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 200000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
def ActiveStageFixedPowerProvider6733:Prop:=
  ∀ {Gamma:Finset K} {flag:FlagDegree}
    (S:Stage K I Gamma IRSProfile.domain prime flag)
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (base:∀ C:FirstTailComponent S,SeparableLiteralCoordinate C.1)
    (hactive:∀ C:FirstTailComponent S,
      KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 0)≠0∨
        KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 2)≠0)
    (hZ:∀ C:FirstTailComponent S,LiteralProjectionGate C 2)
    (D:AdaptiveNestedProjectionDataActive base hactive
      (residualStage_pderiv_one_ne_zero_of_support S)),
    ActiveNestedFixedPowers base hactive hZ
      (residualStage_pderiv_one_ne_zero_of_support S) D
      (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
theorem firstTail_in_twoTailFlag
    {Gamma:Finset K} {flag:FlagDegree}
    (S:Stage K I Gamma IRSProfile.domain prime flag):
    PolynomialInFlag (tailFlag (w+1))
      (globalTailCut (polynomialEmbedding K) S.F (w+1)):=by
  have hs:=firstTail_in_sharp_flag S
  have hAll:
      (sharpResidualAgreementFlag
        ContactProperDelayedTailCertificate6732Research.fixedSupport (w+1)).all ≤
        (tailFlag (w+1)).all:=by decide
  have hYZ:
      (sharpResidualAgreementFlag
          ContactProperDelayedTailCertificate6732Research.fixedSupport (w+1)).yz+
          (sharpResidualAgreementFlag
            ContactProperDelayedTailCertificate6732Research.fixedSupport (w+1)).all ≤
        (tailFlag (w+1)).yz+(tailFlag (w+1)).all:=by decide
  have hTotal:
      (sharpResidualAgreementFlag
          ContactProperDelayedTailCertificate6732Research.fixedSupport (w+1)).zOnly+
          (sharpResidualAgreementFlag
            ContactProperDelayedTailCertificate6732Research.fixedSupport (w+1)).yz+
          (sharpResidualAgreementFlag
            ContactProperDelayedTailCertificate6732Research.fixedSupport (w+1)).all ≤
        (tailFlag (w+1)).zOnly+(tailFlag (w+1)).yz+
          (tailFlag (w+1)).all:=by decide
  intro d hd
  have h:=hs d hd
  exact ⟨h.1.trans hAll,h.2.1.trans hYZ,h.2.2.trans hTotal⟩
theorem properStageProvider6733_of_activeFixedPowers
    (fixedPowers:ActiveStageFixedPowerProvider6733):
    ProperStageProvider6733:=by
  intro Gamma flag S hfirstProper hnodes hagreement hbox hflag
  have hflagChar:flag.yz+flag.all < prime∧flag.all < prime∧
      flag.zOnly+flag.yz+flag.all < prime:=by
    rcases hflag with ⟨hall,hyz,htotal⟩
    dsimp [prime]
    omega
  have hmixed:
      (1+(w+1)*(2*(44+9+3)-2))*flag.all+
        (flag.yz+flag.all)*((2*(9+2)-1)*(w+1)) < prime:=by
    rcases hflag with ⟨hall,hyz,htotal⟩
    norm_num [w,prime] at ⊢
    omega
  obtain ⟨base,hactive,hZ,⟨D⟩⟩:=
    exists_firstTail_activeNestedData_of_caps S hfirstProper hflagChar hmixed
  let hSderiv:=residualStage_pderiv_one_ne_zero_of_support S
  have hGsupport:S.G.support ⊆ flagSupport flag:=
    (support_subset_flagSupport_iff flag S.G).2 S.flag_support
  have hTsupport:
      (globalTailCut (polynomialEmbedding K) S.F (w+1)).support ⊆
        flagSupport (tailFlag (w+1)):=
    (support_subset_flagSupport_iff _ _).2 (firstTail_in_twoTailFlag S)
  let U:=activeNestedUnitFamily base hactive hZ hSderiv D
    S.irreducible_G hfirstProper hGsupport hTsupport
  let multiplicity:FirstTailComponent S → ℕ:=
    localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
  have powers:ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity:=by
    exact fixedPowers S hfirstProper base hactive hZ D
  have resultants:RegularComponentWeightedInertiaResultantCertificate
      U.toPrimeFlagBudgetFamily multiplicity:=by
    exact activeNestedWeightedCertificate base hactive hZ hSderiv D
      S.irreducible_G hfirstProper hGsupport hTsupport multiplicity powers
  have hyzTranscendental:∀ C:FirstTailComponent S,
      Transcendental (GenericField K)
        (coordinateValue (GenericField K) (CoordinateField (GenericField K) C.1)
          (U.yzProjection C)):=by
    intro C
    have hproj:U.yzProjection C=coordinateOfGate
        (ContactFlagAffineFamilyDegree6543Research.affineU
          (GenericField K) C.1 D.lam) (D.uGate C):=rfl
    rw [hproj,coordinateOfGate_value]
    exact D.uTranscendental C
  exact delayedTailMultiplicityProvider_of_certificates S hfirstProper base U
    hyzTranscendental (41*agreements) 1242 11 hnodes hagreement
    (by decide) (by decide) hbox multiplicity
    (one_le_localMultiplicity S hfirstProper)
    (properDelayedTailCertificate S hfirstProper U.toPrimeFlagBudgetFamily)
    resultants
end
end ProximityPrize.SubmissionLower.ContactProperStageActiveProvider6733Research
