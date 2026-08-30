import ProximityPrize.SubmissionLower.P6

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactProperStageActiveProvider6735Research
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
open ContactTwoTailProviderAssembly6735Research
open ContactTwoTailResultantProvider6732Research
open ContactProperDelayedTailCertificate6735Research
open ContactTwoTailFixedSelected6735Research
open ContactTwoTailParameters6735Research
open ContactMovingCurveBudget6719Research
open ContactFirstTailBudget6731Research
open ContactMovingPositiveLedger6719Research
open ContactTerminalAdaptiveProjection6656Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactInterpolation
open ContactTaylorNumerators
open ContactMovingProjection6676Research
open ContactRegularZeroBudget6676Research
open ContactTwoTailRecurrence6731Research
open ContactTwoTailProperBranch6731Research
open ContactTangentCoefficientProvider6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 200000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev Omega:=GenericField K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
local instance:CharP Omega prime:=genericField_charP K prime
theorem firstTail_in_exact_flag
    {Gamma:Finset K} {flag:FlagDegree}
    (S:Stage K I Gamma IRSProfile.domain prime flag):
    PolynomialInFlag exactFirstTailFlag
      (globalTailCut (polynomialEmbedding K) S.F (w+1)):=by
  have heq:exactFirstTailFlag=
      sharpResidualAgreementFlag ContactProperDelayedTailCertificate6735Research.fixedSupport (w+1):=by decide
  rw [heq]
  exact firstTail_in_sharp_flag S

theorem laterTail_in_hybrid_flag
    {Gamma:Finset K} {flag:FlagDegree}
    (S:Stage K I Gamma IRSProfile.domain prime flag)
    (delay multiplicity:ℕ) (hdelay:1 ≤ delay)
    (hdelayMu:delay ≤ multiplicity) (hmu:2 ≤ multiplicity):
    PolynomialInFlag (multiplicity • hybridCoordinateFlag)
      (globalTailCut (polynomialEmbedding K) S.F (w+1+delay)):=by
  let d:=w+1+delay
  have hsharp:PolynomialInFlag
      (ContactSharpTaylorFixedMeet6656Research.sharpResidualAgreementFlag
        ContactProperDelayedTailCertificate6735Research.fixedSupport d)
      (globalTailCut (polynomialEmbedding K) S.F d):=by
    exact surfaceMap_agreement_in_sharp_flag
      (P:=ContactProperDelayedTailCertificate6735Research.fixedSupport) (by decide) (polynomialEmbedding K)
      ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
      d (tailSelector d) 0 0 0
  intro exponent hexponent
  have hs:=hsharp exponent hexponent
  change InFlag (multiplicity • (⟨174983790,6094942,1507351⟩:FlagDegree)) exponent
  change InFlag
    (ContactSharpTaylorFixedMeet6656Research.sharpResidualAgreementFlag
      (support 1335 46 10) (131071+1+delay)) exponent at hs
  norm_num [InFlag,
    ContactSharpTaylorFixedMeet6656Research.sharpResidualAgreementFlag,
    ContactSharpTaylorFixedMeet6656Research.sharpAgreementDirection,
    ContactMovingAgreementCertificate6719Research.support] at hs
  simp only [InFlag,nsmul_zOnly,nsmul_yz,nsmul_all] at ⊢
  omega

theorem component_secondTail_moving_card_le
    {Gamma:Finset K} {flag:FlagDegree}
    (S:Stage K I Gamma IRSProfile.domain prime flag)
    (base:∀ C:FirstTailComponent S,SeparableLiteralCoordinate C.1)
    (M:∀ C:FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (C:FirstTailComponent S)
    (hproper:globalTailCut (polynomialEmbedding K) S.F (w+2)∉C.1):
    (componentSeeds Omega S.G
      (globalTailCut (polynomialEmbedding K) S.F (w+1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
        (M C).weightedCost rationalCoordinateFlag+(w+1)*(M C).movingCost:=by
  let phi:=polynomialEmbedding K
  let T1:=globalTailCut phi S.F (w+1)
  let T2:=globalTailCut phi S.F (w+2)
  let H:=regularitySurface phi S.F
  let G0:=surfaceMap phi (polyG K S.F)
  let Hsupport:ContactResidualSupportParametersResearch.ResidualSupportData
      ContactProperDelayedTailCertificate6735Research.fixedSupport S.F:=
    ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
  obtain ⟨coeffs,cflags,hcut,hcoeff,hclass⟩:=globalTailCut_certificate
    phi 1335 46 10 S.F Hsupport.coordinate_bounds.2.1
      Hsupport.ys_weight Hsupport.total_weight (w+1) (by decide)
  have hcutT:T2=filteredCut (w+1) coeffs H G0:=by
    simpa [T2,H,G0,regularitySurface,polyH,show w+1+1=w+2 by omega] using hcut
  have hfiltered:filteredCut (w+1) coeffs H G0∉C.1:=by
    rwa [←hcutT]
  have hzeroBudget:FiniteRegularZeroSetBound C.1 H
      (filteredCut (w+1) coeffs H G0)
      ((M C).weightedCost (centreFlag 1335 46 10)+
        (w+1)*((M C).weightedCost (normalFlag 1335 46 10)+
          (M C).movingCost)):=by
    exact (M C).zero_le (base C) 1335 46 10 (w+1)
      (centreFlag 1335 46 10) coeffs cflags
      (regularComponent_H_not_mem Omega S.G T1 H C) hfiltered hcoeff hclass
  let seeds:=componentSeeds Omega S.G T1 H Gamma
    (selectedPoint phi S.selected) C
  let points:=seeds.image (selectedPoint phi S.selected)
  have hpointsPrime:∀ v∈points,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
    exact componentSeeds_on_prime Omega S.G T1 H Gamma
      (selectedPoint phi S.selected) C gamma hgamma
  have hpointsRegular:∀ v∈points,MvPolynomial.aeval v H≠0:=by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
    have hGamma:=componentSeeds_subset Omega S.G T1 H Gamma
      (selectedPoint phi S.selected) C hgamma
    change MvPolynomial.eval (selectedPoint phi S.selected gamma)
      (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) S.F))≠0
    rw [selectedPoint_evaluation]
    exact S.regular gamma hGamma
  have hpointsZero:∀ v∈points,
      MvPolynomial.aeval v (filteredCut (w+1) coeffs H G0)=0:=by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
    have hGamma:=componentSeeds_subset Omega S.G T1 H Gamma
      (selectedPoint phi S.selected) C hgamma
    rw [←hcutT]
    exact selected_globalTailCut_zero_of_lt phi S.F S.selected gamma w (w+2)
      (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
  have hbound:=hzeroBudget points hpointsPrime hpointsRegular hpointsZero
  have hcard:points.card=seeds.card:=
    Finset.card_image_of_injective _ (selectedPoint_injective phi S.selected)
  have hcost:
      (M C).weightedCost (centreFlag 1335 46 10)+
          (w+1)*((M C).weightedCost (normalFlag 1335 46 10)+
            (M C).movingCost)=
        (M C).weightedCost rationalCoordinateFlag+(w+1)*(M C).movingCost:=by
    simp only [MovingPoleBudget.weightedCost,centreFlag,directionFlag,
      normalFlag,rationalCoordinateFlag,add_zOnly,add_yz,add_all,
      unitYZFlag,w]
    ring
  simpa only [seeds,hcard,hcost] using hbound

theorem stage_card_le_hybrid
    {Gamma:Finset K} {flag:FlagDegree}
    (S:Stage K I Gamma IRSProfile.domain prime flag)
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (base:∀ C:FirstTailComponent S,SeparableLiteralCoordinate C.1)
    (U:AdaptiveUnitProjectionFamily base flag exactFirstTailFlag)
    (hyzTranscendental:∀ C:FirstTailComponent S,
      Transcendental Omega
        (coordinateValue Omega (CoordinateField Omega C.1) (U.yzProjection C)))
    (M:∀ C:FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (hcost:∀ C,(M C).zCost=U.toPrimeFlagBudgetFamily.zCost C∧
      (M C).yzCost=U.toPrimeFlagBudgetFamily.yzCost C∧
      (M C).allCost=U.toPrimeFlagBudgetFamily.allCost C)
    (hmoving:(∑ C,(M C).movingCost) ≤
      flagMixed flag movingFiberFlag movingCutFlag)
    (resultants:RegularComponentWeightedInertiaResultantCertificate
      U.toPrimeFlagBudgetFamily
        (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)))
    (hnodes:S.nodes.card=agreements+errors)
    (hagreement:∀ gamma∈Gamma,agreements ≤ (S.agreementFiber gamma).card)
    (hbox:S.F∈globalCoefficientBox K (43*agreements) w 1394 12):
    Gamma.card ≤ hybridStageCost flag:=by
  let multiplicity:FirstTailComponent S → ℕ:=
    localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
  have hone:∀ C,1 ≤ multiplicity C:=by
    exact one_le_localMultiplicity S hfirstProper
  let B:=U.toPrimeFlagBudgetFamily
  let T1:=globalTailCut (polynomialEmbedding K) S.F (w+1)
  let H:=regularitySurface (polynomialEmbedding K) S.F
  let point:=selectedPoint (polynomialEmbedding K) S.selected
  let cost:FirstTailComponent S → ℕ:=fun C =>
    multiplicity C*B.weightedCost hybridCoordinateFlag C+
      if multiplicity C=1 then (w+1)*(M C).movingCost else 0
  have hyzPositive (C:FirstTailComponent S):1 ≤ B.yzCost C:=by
    change 1 ≤ coordinateDegree Omega (CoordinateField Omega C.1) (U.yzProjection C)
    exact one_le_coordinateDegree_of_transcendental_value
      (U.yzProjection C) (hyzTranscendental C)
  have hyzPole (C:FirstTailComponent S):∀ W:Finset
      (CoordinatePoleMass.Place Omega (CoordinateField Omega C.1)),
      (∑ v∈W,ContactSparsePoleSupportResearch.exponentSetPoleWeight
        v.val (coordinate Omega C.1) (flagSupport unitYZFlag)) ≤ (B.yzCost C:ℤ):=by
    exact U.toAdaptiveUnitPoleBudget.yzPole C
  have tangentCount (C:FirstTailComponent S)
      (hall:∀ delay,globalTailCut (polynomialEmbedding K) S.F
        (w+1+delay)∈C.1):
      (componentSeeds Omega S.G T1 H Gamma point C).card ≤
        (errors+1)*B.yzCost C:=by
    exact tangent_component_card_le S C hfirstProper (base C)
      agreements (43*agreements) 1394 12 hnodes hagreement
      (by decide) (by decide) (by decide) (by decide) hbox B
      (hyzPositive C) hall (hyzPole C)
  have componentBound (C:FirstTailComponent S):
      (componentSeeds Omega S.G T1 H Gamma point C).card ≤ cost C:=by
    have hd:=local_order_tail_dichotomy S
      (canonicalLocalDVRFamily S hfirstProper) C hfirstProper
    rcases hd.2 with hproper | htangent
    · obtain ⟨delay,hdelay,hdelayMu,hproperTail⟩:=hproper
      change delay ≤ multiplicity C at hdelayMu
      by_cases hmu:multiplicity C=1
      · have hdelayOne:delay=1:=by omega
        subst delay
        have hm:=component_secondTail_moving_card_le S base M C hproperTail
        have hcoordinate:(M C).weightedCost rationalCoordinateFlag ≤
            B.weightedCost hybridCoordinateFlag C:=by
          simp only [MovingPoleBudget.weightedCost,
            PrimeFlagBudgetFamily.weightedCost,B,rationalCoordinateFlag,
            hybridCoordinateFlag,(hcost C).1,(hcost C).2.1,(hcost C).2.2]
          omega
        have hm2:=hm.trans (Nat.add_le_add_right hcoordinate _)
        rw [show cost C=B.weightedCost hybridCoordinateFlag C+
            (w+1)*(M C).movingCost by simp [cost,hmu]]
        simpa [T1,H,point,Omega] using hm2
      · have hmuTwo:2 ≤ multiplicity C:=by omega
        have hflag:=laterTail_in_hybrid_flag S delay (multiplicity C)
          hdelay hdelayMu hmuTwo
        have hzero:∀ gamma∈componentSeeds Omega S.G T1 H Gamma point C,
            MvPolynomial.aeval (point gamma)
              (globalTailCut (polynomialEmbedding K) S.F (w+1+delay))=0:=by
          intro gamma hgamma
          have hGamma:=componentSeeds_subset Omega S.G T1 H Gamma point C hgamma
          exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
            S.selected gamma w (w+1+delay) (S.degree_le gamma hGamma)
              (S.solution gamma hGamma) (by omega)
        have hc:=component_secondTail_card_le B C Gamma point
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflag hproperTail hzero
        have hscale:B.weightedCost
            (multiplicity C • hybridCoordinateFlag) C=
              multiplicity C*B.weightedCost hybridCoordinateFlag C:=by
          simp only [PrimeFlagBudgetFamily.weightedCost,nsmul_zOnly,
            nsmul_yz,nsmul_all]
          ring
        rw [hscale] at hc
        rw [show cost C=multiplicity C*B.weightedCost hybridCoordinateFlag C by
          simp [cost,hmu]]
        simpa [T1,H,point,Omega] using hc
    · have ht:=tangentCount C htangent
      have hfactor:errors+1 ≤ multiplicity C*hybridCoordinateFlag.yz:=by
        rw [show hybridCoordinateFlag.yz=6094942 by rfl]
        have:=hone C
        norm_num [errors] at ⊢
        omega
      have hscaled:(errors+1)*B.yzCost C ≤
          (multiplicity C*hybridCoordinateFlag.yz)*B.yzCost C:=
        Nat.mul_le_mul_right _ hfactor
      have hinside:hybridCoordinateFlag.yz*B.yzCost C ≤
          B.weightedCost hybridCoordinateFlag C:=by
        simp only [PrimeFlagBudgetFamily.weightedCost]
        omega
      have hfinal:(multiplicity C*hybridCoordinateFlag.yz)*B.yzCost C ≤
          multiplicity C*B.weightedCost hybridCoordinateFlag C:=by
        calc
          _=multiplicity C*(hybridCoordinateFlag.yz*B.yzCost C):=by ring
          _ ≤ _:=Nat.mul_le_mul_left _ hinside
      exact (ht.trans (hscaled.trans hfinal)).trans (Nat.le_add_right _ _)
  have hG:∀ gamma∈Gamma,MvPolynomial.eval (point gamma) S.G=0:=S.on_component
  have hT1:∀ gamma∈Gamma,MvPolynomial.eval (point gamma) T1=0:=by
    intro gamma hgamma
    exact selected_globalTailCut_zero (polynomialEmbedding K) S.F S.selected gamma w
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hH:∀ gamma∈Gamma,MvPolynomial.eval (point gamma) H≠0:=by
    intro gamma hgamma
    change MvPolynomial.eval (point gamma)
      (surfaceMap (polynomialEmbedding K)
        (MvPolynomial.pderiv (2:Fin 4) S.F))≠0
    rw [selectedPoint_evaluation]
    exact S.regular gamma hgamma
  have hcover:=card_le_sum_componentSeeds Omega S.G T1 H Gamma point hG hT1 hH
  have hcoordinate:
      (∑ C,multiplicity C*B.weightedCost hybridCoordinateFlag C) ≤
        flagMixed flag exactFirstTailFlag hybridCoordinateFlag:=
    resultants.divisor_le B multiplicity
  have hmovingPart:
      (∑ C,if multiplicity C=1 then (w+1)*(M C).movingCost else 0) ≤
        (w+1)*flagMixed flag movingFiberFlag movingCutFlag:=by
    calc
      _ ≤ ∑ C,(w+1)*(M C).movingCost:=by
        apply Finset.sum_le_sum
        intro C _
        split_ifs <;> omega
      _=(w+1)*(∑ C,(M C).movingCost):=by rw [Finset.mul_sum]
      _ ≤ _:=Nat.mul_le_mul_left _ hmoving
  calc
    Gamma.card ≤ ∑ C:FirstTailComponent S,
        (componentSeeds Omega S.G T1 H Gamma point C).card:=hcover
    _ ≤ ∑ C:FirstTailComponent S,cost C:=
      Finset.sum_le_sum (fun C _↦componentBound C)
    _=(∑ C,multiplicity C*B.weightedCost hybridCoordinateFlag C)+
        ∑ C,if multiplicity C=1 then (w+1)*(M C).movingCost else 0:=by
      simp only [cost,Finset.sum_add_distrib]
    _ ≤ flagMixed flag exactFirstTailFlag hybridCoordinateFlag+
        (w+1)*flagMixed flag movingFiberFlag movingCutFlag:=
      Nat.add_le_add hcoordinate hmovingPart
    _=hybridStageCost flag:=rfl
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
        ContactProperDelayedTailCertificate6735Research.fixedSupport (w+1)).all ≤
        (tailFlag (w+1)).all:=by decide
  have hYZ:
      (sharpResidualAgreementFlag
          ContactProperDelayedTailCertificate6735Research.fixedSupport (w+1)).yz+
          (sharpResidualAgreementFlag
            ContactProperDelayedTailCertificate6735Research.fixedSupport (w+1)).all ≤
        (tailFlag (w+1)).yz+(tailFlag (w+1)).all:=by decide
  have hTotal:
      (sharpResidualAgreementFlag
          ContactProperDelayedTailCertificate6735Research.fixedSupport (w+1)).zOnly+
          (sharpResidualAgreementFlag
            ContactProperDelayedTailCertificate6735Research.fixedSupport (w+1)).yz+
          (sharpResidualAgreementFlag
            ContactProperDelayedTailCertificate6735Research.fixedSupport (w+1)).all ≤
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
      (1+(w+1)*(2*(46+10+3)-2))*flag.all+
        (flag.yz+flag.all)*((2*(10+2)-1)*(w+1)) < prime:=by
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
        flagSupport exactFirstTailFlag:=
    (support_subset_flagSupport_iff _ _).2 (firstTail_in_exact_flag S)
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
  let E:=AlgebraicClosure (RatFunc (GenericField K))
  letI:IsScalarTower (GenericField K) (RatFunc (GenericField K)) E:=by
    infer_instance
  letI:CharP E prime:=by infer_instance
  let Hsupport:ContactResidualSupportParametersResearch.ResidualSupportData
      ContactProperDelayedTailCertificate6735Research.fixedSupport S.F:=
    ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
  have hmix:
      2*(flag.zOnly+flag.yz+flag.all)*(1335+46+10+4)<prime:=by
    rcases hflag with ⟨hall,hyz,htotal⟩
    norm_num [prime] at ⊢
    omega
  obtain ⟨M,hcost,hz,hyz,hall,hmove⟩:=
    exists_firstTail_cut_budgets (E:=E)
      (polynomialEmbedding K) S.F S.G
      (globalTailCut (polynomialEmbedding K) S.F (w+1))
      1335 46 10 w (by decide) rfl Hsupport flag
      S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
      base U prime hmix
  have hfiber:
      ContactMovingPositiveLedger6719Research.fiberFlag 1335 46 10=
        movingFiberFlag:=by decide
  have hcut:
      ContactMovingAgreementCertificate6719Research.center 1335 46 10+
          (w+1) • ContactMovingPositiveLedger6719Research.surfaceFlag
            1335 46 10=movingCutFlag:=by decide
  have hmoveExact:
      (∑ C,(M C).movingCost) ≤
        flagMixed flag movingFiberFlag movingCutFlag:=by
    simpa only [hfiber,hcut] using hmove
  exact stage_card_le_hybrid S hfirstProper base U hyzTranscendental
    M hcost hmoveExact resultants hnodes hagreement hbox
end
end ProximityPrize.SubmissionLower.ContactProperStageActiveProvider6735Research
end
