import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch
import ProximityPrize.SubmissionLower.ContactTwoTailFixedStage6733Research
import ProximityPrize.SubmissionLower.ContactTwoTailIdentityStage6733Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredOrdinaryFixedCell6750Research

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactGenericInitialPoint ContactGenericSurface
open ContactFirstTailCertificate6731Research
open ContactFactorCaps
open ContactTaylorNumerators ContactIdentityResidualGlobalFlagResearch
open ContactFlagBezout6543Research ContactPrimeSeedIncidence
open ContactProperCutSeedCount ContactOriginalRegularSeedCount
open ContactRegularFactorFlag6600Research
open ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorResidualStage6600Research
open ContactGlobalSelectedFamilies6600Research
open ContactResidualSupportParametersResearch
open ContactIdentityResidualIterationResearch
open ContactGCDCumulativeFlagsResearch ContactFactoredFlagCount6676Research
open ContactGeometricFactorCover ContactRobustFixedMeet6656Research
open ContactProfileFixedSelectedCombinerResearch
open ContactTightSingularLedgerResearch
open ContactDelayedTailMultiplicityProvider6732Research
open ContactTwoTailParameters6750Research
open ContactRouterCellCosts6750Research
open ContactMovingAgreementCertificate6719Research
open ContactMovingOuterBudget6719Research
open ContactIdentityCurveProvider6731Research
open ContactFirstTailIdentityIncidence6731Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600

 

def ordinaryProfileD (D t r : Nat) :
    ContactRobustFixedMeet6656Research.Profile :=
  ⟨n, w, agreements, D, t, r⟩

abbrev ordinaryProfile (t r : Nat) := ordinaryProfileD profileA.weightedCap t r

def ordinaryAlignmentD (D t r : Nat) :
    FixedParameterAlignment (ordinaryProfileD D t r)
      (cellTightProfile D t r) where
  n := rfl
  w := rfl
  agreements := rfl
  weightedCap := rfl
  seedTotalCap := rfl
  slopeCap := rfl

abbrev ordinaryAlignment (t r : Nat) :=
  ordinaryAlignmentD profileA.weightedCap t r

 
theorem cellSupport_of_dvd
    (t y r : Nat) (F Q : MvPolynomial (Fin 4) K)
    (hQ : Q ≠ 0) (hdiv : F ∣ Q)
    (Hsupport : ResidualSupportData (cellSupport t y r) Q) :
    ResidualSupportData (cellSupport t y r) F :=
  ⟨(weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans
      Hsupport.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights F Q hdiv hQ).trans
      Hsupport.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans
      Hsupport.total_weight⟩

 
def cellGeometricStageD
    (D t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D w t r)
    (Hsupport : ResidualSupportData (cellSupport t y r) Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      IRSProfile.domain prime errors (geometricCumulativeFlag K g) w
      (cellSupport t y r) := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hRdata := directFactor_data Q R.1 hQ D w t r hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < prime :=
    (degreeOf_R_le_of_mem_box R.1 D w t r
      hRdata.2.2).trans_lt (hr.trans_lt (by norm_num [prime]))
  have hsupport : ResidualSupportData (cellSupport t y r) R.1 :=
    cellSupport_of_dvd t y r R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1
      Hsupport
  let S := regularGeometricResidualStageOfSupport (cellSupport t y r) Q
    selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn hdegree hnoPencil R
    hRdata.1 hRdata.2.1 hRsmall hsupport (by norm_num [prime, w]) g
  exact reflagResidualStage S (polynomialIn_surfaceCumulativeFlag g.1)

abbrev cellGeometricStage := cellGeometricStageD profileA.weightedCap

theorem cellGeometricStageD_flag_caps
    (D t y r : Nat) (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D w t r)
    (Hsupport : ResidualSupportData (cellSupport t y r) Q)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    (geometricCumulativeFlag K g).all ≤ r ∧
      (geometricCumulativeFlag K g).yz +
          (geometricCumulativeFlag K g).all ≤ y ∧
      (geometricCumulativeFlag K g).zOnly +
          (geometricCumulativeFlag K g).yz +
          (geometricCumulativeFlag K g).all ≤ t := by
  have hRdata := directFactor_data Q R.1 hQ D w t r hbox R.2
  have hcaps := geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero
    (cellSupport_of_dvd t y r R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1
      Hsupport) g
  have hs : (cellSupport t y r).s = r := by
    simp only [cellSupport, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  have hys : (cellSupport t y r).ys = y := by
    simp only [cellSupport, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  have htotal : (cellSupport t y r).total = t := by
    simp only [cellSupport, cellA, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  simpa only [hs, hys, htotal] using hcaps

abbrev cellGeometricStage_flag_caps :=
  cellGeometricStageD_flag_caps profileA.weightedCap

 

def ProperStageProviderD6750 (D t y r : Nat) : Prop :=
  ∀ {Gamma : Finset K} {flag : FlagDegree}
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain prime
      errors flag w (cellSupport t y r)),
    ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1) →
    S.nodes.card = agreements + errors →
    (∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card) →
    S.F ∈ globalCoefficientBox K D w t r →
    (flag.all ≤ r ∧ flag.yz + flag.all ≤ y ∧
      flag.zOnly + flag.yz + flag.all ≤ t) →
    Nonempty (DelayedTailMultiplicityProvider
      (tailFlag1 := cellFirstTail t y r)
      (tailFlag2 := cellSecondTail t y r) S)

abbrev ProperStageProvider6750 := ProperStageProviderD6750 profileA.weightedCap

 

def IdentityCellBudget6750 (t y r : Nat) : Prop :=
  ∀ flag : FlagDegree,
    flag.all ≤ r → flag.yz + flag.all ≤ y →
    flag.zOnly + flag.yz + flag.all ≤ t →
    (n - w) * (errors + 1) *
        identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w ≤
      gap * flagMixed flag (cellFirstTail t y r) (cellSecondTail t y r)

 

structure IdentityCellBasisBudget6750 (t y r : Nat) : Prop where
  zOnly :
    (n - w) * (errors + 1) *
        identityCurveDegree unitZFlag (cellA t y) (cellB y r) (cellS r) w ≤
      gap * flagMixed unitZFlag (cellFirstTail t y r) (cellSecondTail t y r)
  yz :
    (n - w) * (errors + 1) *
        identityCurveDegree unitYZFlag (cellA t y) (cellB y r) (cellS r) w ≤
      gap * flagMixed unitYZFlag (cellFirstTail t y r) (cellSecondTail t y r)
  all :
    (n - w) * (errors + 1) *
        identityCurveDegree unitAllFlag (cellA t y) (cellB y r) (cellS r) w ≤
      gap * flagMixed unitAllFlag (cellFirstTail t y r) (cellSecondTail t y r)

theorem identityCellBudget_of_basis
    {t y r : Nat} (h : IdentityCellBasisBudget6750 t y r) :
    IdentityCellBudget6750 t y r := by
  intro flag _ _ _
  have hz := Nat.mul_le_mul_left flag.zOnly h.zOnly
  have hyz := Nat.mul_le_mul_left flag.yz h.yz
  have hall := Nat.mul_le_mul_left flag.all h.all
  calc
    (n - w) * (errors + 1) *
        identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w =
      flag.zOnly * ((n - w) * (errors + 1) *
          identityCurveDegree unitZFlag (cellA t y) (cellB y r)
            (cellS r) w) +
      flag.yz * ((n - w) * (errors + 1) *
          identityCurveDegree unitYZFlag (cellA t y) (cellB y r)
            (cellS r) w) +
      flag.all * ((n - w) * (errors + 1) *
          identityCurveDegree unitAllFlag (cellA t y) (cellB y r)
            (cellS r) w) := by
        simp only [identityCurveDegree, paddedCut,
          ContactMovingPositiveLedger6719Research.centreFlag,
          ContactMovingPositiveLedger6719Research.directionFlag,
          flagMixed, unitZFlag, unitYZFlag, unitAllFlag,
          add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
        ring
    _ ≤ flag.zOnly * (gap * flagMixed unitZFlag
          (cellFirstTail t y r) (cellSecondTail t y r)) +
        flag.yz * (gap * flagMixed unitYZFlag
          (cellFirstTail t y r) (cellSecondTail t y r)) +
        flag.all * (gap * flagMixed unitAllFlag
          (cellFirstTail t y r) (cellSecondTail t y r)) :=
      Nat.add_le_add (Nat.add_le_add hz hyz) hall
    _ = gap * flagMixed flag (cellFirstTail t y r)
        (cellSecondTail t y r) := by
      simp only [flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
      ring

 



theorem identityBasisBudget_of_basic_cell_analytic
    (t y r : Nat) (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t) :
    IdentityCellBasisBudget6750 t y r := by
  let a := cellA t y
  let b := cellB y r
  let s := cellS r
  have ht : a + b + s + 3 = t := by
    simp only [a, b, s, cellA, cellB, cellS]
    omega
  have hy : b + s + 3 = y := by
    simp only [b, s, cellB, cellS]
    omega
  have hr : s + 2 = r := by
    simp only [s, cellS]
    omega
  have ha : cellA (a + b + s + 3) (b + s + 3) = a := by
    unfold cellA
    omega
  have hb : cellB (b + s + 3) (s + 2) = b := by
    unfold cellB
    omega
  have hs : cellS (s + 2) = s := by
    unfold cellS
    omega
  have hsupport : cellSupport (a + b + s + 3) (b + s + 3) (s + 2) =
      ContactMovingAgreementCertificate6719Research.support a b s := by
    simp only [cellSupport, ha, hb, hs]
  have hta : a + b + s + 3 - (b + s + 3) = a := by omega
  have hyb : b + s + 3 - (s + 2) = b + 1 := by omega
  have hrs : 2 * (s + 2) - 2 = 2 * s + 2 := by omega
  have hbasis : IdentityCellBasisBudget6750
      (a + b + s + 3) (b + s + 3) (s + 2) := by
    constructor
    · norm_num [identityCurveDegree, paddedCut,
        ContactMovingPositiveLedger6719Research.centreFlag,
        ContactMovingPositiveLedger6719Research.directionFlag, flagMixed,
        unitZFlag, unitYZFlag, unitAllFlag,
        cellFirstTail, cellSecondTail, hsupport,
        ContactAnchoredDelayedTailProviderAdapter6750Research.reducedResidualAgreementFlag6750,
        ContactAnchoredDelayedTailProviderAdapter6750Research.reducedAgreementDirection6750,
        ContactMovingAgreementCertificate6719Research.support,
        ha, hb, hs, hta, hyb, hrs, n, w, errors, agreements, gap]
      nlinarith
    · norm_num [identityCurveDegree, paddedCut,
        ContactMovingPositiveLedger6719Research.centreFlag,
        ContactMovingPositiveLedger6719Research.directionFlag, flagMixed,
        unitZFlag, unitYZFlag, unitAllFlag,
        cellFirstTail, cellSecondTail, hsupport,
        ContactAnchoredDelayedTailProviderAdapter6750Research.reducedResidualAgreementFlag6750,
        ContactAnchoredDelayedTailProviderAdapter6750Research.reducedAgreementDirection6750,
        ContactMovingAgreementCertificate6719Research.support,
        ha, hb, hs, hta, hyb, hrs, n, w, errors, agreements, gap]
      nlinarith
    · norm_num [identityCurveDegree, paddedCut,
        ContactMovingPositiveLedger6719Research.centreFlag,
        ContactMovingPositiveLedger6719Research.directionFlag, flagMixed,
        unitZFlag, unitYZFlag, unitAllFlag,
        cellFirstTail, cellSecondTail, hsupport,
        ContactAnchoredDelayedTailProviderAdapter6750Research.reducedResidualAgreementFlag6750,
        ContactAnchoredDelayedTailProviderAdapter6750Research.reducedAgreementDirection6750,
        ContactMovingAgreementCertificate6719Research.support,
        ha, hb, hs, hta, hyb, hrs, n, w, errors, agreements, gap]
      nlinarith
  simpa only [ht, hy, hr] using hbasis

 
theorem identity_stage_card_leD
    {Gamma : Finset K} {flag : FlagDegree}
    (D t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (hbudget : IdentityCellBudget6750 t y r)
    (hDshort : w + 1 ≤ D) (hDchar : D < prime)
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain prime
      errors flag w (cellSupport t y r))
    (hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
    (hnodes : S.nodes.card = agreements + errors)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz + flag.all ≤ y ∧
      flag.zOnly + flag.yz + flag.all ≤ t) :
    Gamma.card ≤ flagMixed flag (cellFirstTail t y r)
      (cellSecondTail t y r) := by
  have hTailNumerator : S.G ∣ surfaceMap (polynomialEmbedding K)
      (numerator K S.F (w + 1)) :=
    (globalTailCut_dvd_iff (polynomialEmbedding K)
      (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
  have hflagChar : flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime := by
    norm_num [prime]
    omega
  have hmixed :
      (1 + w * (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
        (flag.yz + flag.all) * ((2 * (cellS r + 2) - 1) * w) < prime := by
    have hb : cellB y r + cellS r + 3 = y := by
      simp only [cellB, cellS]
      omega
    have hs : cellS r + 2 = r := by
      simp only [cellS]
      omega
    rw [hb, hs]
    have hy' : 2 * y - 2 ≤ 128 := by omega
    have hr' : 2 * r - 1 ≤ 27 := by omega
    have h1 : (1 + w * (2 * y - 2)) * flag.all ≤
        (1 + w * 128) * 14 :=
      Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left w hy') 1)
        (hflag.1.trans hr)
    have h2 : (flag.yz + flag.all) * ((2 * r - 1) * w) ≤
        65 * (27 * w) :=
      Nat.mul_le_mul (hflag.2.1.trans hy)
        (Nat.mul_le_mul_right w hr')
    exact (Nat.add_le_add h1 h2).trans_lt (by norm_num [w, prime])
  have hprovider := actual_identityCurveCountProvider S agreements hnodes
    hagreement (by norm_num [w, agreements, n, errors]) hTailNumerator
    D t r (by norm_num [w])
    hDshort hDchar
    hbox hflagChar hmixed
  let identityDegree := identityCurveDegree flag
    (cellA t y) (cellB y r) (cellS r) w
  have hpositive : 1 ≤ identityDegree := by
    have hyG : 0 < S.G.degreeOf 1 := S.y_dependent
    have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
    have htotal : 1 ≤ flag.zOnly + flag.yz + flag.all := hyG.trans_le hdeg
    have hbz : 1 ≤ identityCurveDegree unitZFlag
        (cellA t y) (cellB y r) (cellS r) w := by
      unfold identityCurveDegree
      simp only [flagMixed, paddedCut,
        ContactMovingPositiveLedger6719Research.centreFlag,
        ContactMovingPositiveLedger6719Research.directionFlag,
        unitZFlag, unitYZFlag, unitAllFlag, add_zOnly, add_yz, add_all,
        nsmul_zOnly, nsmul_yz, nsmul_all]
      omega
    have hbyz : 1 ≤ identityCurveDegree unitYZFlag
        (cellA t y) (cellB y r) (cellS r) w := by
      unfold identityCurveDegree
      simp only [flagMixed, paddedCut,
        ContactMovingPositiveLedger6719Research.centreFlag,
        ContactMovingPositiveLedger6719Research.directionFlag,
        unitZFlag, unitYZFlag, unitAllFlag, add_zOnly, add_yz, add_all,
        nsmul_zOnly, nsmul_yz, nsmul_all]
      omega
    have hball : 1 ≤ identityCurveDegree unitAllFlag
        (cellA t y) (cellB y r) (cellS r) w := by
      unfold identityCurveDegree
      simp only [flagMixed, paddedCut,
        ContactMovingPositiveLedger6719Research.centreFlag,
        ContactMovingPositiveLedger6719Research.directionFlag,
        unitZFlag, unitYZFlag, unitAllFlag, add_zOnly, add_yz, add_all,
        nsmul_zOnly, nsmul_yz, nsmul_all]
      omega
    have hz := Nat.le_mul_of_pos_right flag.zOnly hbz
    have hyz := Nat.le_mul_of_pos_right flag.yz hbyz
    have hall := Nat.le_mul_of_pos_right flag.all hball
    apply htotal.trans
    calc
      flag.zOnly + flag.yz + flag.all ≤
          flag.zOnly * identityCurveDegree unitZFlag
              (cellA t y) (cellB y r) (cellS r) w +
            flag.yz * identityCurveDegree unitYZFlag
              (cellA t y) (cellB y r) (cellS r) w +
            flag.all * identityCurveDegree unitAllFlag
              (cellA t y) (cellB y r) (cellS r) w :=
        Nat.add_le_add (Nat.add_le_add hz hyz) hall
      _ = identityDegree := by
        unfold identityDegree identityCurveDegree
        simp only [flagMixed, paddedCut,
          ContactMovingPositiveLedger6719Research.centreFlag,
          ContactMovingPositiveLedger6719Research.directionFlag,
          unitZFlag, unitYZFlag, unitAllFlag, add_zOnly, add_yz, add_all,
          nsmul_zOnly, nsmul_yz, nsmul_all]
        ring
  have hinc := identity_surface_seed_bound S agreements identityDegree
    hprovider hagreement (by norm_num [w, agreements, n, errors])
    (by rw [hnodes]; norm_num [n, agreements, errors]) hpositive
  have hscaled : Gamma.card * gap ≤
      gap * flagMixed flag (cellFirstTail t y r) (cellSecondTail t y r) := by
    calc
      Gamma.card * gap = Gamma.card * (agreements - w) := rfl
      _ ≤ (S.nodes.card - w) * (errors + 1) * identityDegree := hinc
      _ = (n - w) * (errors + 1) * identityDegree := by
        rw [hnodes]
        norm_num [n, agreements, errors]
      _ ≤ gap * flagMixed flag (cellFirstTail t y r)
          (cellSecondTail t y r) := hbudget flag hflag.1 hflag.2.1 hflag.2.2
  exact Nat.le_of_mul_le_mul_right
    (by simpa only [Nat.mul_comm] using hscaled)
    (by norm_num [gap, agreements, n, errors, w])

theorem identity_stage_card_le
    {Gamma : Finset K} {flag : FlagDegree}
    (t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (hbudget : IdentityCellBudget6750 t y r)
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain prime
      errors flag w (cellSupport t y r))
    (hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
    (hnodes : S.nodes.card = agreements + errors)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K profileA.weightedCap w t r)
    (hflag : flag.all ≤ r ∧ flag.yz + flag.all ≤ y ∧
      flag.zOnly + flag.yz + flag.all ≤ t) :
    Gamma.card ≤ flagMixed flag (cellFirstTail t y r)
      (cellSecondTail t y r) := by
  exact identity_stage_card_leD profileA.weightedCap t y r ht hy hr hr2 hry
    hyt hbudget (by norm_num [w, agreements, n, errors, profileA,
      ContactTwoTailParameters6750Research.Profile.weightedCap])
    (by norm_num [prime, agreements, n, errors, profileA,
      ContactTwoTailParameters6750Research.Profile.weightedCap]) S hTail hnodes
    hagreement hbox hflag

 

theorem regular_factor_seed_boundD
    (D t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (proper : ProperStageProviderD6750 D t y r)
    (identityBudget : IdentityCellBudget6750 t y r)
    (hDshort : w + 1 ≤ D) (hDchar : D < prime)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D w t r)
    (Hsupport : ResidualSupportData (cellSupport t y r) Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤
      flagMixed (regularCumulativeFlag Q R)
        (cellFirstTail t y r) (cellSecondTail t y r) := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hRdata := directFactor_data Q R.1 hQ D w t r hbox R.2
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover := card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage : ∀ g : GeometricFactor K R.1,
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        flagMixed (geometricCumulativeFlag K g)
          (cellFirstTail t y r) (cellSecondTail t y r) := by
    intro g
    let S := cellGeometricStageD D t y r ht hy hr hr2 hry hyt
      Q hQ hbox Hsupport selected Gamma u0 u1 hdegree hnoPencil R g
    have hsub : geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
      (geometricSeeds_subset K R.1 selected
        (regularSeeds Q selected Gamma R) g).trans
          (regularSeeds_subset Q selected Gamma R)
    have hnodesS : S.nodes.card = agreements + errors := by
      change (Finset.univ : Finset I).card = agreements + errors
      norm_num [I, agreements, errors, n]
    have hagreementS : ∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,
        agreements ≤ (S.agreementFiber gamma).card := by
      intro gamma hgamma
      simpa [S, ResidualStage.agreementFiber, ResidualStage.Agrees,
        cellGeometricStageD, reflagResidualStage,
        regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using
          hagreement gamma (hsub hgamma)
    have hflag := cellGeometricStageD_flag_caps D t y r hr2 hry hyt
      Q hQ hbox Hsupport R g
    have hboxS : S.F ∈ globalCoefficientBox K D w t r := by
      change R.1 ∈ globalCoefficientBox K D w t r
      exact hRdata.2.2
    by_cases htail : S.G ∣
        globalTailCut (polynomialEmbedding K) S.F (w + 1)
    · exact identity_stage_card_leD D t y r ht hy hr hr2 hry hyt
        identityBudget hDshort hDchar S htail hnodesS hagreementS hboxS hflag
    · exact stage_card_le_flagMixed S
        (proper S htail hnodesS hagreementS hboxS hflag).some
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g : GeometricFactor K R.1,
          (geometricSeeds K R.1 selected
            (regularSeeds Q selected Gamma R) g).card := hcover
    _ ≤ ∑ g : GeometricFactor K R.1,
        flagMixed (geometricCumulativeFlag K g)
          (cellFirstTail t y r) (cellSecondTail t y r) :=
      Finset.sum_le_sum (fun g _ ↦ hstage g)
    _ ≤ flagMixed (originalCumulativeFlag R.1)
        (cellFirstTail t y r) (cellSecondTail t y r) := by
      have hc := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
        (originalCumulativeFlag R.1) _ _ hc.1 hc.2.1 hc.2.2

theorem regular_factor_seed_bound
    (t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (proper : ProperStageProvider6750 t y r)
    (identityBudget : IdentityCellBudget6750 t y r)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K profileA.weightedCap w t r)
    (Hsupport : ResidualSupportData (cellSupport t y r) Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤
      flagMixed (regularCumulativeFlag Q R)
        (cellFirstTail t y r) (cellSecondTail t y r) := by
  exact regular_factor_seed_boundD profileA.weightedCap t y r ht hy hr hr2 hry
    hyt proper identityBudget
    (by norm_num [w, agreements, n, errors, profileA,
      ContactTwoTailParameters6750Research.Profile.weightedCap])
    (by norm_num [prime, agreements, n, errors, profileA,
      ContactTwoTailParameters6750Research.Profile.weightedCap]) Q hQ hbox Hsupport
    selected Gamma u0 u1 hdegree hagreement hnoPencil R

 
structure OrdinaryCellCombinerGatesD6750 (D t r : Nat) : Prop where
  slope_pos : 1 ≤ r
  slope_lt_char : r < prime
  w_pos : 1 ≤ w
  w_lt_char : w < prime
  weighted_nontrivial : w < (2 * r - 1) * D
  algebraic_pos : 1 ≤ (2 * r - 1) * t
  algebraic_lt_char : (2 * r - 1) * t < prime
  implicitY_lt_char :
    (cellTightProfile D t r).implicitYCap < prime
  mixed_lt_char :
    2 * (cellTightProfile D t r).implicitYCap *
      (cellTightProfile D t r).algebraicCap < prime
  w_lt_agreements : w < agreements
  agreements_le_n : agreements ≤ n

abbrev OrdinaryCellCombinerGates6750 :=
  OrdinaryCellCombinerGatesD6750 profileA.weightedCap

 


theorem combinerGatesD_of_bounds_analytic
    (D t r : Nat) (hDlo : w + 1 ≤ D) (hDhi : D ≤ profileA.weightedCap)
    (htLo : 1 ≤ t) (htHi : t ≤ 2530)
    (hrLo : 1 ≤ r) (hrHi : r ≤ 14) :
    OrdinaryCellCombinerGatesD6750 D t r := by
  have hkLo : 1 ≤ 2 * r - 1 := by omega
  have hkHi : 2 * r - 1 ≤ 27 := by omega
  have hDnum : D ≤ 8548548 := by
    simpa [profileA, ContactTwoTailParameters6750Research.Profile.weightedCap,
      agreements, n, errors] using hDhi
  have hkD : (2 * r - 1) * D ≤ 27 * 8548548 :=
    Nat.mul_le_mul hkHi hDnum
  have himp : (cellTightProfile D t r).implicitYCap ≤ 1761 := by
    simp only [cellTightProfile,
      ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa]
    rw [← Nat.lt_succ_iff]
    apply (Nat.div_lt_iff_lt_mul (by norm_num [w])).mpr
    norm_num [w]
    omega
  have halg : (cellTightProfile D t r).algebraicCap ≤ 68310 := by
    simp only [cellTightProfile,
      ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa]
    exact (Nat.mul_le_mul hkHi htHi).trans (by norm_num)
  refine ⟨hrLo, hrHi.trans_lt (by norm_num [prime]),
    by norm_num [w], by norm_num [w, prime], ?_, htLo.trans ?_, ?_,
    himp.trans_lt (by norm_num [prime]), ?_,
    by norm_num [w, agreements, n, errors],
    by norm_num [agreements, n, errors]⟩
  · have hDw : w < D := by omega
    nlinarith
  · exact Nat.le_mul_of_pos_left _ hkLo
  · exact (Nat.mul_le_mul hkHi htHi).trans_lt (by norm_num [prime])
  · exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 himp) halg).trans_lt
      (by norm_num [prime])

 


theorem cell_count_le_mixedReplacementCostD
    (D t y r tightT tightR : Nat)
    (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (proper : ProperStageProviderD6750 D t y r)
    (identityBudget : IdentityCellBudget6750 t y r)
    (hDshort : w + 1 ≤ D) (hDchar : D < prime)
    (gates : OrdinaryCellCombinerGatesD6750 D tightT tightR)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hboxTight : Q ∈ globalCoefficientBox K D w tightT tightR)
    (hboxCell : Q ∈ globalCoefficientBox K D w t r)
    (Hsupport : ResidualSupportData (cellSupport t y r) Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (u0 u1 : I → K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card ≤ cellRegularCost t y r +
      (cellTightProfile D tightT tightR).countCap := by
  let nodes : Finset I := Finset.univ
  have hinj : Set.InjOn IRSProfile.domain nodes :=
    IRSProfile.domain.injective.injOn
  have hnodes : nodes.card = (ordinaryProfileD D tightT tightR).n := by
    change Fintype.card I = n
    norm_num [I, n]
  have h := global_count_le_regular_div_add_tight_countCap
    (ordinaryProfileD D tightT tightR) (cellTightProfile D tightT tightR)
    (ordinaryAlignmentD D tightT tightR)
    (prime := prime) (regularNumerator := cellRegularCost t y r * gap ^ 2)
    Q hQ hboxTight gates.slope_pos gates.slope_lt_char gates.w_pos
    gates.w_lt_char gates.weighted_nontrivial gates.algebraic_pos
    gates.algebraic_lt_char gates.implicitY_lt_char gates.mixed_lt_char
    gates.w_lt_agreements gates.agreements_le_n selected Gamma nodes
    IRSProfile.domain u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
    (regularCumulativeFlag Q)
    (fun f ↦ flagMixed f (cellFirstTail t y r) (cellSecondTail t y r) *
      gap ^ 2)
    (fun count hcount ↦ by
      have hc := regularCumulativeFlag_budgets Q hQ Hsupport
      have hs :
          (ContactMovingPositiveLedger6719Research.surfaceFlag
            (cellA t y) (cellB y r) (cellS r)).all =
            (cellSupport t y r).s := by
        rfl
      have hys :
          (ContactMovingPositiveLedger6719Research.surfaceFlag
              (cellA t y) (cellB y r) (cellS r)).yz +
            (ContactMovingPositiveLedger6719Research.surfaceFlag
              (cellA t y) (cellB y r) (cellS r)).all =
            (cellSupport t y r).ys := by
        simp only [ContactMovingPositiveLedger6719Research.surfaceFlag,
          cellSupport, ContactMovingAgreementCertificate6719Research.support]
        omega
      have htotal :
          (ContactMovingPositiveLedger6719Research.surfaceFlag
              (cellA t y) (cellB y r) (cellS r)).zOnly +
            (ContactMovingPositiveLedger6719Research.surfaceFlag
              (cellA t y) (cellB y r) (cellS r)).yz +
            (ContactMovingPositiveLedger6719Research.surfaceFlag
              (cellA t y) (cellB y r) (cellS r)).all =
            (cellSupport t y r).total := by
        simp only [ContactMovingPositiveLedger6719Research.surfaceFlag,
          cellSupport, ContactMovingAgreementCertificate6719Research.support]
        omega
      calc
        (∑ R, count R) * gap ^ 2 = ∑ R, count R * gap ^ 2 := by
          rw [Finset.sum_mul]
        _ ≤ ∑ R, flagMixed (regularCumulativeFlag Q R)
              (cellFirstTail t y r) (cellSecondTail t y r) * gap ^ 2 :=
          Finset.sum_le_sum (fun R _ ↦ hcount R)
        _ = (∑ R, flagMixed (regularCumulativeFlag Q R)
              (cellFirstTail t y r) (cellSecondTail t y r)) * gap ^ 2 := by
          rw [Finset.sum_mul]
        _ ≤ cellRegularCost t y r * gap ^ 2 :=
          Nat.mul_le_mul_right _ (by
            unfold cellRegularCost cellFixedFlag
            exact sum_flagMixed_le_of_cumulative (regularCumulativeFlag Q)
              (ContactMovingPositiveLedger6719Research.surfaceFlag
                (cellA t y) (cellB y r) (cellS r)) _ _
              (by simpa only [hs] using hc.1)
              (by simpa only [hys] using hc.2.1)
              (by simpa only [htotal] using hc.2.2)))
    (fun R ↦ by
      exact Nat.mul_le_mul_right (gap ^ 2)
        (regular_factor_seed_boundD D t y r ht hy hr hr2 hry hyt
          proper identityBudget hDshort hDchar Q hQ hboxCell Hsupport selected Gamma u0 u1
          hdegree hagreement hnoPencil R))
  have hgap : 0 < gap := by norm_num [gap, agreements, n, errors, w]
  rw [show (ordinaryProfileD D tightT tightR).gap = gap by rfl,
    Nat.mul_div_left _ (pow_pos hgap 2)] at h
  change Gamma.card ≤ cellRegularCost t y r +
    (cellTightProfile D tightT tightR).countCap
  exact h

 

theorem cell_count_le_ordinaryReplacementCostD
    (D t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (proper : ProperStageProviderD6750 D t y r)
    (identityBudget : IdentityCellBudget6750 t y r)
    (hDshort : w + 1 ≤ D) (hDchar : D < prime)
    (gates : OrdinaryCellCombinerGatesD6750 D t r)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D w t r)
    (Hsupport : ResidualSupportData (cellSupport t y r) Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (u0 u1 : I → K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card ≤ cellRegularCost t y r +
      (cellTightProfile D t r).countCap :=
  cell_count_le_mixedReplacementCostD D t y r t r ht hy hr hr2 hry hyt
    proper identityBudget hDshort hDchar gates Q hQ hbox hbox Hsupport
    selected Gamma u0 u1 hsolution hdegree hagreement hnoPencil

 
theorem cell_count_le_ordinaryReplacementCost
    (t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (proper : ProperStageProvider6750 t y r)
    (identityBudget : IdentityCellBudget6750 t y r)
    (gates : OrdinaryCellCombinerGates6750 t r)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K profileA.weightedCap w t r)
    (Hsupport : ResidualSupportData (cellSupport t y r) Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (u0 u1 : I → K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card ≤ ordinaryReplacementCost t y r := by
  simpa only [ordinaryReplacementCost] using
    cell_count_le_ordinaryReplacementCostD profileA.weightedCap t y r ht
    hy hr hr2 hry hyt proper identityBudget
    (by norm_num [w, agreements, n, errors, profileA,
      ContactTwoTailParameters6750Research.Profile.weightedCap])
    (by norm_num [prime, agreements, n, errors, profileA,
      ContactTwoTailParameters6750Research.Profile.weightedCap]) gates Q hQ hbox
    Hsupport selected Gamma u0 u1 hsolution hdegree hagreement hnoPencil

end

end ContactAnchoredOrdinaryFixedCell6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryFixedCell6750Research.identity_stage_card_le
