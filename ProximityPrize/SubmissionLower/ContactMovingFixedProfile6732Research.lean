import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research
import ProximityPrize.SubmissionLower.ContactMovingFactorLedger6719Research
import ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger6720Research
import ProximityPrize.SubmissionLower.ContactMovingAgreementCertificate6719Research
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch
import ProximityPrize.SubmissionLower.ContactMovingOuterBudget6719Research

/-! Fixed 67.32 profile and the reduced-proper/identity factor ledger. -/
namespace ProximityPrize.SubmissionLower.ContactMovingFixedProfile6732Research

open scoped BigOperators
open ContactFlagBezout6543Research ContactRobustFixedMeet6656Research
open ContactResidualSupportParametersResearch ContactGCDCumulativeFlagsResearch
open ContactTightSingularLedgerResearch ContactMovingPositiveLedger6719Research
open ContactMovingFactorLedger6719Research
open ContactMovingReducedPositiveLedger6720Research
open ContactMovingOuterBudget6719Research ContactNearPencil6600ArithmeticResearch
open ContactFactoredFlagCount6676Research

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def prime : ℕ := 2130706433

def fixedProfile : Profile := ⟨262144,131071,182062,7282480,1222,11⟩

def fixedSupport : ResidualSupportParameters :=
  ContactMovingAgreementCertificate6719Research.support 1167 43 9

def fixedTightProfile : TightParameters :=
  ⟨262144,131071,182062,7282480,1222,11⟩

def identityDegree (p : Profile) (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  flagMixed flag (paddedCut a b s (p.w+1)) unitZFlag +
    flagMixed flag (paddedCut a b s (p.w+1)) unitYZFlag

def properLedger (p : Profile) (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  (p.w+1)*ContactMovingReducedFactorLedger6720Research.factorDegreeCost
      p (ContactMovingAgreementCertificate6719Research.support a b s) a b s flag +
    ContactMovingReducedFactorLedger6720Research.factorUnitCost
      p (ContactMovingAgreementCertificate6719Research.support a b s) a b s flag

def factorLedger (p : Profile) (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  properLedger p a b s flag

theorem sum_factorLedger_le {J : Type*} [Fintype J]
    (p : Profile) (a b s : ℕ) (flags : J → FlagDegree) (cap : FlagDegree)
    (hi : (∑ j, (flags j).all) ≤ cap.all)
    (hm : (∑ j, ((flags j).yz+(flags j).all)) ≤ cap.yz+cap.all)
    (ht : (∑ j, ((flags j).zOnly+(flags j).yz+(flags j).all)) ≤
      cap.zOnly+cap.yz+cap.all) :
    (∑ j, factorLedger p a b s (flags j)) ≤ factorLedger p a b s cap := by
  simp only [factorLedger, properLedger,
    ContactMovingReducedFactorLedger6720Research.factorDegreeCost,
    ContactMovingReducedFactorLedger6720Research.factorUnitCost,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  gcongr
  all_goals first
    | exact ContactMovingReducedPositiveLedger6720Research.sum_degreeSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate6719Research.support a b s) a b s
    | exact ContactMovingReducedPositiveLedger6720Research.sum_unitSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate6719Research.support a b s) a b s
    | exact ContactMovingReducedPositiveLedger6720Research.sum_zSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate6719Research.support a b s)
    | exact ContactMovingReducedPositiveLedger6720Research.sum_yzSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate6719Research.support a b s)
    | exact ContactMovingReducedPositiveLedger6720Research.sum_degreeBase_le
        flags cap hi hm ht a b s
    | exact ContactMovingReducedPositiveLedger6720Research.sum_unitBase_le
        flags cap hi hm ht a b s
    | exact ContactMovingReducedPositiveLedger6720Research.sum_zBase_le flags cap hi hm ht
    | exact ContactMovingReducedPositiveLedger6720Research.sum_yzBase_le flags cap hi hm ht

def fixedFlag : FlagDegree := supportCumulativeFlag fixedSupport
def fixedFactorLedger : ℕ := factorLedger fixedProfile 1167 43 9 fixedFlag

theorem fixed_values :
    fixedProfile.errors=80082 ∧ fixedProfile.gap=50991 ∧
    fixedProfile.yCap=55 ∧ fixedProfile.degreeIncidence=9623227539 ∧
    fixedProfile.unitIncidence=131073 ∧ fixedFlag=⟨1167,44,11⟩ ∧
    identityDegree fixedProfile 1167 43 9 fixedFlag=
      ContactMovingParameters6732Research.identityZDegree+
        ContactMovingParameters6732Research.identityYZDegree := by decide

theorem fixed_regular_ceiling :
    fixedFactorLedger/fixedProfile.gap+1 =
      ContactMovingParameters6732Research.fixedRegularCost := by decide

theorem fixed_singular_ceiling : fixedTightProfile.countCap+1 =
    ContactMovingParameters6732Research.fixedSingularCost := by decide

theorem fixed_inclusive_cost_le :
    (fixedFactorLedger*fixedProfile.gap)/fixedProfile.gap^2+
      fixedTightProfile.countCap ≤ ContactMovingParameters6732Research.fixedRegularCost+
        ContactMovingParameters6732Research.fixedSingularCost := by decide

theorem fixed_alignment :
    ContactProfileFixedSelectedCombinerResearch.FixedParameterAlignment
      fixedProfile fixedTightProfile := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem fixed_characteristic_gates :
    1 ≤ fixedProfile.slopeCap ∧ fixedProfile.slopeCap < prime ∧
    1 ≤ fixedProfile.w ∧ fixedProfile.w < prime ∧
    fixedProfile.w < fixedProfile.agreements ∧ fixedProfile.agreements ≤ fixedProfile.n ∧
    fixedProfile.w < fixedTightProfile.kappa*fixedTightProfile.D ∧
    1 ≤ fixedTightProfile.algebraicCap ∧
    fixedTightProfile.algebraicCap < prime ∧ fixedTightProfile.implicitYCap < prime ∧
    2*fixedTightProfile.implicitYCap*fixedTightProfile.algebraicCap < prime := by decide

theorem fixed_flag_gates :
    fixedSupport.s < fixedSupport.ys ∧ fixedSupport.ys+1 < prime ∧
    fixedSupport.s-1 < prime ∧ fixedSupport.total < prime ∧
    (1+(fixedProfile.w+1)*(2*(43+9+3)-2))*fixedSupport.s+
      fixedSupport.ys*((2*(9+2)-1)*(fixedProfile.w+1)) < prime ∧
    (1+(fixedProfile.w+1)*(2*(43+9+3)-2))*fixedSupport.s+
      fixedSupport.ys*((2*(9+2)-2)*(fixedProfile.w+1)) < prime ∧
    2*fixedSupport.total*(1167+43+9+4) < prime := by decide

theorem fixed_degree_incidence_ceiling :
    fixedProfile.n*fixedProfile.gap*fixedProfile.w ≤
      fixedProfile.degreeIncidence*fixedProfile.agreements := by decide

theorem fixed_degree_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n-k)*fixedProfile.gap*(fixedProfile.w-k) ≤
      fixedProfile.degreeIncidence*(fixedProfile.agreements-k) := by
  have hcross := identity_degree_weight_cross_le fixedProfile.n
    fixedProfile.agreements fixedProfile.w k hk (by decide) (by decide)
  have hmul := Nat.mul_le_mul_right (fixedProfile.agreements-k)
    fixed_degree_incidence_ceiling
  have htotal : ((fixedProfile.n-k)*fixedProfile.gap*(fixedProfile.w-k))*
      fixedProfile.agreements ≤
      (fixedProfile.degreeIncidence*(fixedProfile.agreements-k))*fixedProfile.agreements := by
    calc
      _ = (fixedProfile.n-k)*(fixedProfile.agreements-fixedProfile.w)*
          (fixedProfile.w-k)*fixedProfile.agreements := rfl
      _ ≤ fixedProfile.n*(fixedProfile.agreements-fixedProfile.w)*fixedProfile.w*
          (fixedProfile.agreements-k) := hcross
      _ ≤ (fixedProfile.degreeIncidence*fixedProfile.agreements)*
          (fixedProfile.agreements-k) := by simpa only [Profile.gap] using hmul
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right htotal (by decide)

theorem fixed_unit_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n-k)*fixedProfile.gap ≤
      fixedProfile.unitIncidence*(fixedProfile.agreements-k) := by
  simpa only [Profile.gap, Profile.unitIncidence] using
    identity_unit_weight_le fixedProfile.n fixedProfile.agreements fixedProfile.w
      k hk (by decide) (by decide)

private theorem flagMixed_left_expand (p q r : FlagDegree) :
    flagMixed p q r =
      p.zOnly * flagMixed unitZFlag q r +
      p.yz * flagMixed unitYZFlag q r +
      p.all * flagMixed unitAllFlag q r := by
  cases p
  simp [flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
  ring

private theorem identityDegree_expand (p : Profile) (a b s : ℕ) (flag : FlagDegree) :
    identityDegree p a b s flag =
      flag.zOnly * identityDegree p a b s unitZFlag +
      flag.yz * identityDegree p a b s unitYZFlag +
      flag.all * identityDegree p a b s unitAllFlag := by
  unfold identityDegree
  rw [flagMixed_left_expand flag (paddedCut a b s (p.w+1)) unitZFlag,
    flagMixed_left_expand flag (paddedCut a b s (p.w+1)) unitYZFlag]
  ring

private theorem properLedger_expand (p : Profile) (a b s : ℕ) (flag : FlagDegree) :
    properLedger p a b s flag =
      flag.zOnly * properLedger p a b s unitZFlag +
      flag.yz * properLedger p a b s unitYZFlag +
      flag.all * properLedger p a b s unitAllFlag := by
  unfold properLedger
    ContactMovingReducedFactorLedger6720Research.factorDegreeCost
    ContactMovingReducedFactorLedger6720Research.factorUnitCost
    ContactMovingReducedPositiveLedger6720Research.degreeSlope
    ContactMovingReducedPositiveLedger6720Research.degreeBase
    ContactMovingReducedPositiveLedger6720Research.unitSlope
    ContactMovingReducedPositiveLedger6720Research.unitBase
    ContactMovingReducedPositiveLedger6720Research.zSlope
    ContactMovingReducedPositiveLedger6720Research.zBase
    ContactMovingReducedPositiveLedger6720Research.yzSlope
    ContactMovingReducedPositiveLedger6720Research.yzBase
  simp only [weightedMixed_eq]
  rw [flagMixed_left_expand flag, flagMixed_left_expand flag,
    flagMixed_left_expand flag, flagMixed_left_expand flag,
    flagMixed_left_expand flag, flagMixed_left_expand flag,
    flagMixed_left_expand flag, flagMixed_left_expand flag,
    flagMixed_left_expand flag, flagMixed_left_expand flag]
  ring

theorem identity_le_proper (flag : FlagDegree) :
    (fixedProfile.n - fixedProfile.w) * (fixedProfile.errors + 1) *
      identityDegree fixedProfile 1167 43 9 flag ≤
    properLedger fixedProfile 1167 43 9 flag := by
  have hz : (fixedProfile.n - fixedProfile.w) * (fixedProfile.errors + 1) *
      identityDegree fixedProfile 1167 43 9 unitZFlag ≤
      properLedger fixedProfile 1167 43 9 unitZFlag := by decide
  have hyz : (fixedProfile.n - fixedProfile.w) * (fixedProfile.errors + 1) *
      identityDegree fixedProfile 1167 43 9 unitYZFlag ≤
      properLedger fixedProfile 1167 43 9 unitYZFlag := by decide
  have hall : (fixedProfile.n - fixedProfile.w) * (fixedProfile.errors + 1) *
      identityDegree fixedProfile 1167 43 9 unitAllFlag ≤
      properLedger fixedProfile 1167 43 9 unitAllFlag := by decide
  rw [identityDegree_expand, properLedger_expand]
  have hdistrib :
      (fixedProfile.n - fixedProfile.w) * (fixedProfile.errors + 1) *
        (flag.zOnly * identityDegree fixedProfile 1167 43 9 unitZFlag +
          flag.yz * identityDegree fixedProfile 1167 43 9 unitYZFlag +
          flag.all * identityDegree fixedProfile 1167 43 9 unitAllFlag) =
      flag.zOnly * ((fixedProfile.n - fixedProfile.w) * (fixedProfile.errors + 1) *
        identityDegree fixedProfile 1167 43 9 unitZFlag) +
      flag.yz * ((fixedProfile.n - fixedProfile.w) * (fixedProfile.errors + 1) *
        identityDegree fixedProfile 1167 43 9 unitYZFlag) +
      flag.all * ((fixedProfile.n - fixedProfile.w) * (fixedProfile.errors + 1) *
        identityDegree fixedProfile 1167 43 9 unitAllFlag) := by ring
  rw [hdistrib]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hz)
    (Nat.mul_le_mul_left _ hyz)) (Nat.mul_le_mul_left _ hall)

end ProximityPrize.SubmissionLower.ContactMovingFixedProfile6732Research
