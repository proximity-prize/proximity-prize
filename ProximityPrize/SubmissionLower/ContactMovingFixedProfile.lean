import ProximityPrize.SubmissionLower.ContactMovingParameters
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombiner
import ProximityPrize.SubmissionLower.ContactMovingOuterBudget
/-! Fixed 67.32 profile and the reduced-proper/identity factor ledger. -/
namespace ProximityPrize.SubmissionLower.ContactMovingFixedProfile

open scoped BigOperators
open ContactFlagBezout ContactRobustFixedMeet
open ContactResidualSupportParameters ContactGCDCumulativeFlags
open ContactTightSingularLedger ContactMovingPositiveLedger
open ContactMovingReducedPositiveLedger
open ContactMovingOuterBudget ContactNearPencil6600Arithmetic
open ContactFactoredFlagCount

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def fixedProfile : Profile := ⟨262144,131071,182062,7282480,1222,11⟩

def fixedTightProfile : TightParameters :=
  ⟨262144,131071,182062,7282480,1222,11⟩

def identityDegree (p : Profile) (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  flagMixed flag (paddedCut a b s (p.w+1)) unitZFlag +
    flagMixed flag (paddedCut a b s (p.w+1)) unitYZFlag

def factorLedger (p : Profile) (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  (p.w+1)*ContactMovingReducedFactorLedger.factorDegreeCost
      p (ContactMovingAgreementCertificate.support a b s) a b s flag +
    ContactMovingReducedFactorLedger.factorUnitCost
      p (ContactMovingAgreementCertificate.support a b s) a b s flag +
    (p.n-p.w)*(p.errors+1)*identityDegree p a b s flag

theorem sum_factorLedger_le {J : Type*} [Fintype J]
    (p : Profile) (a b s : ℕ) (flags : J → FlagDegree) (cap : FlagDegree)
    (hi : (∑ j, (flags j).all) ≤ cap.all)
    (hm : (∑ j, ((flags j).yz+(flags j).all)) ≤ cap.yz+cap.all)
    (ht : (∑ j, ((flags j).zOnly+(flags j).yz+(flags j).all)) ≤
      cap.zOnly+cap.yz+cap.all) :
    (∑ j, factorLedger p a b s (flags j)) ≤ factorLedger p a b s cap := by
  simp only [factorLedger,
    ContactMovingReducedFactorLedger.factorDegreeCost,
    ContactMovingReducedFactorLedger.factorUnitCost, identityDegree,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  gcongr
  all_goals first
    | exact ContactMovingReducedPositiveLedger.sum_degreeSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate.support a b s) a b s
    | exact ContactMovingReducedPositiveLedger.sum_unitSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate.support a b s) a b s
    | exact ContactMovingReducedPositiveLedger.sum_zSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate.support a b s)
    | exact ContactMovingReducedPositiveLedger.sum_yzSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate.support a b s)
    | exact ContactMovingReducedPositiveLedger.sum_degreeBase_le
        flags cap hi hm ht a b s
    | exact ContactMovingReducedPositiveLedger.sum_unitBase_le
        flags cap hi hm ht a b s
    | exact ContactMovingReducedPositiveLedger.sum_zBase_le flags cap hi hm ht
    | exact ContactMovingReducedPositiveLedger.sum_yzBase_le flags cap hi hm ht
    | exact sum_flagMixed_le_of_cumulative flags cap _ _ hi hm ht

def fixedFlag : FlagDegree :=
  supportCumulativeFlag ContactMovingParameters.fixedSupport
def fixedFactorLedger : ℕ := factorLedger fixedProfile 1167 43 9 fixedFlag

theorem fixed_inclusive_cost_le :
    (fixedFactorLedger*fixedProfile.gap)/fixedProfile.gap^2+
      fixedTightProfile.countCap ≤ ContactMovingParameters.fixedRegularCost+
        ContactMovingParameters.fixedSingularCost := by decide

theorem fixed_alignment :
    ContactProfileFixedSelectedCombiner.FixedParameterAlignment
      fixedProfile fixedTightProfile := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

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

end ProximityPrize.SubmissionLower.ContactMovingFixedProfile
