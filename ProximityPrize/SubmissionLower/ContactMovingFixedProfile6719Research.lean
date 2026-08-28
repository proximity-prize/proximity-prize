import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingParameters6719Research
import ProximityPrize.SubmissionLower.ContactMovingFactorLedger6719Research
import ProximityPrize.SubmissionLower.ContactMovingAgreementCertificate6719Research
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch

namespace ProximityPrize.SubmissionLower.ContactMovingFixedProfile6719Research

open ContactFlagBezout6543Research ContactRobustFixedMeet6656Research
open ContactResidualSupportParametersResearch ContactGCDCumulativeFlagsResearch
open ContactTightSingularLedgerResearch ContactNearPencil6600ArithmeticResearch
open ContactMovingFactorLedger6719Research

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def prime : ℕ := 2130706433

def fixedProfile : ContactRobustFixedMeet6656Research.Profile :=
  ⟨262144,131071,182189,6740993,1006,10⟩

def fixedSupport : ResidualSupportParameters :=
  ContactMovingAgreementCertificate6719Research.support 955 40 8

def fixedTightProfile : TightParameters :=
  ⟨262144,131071,182189,6740993,1006,10⟩

def fixedLedger : ℕ :=
  regularLedger fixedProfile 955 40 8 (supportCumulativeFlag fixedSupport)

theorem fixed_values :
    fixedProfile.errors = 79955 ∧ fixedProfile.gap = 51118 ∧
    fixedProfile.yCap = 51 ∧ fixedProfile.degreeIncidence = 9640470642 ∧
    fixedProfile.unitIncidence = 131073 ∧
    supportCumulativeFlag fixedSupport = ⟨955,41,10⟩ := by decide

theorem fixedLedger_eq_numeric : fixedLedger =
    ContactMovingParameters6719Research.primary +
      ContactMovingParameters6719Research.zTail + ContactMovingParameters6719Research.yzTail := by
  decide

theorem fixed_ledger_exact : fixedLedger = 712013114602776259677364218 := by decide

theorem fixed_tight_ceiling : fixedTightProfile.countCap + 1 =
    ContactMovingParameters6719Research.fixedSingularCost := by decide

theorem fixed_regular_ceiling : fixedLedger / fixedProfile.gap^2 + 1 =
    ContactMovingParameters6719Research.fixedRegularCost := by decide

theorem fixed_inclusive_cost_le :
    fixedLedger / fixedProfile.gap^2 + fixedTightProfile.countCap ≤
      ContactMovingParameters6719Research.fixedCost := by decide

theorem fixed_alignment :
    ContactProfileFixedSelectedCombinerResearch.FixedParameterAlignment
      fixedProfile fixedTightProfile := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem fixed_characteristic_gates :
    1 ≤ fixedProfile.slopeCap ∧ fixedProfile.slopeCap < prime ∧
    1 ≤ fixedProfile.w ∧ fixedProfile.w < prime ∧
    fixedProfile.w < fixedProfile.agreements ∧ fixedProfile.agreements ≤ fixedProfile.n ∧
    fixedProfile.algebraicCap < prime ∧ fixedProfile.implicitWeightedCap < prime ∧
    fixedProfile.implicitYCap < prime ∧
    fixedTightProfile.w < fixedTightProfile.kappa * fixedTightProfile.D ∧
    fixedTightProfile.kappa * fixedTightProfile.D < prime ∧
    1 ≤ fixedTightProfile.algebraicCap ∧ fixedTightProfile.algebraicCap < prime ∧
    fixedTightProfile.implicitYCap < prime ∧
    2 * fixedTightProfile.implicitYCap * fixedTightProfile.algebraicCap < prime := by decide

theorem fixed_tight_singular_gates :
    1 ≤ fixedTightProfile.s ∧ fixedTightProfile.s < prime ∧
    1 ≤ fixedTightProfile.w ∧ fixedTightProfile.w < prime ∧
    fixedTightProfile.w < fixedTightProfile.kappa * fixedTightProfile.D ∧
    1 ≤ fixedTightProfile.algebraicCap ∧ fixedTightProfile.implicitYCap < prime ∧
    fixedTightProfile.algebraicCap < prime ∧
    2 * fixedTightProfile.implicitYCap * fixedTightProfile.algebraicCap < prime ∧
    fixedTightProfile.w < fixedTightProfile.a ∧ fixedTightProfile.a ≤ fixedTightProfile.n := by decide

theorem fixed_active_yz_gates :
    fixedSupport.s < fixedSupport.ys ∧ fixedSupport.ys+1 < prime ∧
    fixedSupport.s-1 < prime ∧ fixedSupport.total < prime ∧
    (1+fixedProfile.w*(2*fixedSupport.ys-2))*fixedSupport.s +
      fixedSupport.ys*((2*fixedSupport.s-1)*fixedProfile.w) < prime := by decide

theorem fixed_small_moving_gate :
    2*fixedSupport.total*(955+40+8+4) < prime := by decide

theorem fixed_degree_incidence_ceiling :
    fixedProfile.n*fixedProfile.gap*fixedProfile.w ≤
      fixedProfile.degreeIncidence*fixedProfile.agreements := by decide

theorem fixed_degree_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n-k)*fixedProfile.gap*(fixedProfile.w-k) ≤
      fixedProfile.degreeIncidence*(fixedProfile.agreements-k) := by
  have hcross := identity_degree_weight_cross_le fixedProfile.n
    fixedProfile.agreements fixedProfile.w k hk (by decide) (by decide)
  have hmul := Nat.mul_le_mul_right (fixedProfile.agreements-k) fixed_degree_incidence_ceiling
  have htotal :
      ((fixedProfile.n-k)*fixedProfile.gap*(fixedProfile.w-k))*fixedProfile.agreements ≤
        (fixedProfile.degreeIncidence*(fixedProfile.agreements-k))*fixedProfile.agreements := by
    calc
      _ = (fixedProfile.n-k)*(fixedProfile.agreements-fixedProfile.w)*
          (fixedProfile.w-k)*fixedProfile.agreements := rfl
      _ ≤ fixedProfile.n*(fixedProfile.agreements-fixedProfile.w)*fixedProfile.w*
          (fixedProfile.agreements-k) := hcross
      _ ≤ (fixedProfile.degreeIncidence*fixedProfile.agreements)*(fixedProfile.agreements-k) := by
        simpa only [Profile.gap] using hmul
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right htotal (by decide)

theorem fixed_unit_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n-k)*fixedProfile.gap ≤
      fixedProfile.unitIncidence*(fixedProfile.agreements-k) := by
  simpa only [Profile.gap,Profile.unitIncidence] using
    identity_unit_weight_le fixedProfile.n fixedProfile.agreements fixedProfile.w
      k hk (by decide) (by decide)

end ProximityPrize.SubmissionLower.ContactMovingFixedProfile6719Research
