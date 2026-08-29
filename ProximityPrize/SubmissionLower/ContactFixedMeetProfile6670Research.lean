import ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
import ProximityPrize.SubmissionLower.ContactProfileYZFactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactGCDCumulativeFlagsResearch

/-!
# Fixed-meet arithmetic at agreement 182078

This module records the exact profile, support, sharp-YZ regular ledger, tight
singular ledger, and characteristic/incidence gates for the recursive-GCD
fixed cell at agreement `182078`.
-/

namespace ProximityPrize.SubmissionLower.ContactFixedMeetProfile6670Research

open ContactFlagBezout6543Research
open ContactNearPencil6600ArithmeticResearch
open ContactProfileYZFactorLedgerResearch
open ContactResidualSupportParametersResearch
open ContactResidualSupportParametersResearch.ResidualSupportParameters
open ContactRobustFixedMeet6656Research
open ContactSharpTaylorFixedMeet6656Research
open ContactSingularLedger6600Research
open ContactTightSingularLedgerResearch
open ContactGCDCumulativeFlagsResearch

set_option maxHeartbeats 2000000
set_option maxRecDepth 50000

/-- The challenge characteristic. -/
def prime : ℕ := 2130706433

/-- The final fixed-meet profile at agreement `182078`. -/
def fixedProfile : Profile where
  n := 262144
  w := 131071
  agreements := 182078
  weightedCap := 9103900
  seedTotalCap := 3100
  slopeCap := 15

/-- Residual support preserved by the target fixed-meet recursion. -/
def fixedSupport : ResidualSupportParameters where
  s := 15
  ys := 84
  total := 3100
  one_le_s := by norm_num
  s_le_ys := by norm_num
  ys_le_total := by norm_num
  two_le_ys := by norm_num

/-- Tight implicit-pair parameters for the singular fixed branch. -/
def fixedTightProfile : TightParameters where
  n := 262144
  w := 131071
  a := 182078
  D := 9103900
  L := 3100
  s := 15

/-- The sharp equal-weight direction paired with the accepted YZ tail. -/
def fixedSharpDirection : FlagDegree := sharpAgreementDirection fixedSupport

/-- Unnormalized sharp-YZ regular-factor ledger. -/
def fixedSharpYZRegularNumerator : ℕ :=
  factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
    (supportCumulativeFlag fixedSupport)

/-- Strict regular-factor count ceiling. -/
def fixedSharpYZRegularCeiling : ℕ :=
  fixedSharpYZRegularNumerator / fixedProfile.gap ^ 2 + 1

/-- Strict singular ceiling for the fixed tight profile. -/
def fixedTightSingularCeiling : ℕ :=
  fixedTightProfile.tightNumerator / fixedTightProfile.gap ^ 2 + 1

/-- Fixed cost combining the sharp-YZ regular ledger and the tight singular
ceiling. -/
def fixedCountCeiling : ℕ :=
  fixedSharpYZRegularCeiling + fixedTightProfile.countCap + 1

theorem fixed_profile_values :
    fixedProfile.errors = 80066 ∧
      fixedProfile.gap = 51007 ∧
      fixedProfile.yCap = 69 ∧
      fixedProfile.degreeIncidence = 9724036071 ∧
      fixedProfile.unitIncidence = 131073 ∧
      fixedProfile.surfaceFlag = ⟨3046, 54, 15⟩ ∧
      fixedProfile.derivativeFlag = ⟨3046, 54, 14⟩ ∧
      fixedProfile.agreementDirection = ⟨6092, 108, 29⟩ := by
  norm_num [fixedProfile, Profile.errors, Profile.gap, Profile.yCap,
    Profile.degreeIncidence, Profile.unitIncidence, Profile.surfaceFlag,
    Profile.derivativeFlag, Profile.agreementDirection]

theorem fixed_support_values :
    fixedSupport.agreementDirection = ⟨6032, 137, 29⟩ ∧
      supportCumulativeFlag fixedSupport = ⟨0, 138, 29⟩ := by
  norm_num [fixedSupport, sharpAgreementDirection, supportCumulativeFlag,
    flagMixed, unitZFlag, unitYZFlag, unitAllFlag]

theorem fixed_tight_values :
    fixedTightProfile.errors = 80066 ∧
      fixedTightProfile.gap = 51007 ∧
      fixedTightProfile.kappa = 29 ∧
      fixedTightProfile.implicitYCap = 70 ∧
      fixedTightProfile.algebraicCap = 46515 ∧
      fixedTightProfile.agreement = ⟨18349941, 3801059, 7943542945⟩ ∧
      fixedTightProfile.aggregateCost = ⟨1, 46515, 1⟩ ∧
      fixedTightProfile.coreNumerator = 23277717462100806 ∧
      fixedTightProfile.tightNumerator = 23471025417275496 ∧
      fixedTightProfile.countCap = 9021370 := by
  norm_num [fixedTightProfile, TightParameters.errors, TightParameters.gap,
    TightParameters.kappa, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.agreement,
    TightParameters.aggregateCost, TightParameters.coreNumerator,
    TightParameters.tightNumerator, TightParameters.countCap, dot]

theorem fixed_sharp_yz_regular_numerator_exact :
    fixedSharpYZRegularNumerator = 242973367976502272749186997 := by
  norm_num [fixedSharpYZRegularNumerator, factorRegularLedgerYZForDirection,
    factorPrimaryForDirection, factorZTailForDirection,
    factorYZTailForDirection, fixedProfile, fixedSupport,
    fixedSharpDirection, sharpAgreementDirection,
    supportCumulativeFlag, Profile.degreeIncidence, Profile.unitIncidence,
    Profile.errors, Profile.gap, flagMixed, unitZFlag, unitYZFlag,
    unitAllFlag]

theorem fixed_sharp_yz_regular_ceiling_exact :
    fixedSharpYZRegularCeiling = 93389728233159214 := by
  norm_num [fixedSharpYZRegularCeiling, fixed_sharp_yz_regular_numerator_exact,
    fixedProfile, Profile.gap]

theorem fixed_tight_singular_ceiling_exact :
    fixedTightSingularCeiling = 9021371 := by
  norm_num [fixedTightSingularCeiling, fixedTightProfile,
    TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap, dot]

theorem fixed_tight_singular_count_cap_exact :
    fixedTightProfile.countCap = 9021371 - 1 := by
  rw [fixed_tight_values.2.2.2.2.2.2.2.2.2]

theorem fixed_count_ceiling_exact :
    fixedCountCeiling = 93389728242180585 := by
  rw [fixedCountCeiling, fixed_sharp_yz_regular_ceiling_exact,
    fixed_tight_singular_ceiling_exact]

theorem fixed_projection_gates :
    0 < fixedProfile.gap ∧
      fixedProfile.agreements ≤ fixedProfile.n ∧
      fixedProfile.w < fixedProfile.agreements ∧
      fixedProfile.errors < fixedProfile.n ∧
      fixedProfile.slopeCap ≤ fixedProfile.seedTotalCap ∧
      fixedProfile.yCap ≤ fixedProfile.seedTotalCap ∧
      fixedTightProfile.gap = fixedProfile.gap ∧
      (fixedTightProfile.D - 1) / fixedTightProfile.w ≤ fixedProfile.yCap ∧
      fixedTightProfile.s ≤ fixedProfile.slopeCap ∧
      fixedTightProfile.L ≤ fixedProfile.seedTotalCap := by
  norm_num [fixedProfile, fixedTightProfile, Profile.gap, Profile.errors,
    Profile.yCap, TightParameters.gap]

theorem fixed_characteristic_gates :
    fixedProfile.weightedCap < prime ∧
      (2 * fixedProfile.slopeCap - 1) * fixedProfile.weightedCap < prime ∧
      (2 * fixedProfile.slopeCap - 1) * fixedProfile.seedTotalCap < prime ∧
      fixedProfile.slopeCap < prime ∧
      1 ≤ fixedTightProfile.s ∧ fixedTightProfile.s < prime ∧
      1 ≤ fixedTightProfile.w ∧ fixedTightProfile.w < prime ∧
      fixedTightProfile.w < fixedTightProfile.kappa * fixedTightProfile.D ∧
      fixedTightProfile.kappa * fixedTightProfile.D < prime ∧
      1 ≤ fixedTightProfile.algebraicCap ∧
      fixedTightProfile.algebraicCap < prime ∧
      fixedTightProfile.implicitYCap < prime ∧
      2 * fixedTightProfile.implicitYCap *
        fixedTightProfile.algebraicCap < prime ∧
      fixedTightProfile.w < fixedTightProfile.a ∧
      fixedTightProfile.a ≤ fixedTightProfile.n := by
  norm_num [fixedProfile, fixedTightProfile, prime,
    TightParameters.kappa, TightParameters.implicitYCap,
    TightParameters.algebraicCap]

theorem fixed_degree_incidence_ceiling :
    fixedProfile.n * fixedProfile.gap * fixedProfile.w ≤
      fixedProfile.degreeIncidence * fixedProfile.agreements := by
  norm_num [fixedProfile, Profile.gap, Profile.degreeIncidence]

theorem fixed_degree_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n - k) * fixedProfile.gap * (fixedProfile.w - k) ≤
      fixedProfile.degreeIncidence * (fixedProfile.agreements - k) := by
  have hcross := identity_degree_weight_cross_le
    fixedProfile.n fixedProfile.agreements fixedProfile.w k hk
    (by norm_num [fixedProfile]) (by norm_num [fixedProfile])
  have hmul := Nat.mul_le_mul_right (fixedProfile.agreements - k)
    fixed_degree_incidence_ceiling
  have htotal :
      ((fixedProfile.n - k) * fixedProfile.gap * (fixedProfile.w - k)) *
          fixedProfile.agreements ≤
        (fixedProfile.degreeIncidence * (fixedProfile.agreements - k)) *
          fixedProfile.agreements := by
    calc
      ((fixedProfile.n - k) * fixedProfile.gap * (fixedProfile.w - k)) *
            fixedProfile.agreements =
          (fixedProfile.n - k) *
            (fixedProfile.agreements - fixedProfile.w) *
            (fixedProfile.w - k) * fixedProfile.agreements := by
              rfl
      _ ≤ fixedProfile.n * (fixedProfile.agreements - fixedProfile.w) *
          fixedProfile.w * (fixedProfile.agreements - k) := hcross
      _ ≤ (fixedProfile.degreeIncidence * fixedProfile.agreements) *
          (fixedProfile.agreements - k) := by
            simpa only [Profile.gap] using hmul
      _ = (fixedProfile.degreeIncidence * (fixedProfile.agreements - k)) *
          fixedProfile.agreements := by ring
  exact Nat.le_of_mul_le_mul_right htotal (by norm_num [fixedProfile])

theorem fixed_unit_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n - k) * fixedProfile.gap ≤
      fixedProfile.unitIncidence * (fixedProfile.agreements - k) := by
  simpa only [Profile.gap, Profile.unitIncidence] using
    identity_unit_weight_le
      fixedProfile.n fixedProfile.agreements
      fixedProfile.w k hk (by norm_num [fixedProfile]) (by norm_num [fixedProfile])

end ProximityPrize.SubmissionLower.ContactFixedMeetProfile6670Research
