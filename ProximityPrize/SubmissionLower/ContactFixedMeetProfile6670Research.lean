import ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
import ProximityPrize.SubmissionLower.ContactProfileYZFactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactGCDCumulativeFlagsResearch

/-!
# Fixed-meet arithmetic at agreement 182268

This module records the exact profile, support, sharp-YZ regular ledger, tight
singular ledger, and characteristic/incidence gates for the recursive-GCD
fixed cell at agreement `182268`. The ordinary-box profile flag retains
total cap `909`; the actual joint-support ledger instead uses cumulative
total cap `900`. It contains no new geometry.
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

/-- The final fixed-meet profile at agreement `182268`. -/
def fixedProfile : Profile where
  n := 262144
  w := 131071
  agreements := 182268
  weightedCap := 6379380
  seedTotalCap := 900
  slopeCap := 10

/-- Residual support preserved by the target fixed-meet recursion. -/
def fixedSupport : ResidualSupportParameters where
  s := 10
  ys := 43
  total := 900
  one_le_s := by norm_num
  s_le_ys := by norm_num
  ys_le_total := by norm_num
  two_le_ys := by norm_num

/-- Tight implicit-pair parameters for the singular fixed branch. -/
def fixedTightProfile : TightParameters where
  n := 262144
  w := 131071
  a := 182268
  D := 6379380
  L := 900
  s := 10

/-- The sharp equal-weight direction paired with the accepted YZ tail. -/
def fixedSharpDirection : FlagDegree := sharpAgreementDirection fixedSupport

/-- Unnormalized sharp-YZ regular-factor ledger. -/
def fixedSharpYZRegularNumerator : ℕ :=
  factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
    (supportCumulativeFlag fixedSupport)

/-- Strict regular-factor count ceiling. -/
def fixedSharpYZRegularCeiling : ℕ :=
  fixedSharpYZRegularNumerator / fixedProfile.gap ^ 2 + 1

/-- Strict singular-factor count ceiling. -/
def fixedTightSingularCeiling : ℕ := fixedTightProfile.countCap + 1

/-- Strict fixed-cell ceiling after adding regular and singular branches. -/
def fixedCountCeiling : ℕ :=
  fixedSharpYZRegularCeiling + fixedTightSingularCeiling

theorem fixed_profile_values :
    fixedProfile.errors = 79876 ∧
      fixedProfile.gap = 51197 ∧
      fixedProfile.yCap = 48 ∧
      fixedProfile.degreeIncidence = 9651184543 ∧
      fixedProfile.unitIncidence = 131073 ∧
      fixedProfile.surfaceFlag = ⟨862, 38, 10⟩ ∧
      fixedProfile.agreementDirection = ⟨1724, 76, 19⟩ ∧
      fixedProfile.rectangularSurfaceFlag = ⟨900, 48, 10⟩ := by
  norm_num [fixedProfile, Profile.errors, Profile.gap, Profile.yCap,
    Profile.degreeIncidence, Profile.unitIncidence, Profile.surfaceFlag,
    Profile.derivativeFlag, Profile.agreementDirection,
    Profile.rectangularSurfaceFlag]
  rfl

theorem fixed_support_values :
    fixedSupport.agreementDirection = ⟨1714, 66, 19⟩ ∧
      fixedSharpDirection = ⟨1714, 65, 19⟩ := by
  norm_num [fixedSupport, fixedSharpDirection,
    ResidualSupportParameters.agreementDirection, sharpAgreementDirection]

theorem fixed_cumulative_surface_flag_exact :
    supportCumulativeFlag fixedSupport = ⟨857, 33, 10⟩ := by
  norm_num [supportCumulativeFlag, flagFromCaps, fixedSupport]

theorem fixed_sharp_yz_regular_numerator_exact :
    fixedSharpYZRegularNumerator = 711111975280460686113783943 := by
  norm_num [fixedSharpYZRegularNumerator, fixedSharpDirection,
    factorRegularLedgerYZForDirection, factorPrimaryForDirection,
    factorZTailForDirection, factorYZTailForDirection, fixedProfile,
    fixedSupport, sharpAgreementDirection, supportCumulativeFlag, flagFromCaps,
    Profile.yCap, Profile.degreeIncidence, Profile.unitIncidence,
    Profile.errors, Profile.gap, flagMixed, unitZFlag, unitYZFlag]

theorem fixed_sharp_yz_regular_ceiling_exact :
    fixedSharpYZRegularCeiling = 271299482742257601 := by
  rw [fixedSharpYZRegularCeiling, fixed_sharp_yz_regular_numerator_exact]
  norm_num [fixedProfile, Profile.gap]

theorem fixed_tight_values :
    fixedTightProfile.kappa = 19 ∧
      fixedTightProfile.implicitYCap = 924 ∧
      fixedTightProfile.algebraicCap = 17100 ∧
      fixedTightProfile.agreement = ⟨242220209, 131071, 4482628201⟩ ∧
      fixedTightProfile.aggregateCost = ⟨17100, 31600800, 924⟩ ∧
      fixedTightProfile.coreNumerator = 1628696803730309908 ∧
      fixedTightProfile.tightNumerator = 1628726746816029908 ∧
      fixedTightProfile.countCap = 31812929513253 := by
  norm_num [fixedTightProfile, TightParameters.kappa,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.agreement, TightParameters.aggregateCost,
    TightParameters.coreNumerator, TightParameters.tightNumerator,
    TightParameters.countCap, TightParameters.errors, TightParameters.gap,
    dot]

theorem fixed_tight_singular_ceiling_exact :
    fixedTightSingularCeiling = 31812929513254 := by
  norm_num [fixedTightSingularCeiling, fixedTightProfile,
    TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap, dot]

theorem fixed_tight_singular_count_cap_exact :
    fixedTightProfile.countCap = 31812929513254 - 1 := by
  rw [fixed_tight_values.2.2.2.2.2.2.2]

theorem fixed_count_ceiling_exact :
    fixedCountCeiling = 271331295671770855 := by
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

end ProximityPrize.SubmissionLower.ContactFixedMeetProfile6670Research
