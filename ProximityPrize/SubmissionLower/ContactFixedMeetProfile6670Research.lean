import ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
import ProximityPrize.SubmissionLower.ContactProfileYZFactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactGCDCumulativeFlagsResearch

/-!
# Fixed-meet arithmetic at agreement 182278

This module records the exact profile, support, sharp-YZ regular ledger, tight
singular ledger, and characteristic/incidence gates for the recursive-GCD
fixed cell at agreement `182278`. The ordinary-box profile flag retains
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

/-- The final fixed-meet profile at agreement `181589`. -/
def fixedProfile : Profile where
  n := 262144
  w := 131071
  agreements := 181589
  weightedCap := 6174026
  seedTotalCap := 900
  slopeCap := 9

/-- Residual support preserved by the target fixed-meet recursion. -/
def fixedSupport : ResidualSupportParameters where
  s := 9
  ys := 47
  total := 900
  one_le_s := by norm_num
  s_le_ys := by norm_num
  ys_le_total := by norm_num
  two_le_ys := by norm_num

/-- Tight implicit-pair parameters for the singular fixed branch. -/
def fixedTightProfile : TightParameters where
  n := 262144
  w := 131071
  a := 181589
  D := 6174026
  L := 900
  s := 9

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
    fixedProfile.errors = 80555 ∧
      fixedProfile.gap = 50518 ∧
      fixedProfile.yCap = 47 ∧
      fixedProfile.degreeIncidence = 9558794971 ∧
      fixedProfile.unitIncidence = 131073 ∧
      fixedProfile.surfaceFlag = ⟨862, 38, 9⟩ ∧
      fixedProfile.agreementDirection = ⟨1724, 76, 17⟩ ∧
      fixedProfile.rectangularSurfaceFlag = ⟨900, 47, 9⟩ := by
  norm_num [fixedProfile, Profile.errors, Profile.gap, Profile.yCap,
    Profile.degreeIncidence, Profile.unitIncidence, Profile.surfaceFlag,
    Profile.derivativeFlag, Profile.agreementDirection,
    Profile.rectangularSurfaceFlag]
  rfl

theorem fixed_support_values :
    fixedSupport.agreementDirection = ⟨1706, 76, 17⟩ ∧
      fixedSharpDirection = ⟨1706, 75, 17⟩ := by
  norm_num [fixedSupport, fixedSharpDirection,
    ResidualSupportParameters.agreementDirection, sharpAgreementDirection]

theorem fixed_cumulative_surface_flag_exact :
    supportCumulativeFlag fixedSupport = ⟨853, 38, 9⟩ := by
  norm_num [supportCumulativeFlag, flagFromCaps, fixedSupport]

theorem fixed_sharp_yz_regular_numerator_exact :
    fixedSharpYZRegularNumerator = 698891531448260218566039124 := by
  norm_num [fixedSharpYZRegularNumerator, fixedSharpDirection,
    factorRegularLedgerYZForDirection, factorPrimaryForDirection,
    factorZTailForDirection, factorYZTailForDirection, fixedProfile,
    fixedSupport, sharpAgreementDirection, supportCumulativeFlag, flagFromCaps,
    Profile.yCap, Profile.degreeIncidence, Profile.unitIncidence,
    Profile.errors, Profile.gap, flagMixed, unitZFlag, unitYZFlag]

theorem fixed_sharp_yz_regular_ceiling_exact :
    fixedSharpYZRegularCeiling = 273852986174307542 := by
  rw [fixedSharpYZRegularCeiling, fixed_sharp_yz_regular_numerator_exact]
  norm_num [fixedProfile, Profile.gap]

theorem fixed_tight_values :
    fixedTightProfile.kappa = 17 ∧
      fixedTightProfile.implicitYCap = 800 ∧
      fixedTightProfile.algebraicCap = 15300 ∧
      fixedTightProfile.agreement = ⟨209713601, 131071, 4010772601⟩ ∧
      fixedTightProfile.aggregateCost = ⟨15300, 24480000, 800⟩ ∧
      fixedTightProfile.coreNumerator = 1261692850532201700 ∧
      fixedTightProfile.tightNumerator = 1261716502049441700 ∧
      fixedTightProfile.countCap = 24975583001097 := by
  norm_num [fixedTightProfile, TightParameters.kappa,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.agreement, TightParameters.aggregateCost,
    TightParameters.coreNumerator, TightParameters.tightNumerator,
    TightParameters.countCap, TightParameters.errors, TightParameters.gap,
    dot]

theorem fixed_tight_singular_ceiling_exact :
    fixedTightSingularCeiling = 24975583001098 := by
  norm_num [fixedTightSingularCeiling, fixedTightProfile,
    TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap, dot]

theorem fixed_tight_singular_count_cap_exact :
    fixedTightProfile.countCap = 24975583001097 := fixed_tight_values.2.2.2.2.2.2.2

theorem fixed_count_ceiling_exact :
    fixedCountCeiling = 273877961757308640 := by
  rw [fixedCountCeiling, fixed_sharp_yz_regular_ceiling_exact,
    fixed_tight_singular_ceiling_exact]

/-! ## Active-YZ projection and characteristic gates -/

/-- Exact cumulative surface and sharp cut caps used by the active-YZ
terminal projection constructor. -/
theorem fixed_active_yz_caps :
    (supportCumulativeFlag fixedSupport).yz +
        (supportCumulativeFlag fixedSupport).all = 47 ∧
      (supportCumulativeFlag fixedSupport).all = 9 ∧
      (supportCumulativeFlag fixedSupport).zOnly +
          (supportCumulativeFlag fixedSupport).yz +
          (supportCumulativeFlag fixedSupport).all = 900 ∧
      1 + fixedProfile.w * (2 * fixedSupport.ys - 2) = 12058533 ∧
      (2 * fixedSupport.s - 1) * fixedProfile.w = 2228207 := by
  norm_num [fixedProfile, fixedSupport, supportCumulativeFlag, flagFromCaps]

/-- Every small-characteristic and retained mixed-Z inequality required by
the active-YZ projection family at the target caps. -/
theorem fixed_active_yz_characteristic_gates :
    fixedSupport.s < fixedSupport.ys ∧
      fixedSupport.ys + 1 < prime ∧ fixedSupport.s - 1 < prime ∧
      fixedSupport.total < prime ∧
      (1 + fixedProfile.w * (2 * fixedSupport.ys - 2)) * fixedSupport.s +
        fixedSupport.ys * ((2 * fixedSupport.s - 1) * fixedProfile.w) =
          213252526 ∧
      (1 + fixedProfile.w * (2 * fixedSupport.ys - 2)) * fixedSupport.s +
        fixedSupport.ys * ((2 * fixedSupport.s - 1) * fixedProfile.w) < prime := by
  norm_num [fixedProfile, fixedSupport, prime]

/-- Characteristic gates for the profile and tight singular-pair ledger. -/
theorem fixed_characteristic_gates :
    1 ≤ fixedProfile.slopeCap ∧
      fixedProfile.slopeCap < prime ∧
      1 ≤ fixedProfile.w ∧
      fixedProfile.w < prime ∧
      fixedProfile.w < fixedProfile.agreements ∧
      fixedProfile.agreements ≤ fixedProfile.n ∧
      fixedProfile.algebraicCap < prime ∧
      fixedProfile.implicitWeightedCap < prime ∧
      fixedProfile.implicitYCap < prime ∧
      fixedTightProfile.w < fixedTightProfile.kappa * fixedTightProfile.D ∧
      fixedTightProfile.kappa * fixedTightProfile.D < prime ∧
      1 ≤ fixedTightProfile.algebraicCap ∧
      fixedTightProfile.algebraicCap < prime ∧
      fixedTightProfile.implicitYCap < prime ∧
      2 * fixedTightProfile.implicitYCap * fixedTightProfile.algebraicCap < prime := by
  norm_num [fixedProfile, fixedTightProfile, prime, Profile.algebraicCap,
    Profile.implicitWeightedCap, Profile.implicitYCap,
    TightParameters.kappa, TightParameters.algebraicCap,
    TightParameters.implicitYCap]

/-- The singular provider's hypotheses, in its argument order. -/
theorem fixed_tight_singular_gates :
    1 ≤ fixedTightProfile.s ∧
      fixedTightProfile.s < prime ∧
      1 ≤ fixedTightProfile.w ∧
      fixedTightProfile.w < prime ∧
      fixedTightProfile.w < fixedTightProfile.kappa * fixedTightProfile.D ∧
      1 ≤ fixedTightProfile.algebraicCap ∧
      fixedTightProfile.implicitYCap < prime ∧
      fixedTightProfile.algebraicCap < prime ∧
      2 * fixedTightProfile.implicitYCap *
          fixedTightProfile.algebraicCap < prime ∧
      fixedTightProfile.w < fixedTightProfile.a ∧
      fixedTightProfile.a ≤ fixedTightProfile.n := by
  norm_num [fixedTightProfile, prime, TightParameters.kappa,
    TightParameters.algebraicCap, TightParameters.implicitYCap]

/-! ## Global identity-incidence gates -/

theorem fixed_degree_incidence_ceiling :
    fixedProfile.n * fixedProfile.gap * fixedProfile.w ≤
      fixedProfile.degreeIncidence * fixedProfile.agreements := by
  norm_num [fixedProfile, Profile.gap, Profile.degreeIncidence]

/-- Uniform degree-weighted identity-incidence compression. -/
theorem fixed_degree_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n - k) * fixedProfile.gap * (fixedProfile.w - k) ≤
      fixedProfile.degreeIncidence * (fixedProfile.agreements - k) := by
  have hcross := identity_degree_weight_cross_le fixedProfile.n
    fixedProfile.agreements fixedProfile.w k hk
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
            (fixedProfile.w - k) * fixedProfile.agreements := by rfl
      _ ≤ fixedProfile.n * (fixedProfile.agreements - fixedProfile.w) *
          fixedProfile.w * (fixedProfile.agreements - k) := hcross
      _ ≤ (fixedProfile.degreeIncidence * fixedProfile.agreements) *
          (fixedProfile.agreements - k) := by
            simpa only [Profile.gap] using hmul
      _ = (fixedProfile.degreeIncidence * (fixedProfile.agreements - k)) *
          fixedProfile.agreements := by ring
  exact Nat.le_of_mul_le_mul_right htotal (by norm_num [fixedProfile])

/-- Uniform affine-unit identity-incidence compression. -/
theorem fixed_unit_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n - k) * fixedProfile.gap ≤
      fixedProfile.unitIncidence * (fixedProfile.agreements - k) := by
  simpa only [Profile.gap, Profile.unitIncidence] using
    identity_unit_weight_le fixedProfile.n fixedProfile.agreements
      fixedProfile.w k hk (by norm_num [fixedProfile])
        (by norm_num [fixedProfile])


end ProximityPrize.SubmissionLower.ContactFixedMeetProfile6670Research
