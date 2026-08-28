import ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
import ProximityPrize.SubmissionLower.ContactProfileYZFactorLedgerResearch

/-!
# Fixed-meet arithmetic at agreement 182668

This module records the exact profile, support, sharp-YZ regular ledger, tight
singular ledger, and characteristic/incidence gates for the recursive-GCD
fixed cell at agreement `182668`.  It contains no new geometry.
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

set_option maxHeartbeats 2000000
set_option maxRecDepth 50000

/-- The challenge characteristic. -/
def prime : ℕ := 2130706433

/-- The final fixed-meet profile at agreement `182668`. -/
def fixedProfile : Profile where
  n := 262144
  w := 131071
  agreements := 182668
  weightedCap := 4932036
  seedTotalCap := 690
  slopeCap := 7

/-- Residual support preserved by the target fixed-meet recursion. -/
def fixedSupport : ResidualSupportParameters where
  s := 7
  ys := 37
  total := 697
  one_le_s := by norm_num
  s_le_ys := by norm_num
  ys_le_total := by norm_num
  two_le_ys := by norm_num

/-- Tight implicit-pair parameters for the singular fixed branch. -/
def fixedTightProfile : TightParameters where
  n := 262144
  w := 131071
  a := 182668
  D := 4932036
  L := 690
  s := 7

/-- The sharp equal-weight direction paired with the accepted YZ tail. -/
def fixedSharpDirection : FlagDegree := sharpAgreementDirection fixedSupport

/-- Unnormalized sharp-YZ regular-factor ledger. -/
def fixedSharpYZRegularNumerator : ℕ :=
  factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
    fixedProfile.rectangularSurfaceFlag

/-- Strict regular-factor count ceiling. -/
def fixedSharpYZRegularCeiling : ℕ :=
  fixedSharpYZRegularNumerator / fixedProfile.gap ^ 2 + 1

/-- Strict singular-factor count ceiling. -/
def fixedTightSingularCeiling : ℕ := fixedTightProfile.countCap + 1

/-- Strict fixed-cell ceiling after adding regular and singular branches. -/
def fixedCountCeiling : ℕ :=
  fixedSharpYZRegularCeiling + fixedTightSingularCeiling

theorem fixed_profile_values :
    fixedProfile.errors = 79476 ∧
      fixedProfile.gap = 51597 ∧
      fixedProfile.yCap = 37 ∧
      fixedProfile.degreeIncidence = 9705289897 ∧
      fixedProfile.unitIncidence = 131073 ∧
      fixedProfile.surfaceFlag = ⟨660, 30, 7⟩ ∧
      fixedProfile.agreementDirection = ⟨1320, 60, 13⟩ ∧
      fixedProfile.rectangularSurfaceFlag = ⟨690, 37, 7⟩ := by
  norm_num [fixedProfile, Profile.errors, Profile.gap, Profile.yCap,
    Profile.degreeIncidence, Profile.unitIncidence, Profile.surfaceFlag,
    Profile.derivativeFlag, Profile.agreementDirection,
    Profile.rectangularSurfaceFlag]
  rfl

theorem fixed_support_values :
    fixedSupport.agreementDirection = ⟨1320, 60, 13⟩ ∧
      fixedSharpDirection = ⟨1320, 59, 13⟩ := by
  norm_num [fixedSupport, fixedSharpDirection,
    ResidualSupportParameters.agreementDirection, sharpAgreementDirection]

theorem fixed_sharp_yz_regular_numerator_exact :
    fixedSharpYZRegularNumerator = 365777964798168936351261872 := by
  norm_num [fixedSharpYZRegularNumerator, fixedSharpDirection,
    factorRegularLedgerYZForDirection, factorPrimaryForDirection,
    factorZTailForDirection, factorYZTailForDirection, fixedProfile,
    fixedSupport, sharpAgreementDirection, Profile.rectangularSurfaceFlag,
    Profile.yCap, Profile.degreeIncidence, Profile.unitIncidence,
    Profile.errors, Profile.gap, flagMixed, unitZFlag, unitYZFlag]

theorem fixed_sharp_yz_regular_ceiling_exact :
    fixedSharpYZRegularCeiling = 137394274994425942 := by
  rw [fixedSharpYZRegularCeiling, fixed_sharp_yz_regular_numerator_exact]
  norm_num [fixedProfile, Profile.gap]

theorem fixed_tight_values :
    fixedTightProfile.kappa = 13 ∧
      fixedTightProfile.implicitYCap = 489 ∧
      fixedTightProfile.algebraicCap = 8970 ∧
      fixedTightProfile.agreement = ⟨128187439, 131071, 2351413741⟩ ∧
      fixedTightProfile.aggregateCost = ⟨8970, 8772660, 489⟩ ∧
      fixedTightProfile.coreNumerator = 452141460079491888 ∧
      fixedTightProfile.tightNumerator = 452149763161606488 ∧
      fixedTightProfile.countCap = 8763101791995 := by
  norm_num [fixedTightProfile, TightParameters.kappa,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.agreement, TightParameters.aggregateCost,
    TightParameters.coreNumerator, TightParameters.tightNumerator,
    TightParameters.countCap, TightParameters.errors, TightParameters.gap,
    dot]

theorem fixed_tight_singular_ceiling_exact :
    fixedTightSingularCeiling = 8763101791996 := by
  norm_num [fixedTightSingularCeiling, fixedTightProfile,
    TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap, dot]

theorem fixed_tight_singular_count_cap_exact :
    fixedTightProfile.countCap = 8763101791995 := fixed_tight_values.2.2.2.2.2.2.2

theorem fixed_count_ceiling_exact :
    fixedCountCeiling = 137403038096217938 := by
  rw [fixedCountCeiling, fixed_sharp_yz_regular_ceiling_exact,
    fixed_tight_singular_ceiling_exact]

/-! ## Active-YZ projection and characteristic gates -/

/-- Exact cumulative surface and sharp cut caps used by the active-YZ
terminal projection constructor. -/
theorem fixed_active_yz_caps :
    fixedProfile.rectangularSurfaceFlag.yz +
        fixedProfile.rectangularSurfaceFlag.all = 44 ∧
      fixedProfile.rectangularSurfaceFlag.all = 7 ∧
      fixedProfile.rectangularSurfaceFlag.zOnly +
          fixedProfile.rectangularSurfaceFlag.yz +
          fixedProfile.rectangularSurfaceFlag.all = 734 ∧
      1 + fixedProfile.w * (2 * fixedSupport.ys - 2) = 9437113 ∧
      (2 * fixedSupport.s - 1) * fixedProfile.w = 1703923 := by
  norm_num [fixedProfile, fixedSupport, Profile.rectangularSurfaceFlag,
    Profile.yCap]

/-- Every small-characteristic and retained mixed-Z inequality required by
the active-YZ projection family at the target caps. -/
theorem fixed_active_yz_characteristic_gates :
    fixedSupport.s < fixedSupport.ys ∧
      44 < prime ∧ 7 < prime ∧ 734 < prime ∧
      9437113 * 7 + 44 * 1703923 = 141032403 ∧
      9437113 * 7 + 44 * 1703923 < prime := by
  norm_num [fixedSupport, prime]

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

#print axioms fixed_sharp_yz_regular_ceiling_exact
#print axioms fixed_tight_singular_ceiling_exact
#print axioms fixed_degree_part_bound
#print axioms fixed_unit_part_bound

end ProximityPrize.SubmissionLower.ContactFixedMeetProfile6670Research
