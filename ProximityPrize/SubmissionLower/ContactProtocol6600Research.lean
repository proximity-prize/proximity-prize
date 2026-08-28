import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6600AdaptiveResearch
import ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research
import ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research

/-!
# Unconditional score-66 protocol endpoint

The terminal constructor applies to each actual geometric factor because its
coordinate degrees are bounded by the containing regular factor, while every
regular factor is pointwise bounded by the global rectangular flag sums.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6600Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactParameters6600Research
open ContactGenericInitialPoint ContactOriginalRegularSeedCount
open ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorFlag6600Research
open ContactRegularFactorResidualStage6600Research
open ContactGlobalSelectedFamilies6600Research
open ContactSelectedSeedDecomposition
open ContactGlobalAdaptiveAlignment6600Research
open ContactTerminalAdaptiveProjection6600Research
open ContactSharpFactorAggregationPost6600Research

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 35000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : DecidableEq (GenericField IRSProfile.Field) := Classical.decEq _
local instance : CharP IRSProfile.Field prime :=
  ContactFrozenAlignment6600Research.challenge_field_characteristic6600
local instance : CharP (GenericField IRSProfile.Field) prime :=
  genericField_charP IRSProfile.Field prime

/-- The terminal projection-family premise, closed for every actual regular
geometric factor by the rectangular score-66 flag caps. -/
theorem frozenTerminalAdaptiveProjectionFamilies6600 :
    FrozenTerminalAdaptiveProjectionFamilies6600 := by
  intro Q hQ hbox htriangle selected seeds u0 u1 hdegree hnoPencil R g
  have hRdata := directFactor_data Q R.1 hQ weightedCap w seedTotalCap
    slopeCap hbox R.2
  have hRne : R.1 ≠ 0 := hRdata.1.ne_zero
  have hglobal := positiveRFactor_raw_budgets Q hQ hbox htriangle
  have hRrawR : factorRawR Q R ≤ 9 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.1
  have hRrawYR : factorRawYR Q R ≤ 44 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.1
  have hRrawTotal : factorRawTotal Q R ≤ 469 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.2
  have hgeom := geometricFactor_raw_budgets R.1 hRne
  have hgRawR : geometricRawR IRSProfile.Field g ≤ 9 :=
    ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans hgeom.1).trans hRrawR
  have hgRawYR : geometricRawYR IRSProfile.Field g ≤ 44 :=
    ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans hgeom.2.1).trans hRrawYR
  have hgRawTotal : geometricRawTotal IRSProfile.Field g ≤ 469 :=
    ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans hgeom.2.2).trans hRrawTotal
  have hgZ : (sharpGeometricFlag IRSProfile.Field g).zOnly ≤ 469 := by
    exact (Nat.sub_le _ _).trans hgRawTotal
  have hgY : (sharpGeometricFlag IRSProfile.Field g).yz ≤ 44 := by
    exact (Nat.sub_le _ _).trans hgRawYR
  have hgS : (sharpGeometricFlag IRSProfile.Field g).all ≤ 9 := hgRawR
  exact terminalAdaptiveProjectionFamilies_of_rectangular_caps
    (regularGeometricResidualStage Q hQ hbox htriangle selected seeds
      (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
      u0 u1 IRSProfile.domain.injective.injOn hdegree hnoPencil R g)
    hgZ hgY hgS

/-- Fully closed score-66 lower-track claim. -/
theorem protocolClaim6600 : ProtocolClaim 6636 316543 1048576 :=
  ContactProtocol6600AdaptiveResearch.protocolClaim6600_of_terminal_projection_families
    frozenTerminalAdaptiveProjectionFamilies6600

end


end ProximityPrize.SubmissionLower.ContactProtocol6600Research

#print axioms ProximityPrize.SubmissionLower.ContactProtocol6600Research.frozenTerminalAdaptiveProjectionFamilies6600
#print axioms ProximityPrize.SubmissionLower.ContactProtocol6600Research.protocolClaim6600
