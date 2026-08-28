import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6600AdaptiveResearch
import ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research

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
  intro Q hQ hbox selected seeds u0 u1 hdegree hnoPencil R g
  have hRdata := directFactor_data Q R.1 hQ weightedCap w seedTotalCap
    slopeCap hbox R.2
  have hRne : R.1 ≠ 0 := hRdata.1.ne_zero
  have hglobal := regularFlag_budgets Q hQ hbox
  have hRZ : (regularFlag Q R).zOnly ≤ 576 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.1
  have hRY : (regularFlag Q R).yz ≤ 33 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.1
  have hRS : (regularFlag Q R).all ≤ 6 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.2
  have hgZ : (geometricFlag IRSProfile.Field g).zOnly ≤
      (regularFlag Q R).zOnly := by
    simpa only [geometricFlag, regularFlag,
      show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide] using
      geometricFactor_degree_le IRSProfile.Field R.1 hRne g (2 : Fin 3)
  have hgY : (geometricFlag IRSProfile.Field g).yz ≤
      (regularFlag Q R).yz := by
    simpa only [geometricFlag, regularFlag,
      show Fin.succ (0 : Fin 3) = (1 : Fin 4) by decide] using
      geometricFactor_degree_le IRSProfile.Field R.1 hRne g (0 : Fin 3)
  have hgS : (geometricFlag IRSProfile.Field g).all ≤
      (regularFlag Q R).all := by
    simpa only [geometricFlag, regularFlag,
      show Fin.succ (1 : Fin 3) = (2 : Fin 4) by decide] using
      geometricFactor_degree_le IRSProfile.Field R.1 hRne g (1 : Fin 3)
  exact terminalAdaptiveProjectionFamilies_of_rectangular_caps
    (regularGeometricResidualStage Q hQ hbox selected seeds
      (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
      u0 u1 IRSProfile.domain.injective.injOn hdegree hnoPencil R g)
    (hgZ.trans hRZ) (hgY.trans hRY) (hgS.trans hRS)

/-- Fully closed score-66 lower-track claim. -/
theorem protocolClaim6600 : ProtocolClaim 6600 315111 1048576 :=
  ContactProtocol6600AdaptiveResearch.protocolClaim6600_of_terminal_projection_families
    frozenTerminalAdaptiveProjectionFamilies6600

end


end ProximityPrize.SubmissionLower.ContactProtocol6600Research

#print axioms ProximityPrize.SubmissionLower.ContactProtocol6600Research.frozenTerminalAdaptiveProjectionFamilies6600
#print axioms ProximityPrize.SubmissionLower.ContactProtocol6600Research.protocolClaim6600
