import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSeedlessProtocolResearch
import ProximityPrize.SubmissionLower.ContactGlobalAdaptiveAlignment6630Research
import ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6630Research
import ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6641Research

/-!
# Unconditional score-66.30 protocol endpoint

The terminal constructor is closed for every actual regular geometric factor
using nested cumulative support bounds.  This is essential: factorization
preserves the sums of `R`, `Y+R`, and `Y+R+Z` support functionals, whereas the
three flag increments need not be bounded separately factor by factor.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6630Research

set_option autoImplicit false

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactParameters6630Research
open ContactGenericInitialPoint ContactOriginalRegularSeedCount
open ContactOriginalRegularResidualStage6630Research
open ContactRegularFactorFlag6630Research
open ContactRegularFactorResidualStage6630Research
open ContactRegularSeeds6630Research
open ContactSelectedSeedDecomposition
open ContactGlobalAdaptiveAlignment6630Research
open ContactTerminalAdaptiveProjection6630Research
open ContactFlagRegularFactorCaps6641Research

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

local instance : DecidableEq (GenericField IRSProfile.Field) := Classical.decEq _
local instance : CharP IRSProfile.Field prime :=
  ContactFrozenAlignment6630Research.challenge_field_characteristic6630
local instance : CharP (GenericField IRSProfile.Field) prime :=
  genericField_charP IRSProfile.Field prime

/-- The terminal projection-family premise, closed for every actual regular
geometric factor by the exact cumulative score-66.30 Newton caps. -/
theorem frozenTerminalAdaptiveProjectionFamiliesYZ6630 :
    FrozenTerminalAdaptiveProjectionFamiliesYZ6630 := by
  intro Q hQ hbox hsharp selected seeds u0 u1 hdegree hnoPencil R g
  have hRdata := directFactor_data Q R.1 hQ weightedCap w seedTotalCap
    slopeCap hbox R.2
  have hRne : R.1 ≠ 0 := hRdata.1.ne_zero
  have hregular := regularFlag6630_budgets_of_flagBox6641 Q hQ hsharp
  have hRAll : (regularFlag6630 Q R).all ≤ 10 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hregular.1
  have hRYS : (regularFlag6630 Q R).yz + (regularFlag6630 Q R).all ≤ 48 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hregular.2.1
  have hRTotal : (regularFlag6630 Q R).zOnly +
      (regularFlag6630 Q R).yz + (regularFlag6630 Q R).all ≤ 825 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hregular.2.2
  have hgeometric := geometricFlag6630_budgets IRSProfile.Field R.1 hRne
  rw [originalFlag6630_eq_regularFlag IRSProfile.Field R] at hgeometric
  have hgAll : (geometricFlag6630 IRSProfile.Field g).all ≤
      (regularFlag6630 Q R).all :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans hgeometric.1
  have hgYS : (geometricFlag6630 IRSProfile.Field g).yz +
      (geometricFlag6630 IRSProfile.Field g).all ≤
      (regularFlag6630 Q R).yz + (regularFlag6630 Q R).all :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans hgeometric.2.1
  have hgTotal : (geometricFlag6630 IRSProfile.Field g).zOnly +
      (geometricFlag6630 IRSProfile.Field g).yz +
      (geometricFlag6630 IRSProfile.Field g).all ≤
      (regularFlag6630 Q R).zOnly + (regularFlag6630 Q R).yz +
        (regularFlag6630 Q R).all :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans hgeometric.2.2
  exact terminalAdaptiveProjectionFamiliesYZ6630_of_cumulative_caps
    (regularGeometricResidualStage6630 Q hQ hbox hsharp selected seeds
      (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
      u0 u1 IRSProfile.domain.injective.injOn hdegree hnoPencil R g)
    (hgAll.trans hRAll) (hgYS.trans hRYS) (hgTotal.trans hRTotal)

/-- Fully closed score-66.75 lower-track claim. -/
theorem protocolClaim6630 : ProtocolClaim 6675 318083 1048576 := by
  have hcount : ContactFrozenAlignment6630Research.GlobalCountLtAlignment6630 :=
    global_count_lt_alignment6630_of_terminal_projection_families
      frozenTerminalAdaptiveProjectionFamiliesYZ6630
  have halign : AffineLineAlignmentBound IRSProfile.baseCode errors alignmentBudget :=
    ContactFrozenAlignment6630Research.alignment_of_global_count_lt_alignment6630
      hcount
  apply ContactSeedlessProtocolResearch.protocolClaim6675_of_alignment
  simpa [ContactSeedlessProtocolResearch.errors,
    ContactSeedlessProtocolResearch.mcaBudget, errors, alignmentBudget,
    ContactScore6630Research.errors6630] using halign

end


end ProximityPrize.SubmissionLower.ContactProtocol6630Research
