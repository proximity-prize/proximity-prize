import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFrozenAlignment6600Research
import ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6600Research

/-!
# Frozen score-66 alignment from terminal adaptive projection families

This adapter specializes the end-to-end geometric count to the benchmark
field and its full evaluation domain.  Its sole remaining premise is the
construction of an adaptive unit projection family at every terminal proper
cut of every actual regular geometric factor.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalAdaptiveAlignment6600Research

open scoped Classical
open ProximityPrize.Benchmark
open ContactParameters6600Research
open ContactInterpolation ContactTranslation ContactPrimeSeedIncidence
open ContactGenericInitialPoint ContactOriginalRegularSeedCount
open ContactGlobalSelectedFamilies6600Research
open ContactRegularFactorResidualStage6600Research
open ContactAdaptiveProjectionFactorProvider6600Research
open ContactGlobalAdaptiveProjection6600Research

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

/-- The exact geometric premise left after freezing the interpolation and
alignment frontend.  No counting or numerical assertion is exposed here. -/
def FrozenTerminalAdaptiveProjectionFamilies6600 : Prop :=
  ∀ (Q : MvPolynomial (Fin 4) IRSProfile.Field) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox IRSProfile.Field
      weightedCap w seedTotalCap slopeCap)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (seeds : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hnoPencil : NoLargeSelectedPencil selected seeds w errors)
    (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
    (g : GeometricFactor IRSProfile.Field R.1),
    TerminalAdaptiveProjectionFamilies
      (regularGeometricResidualStage Q hQ hbox selected seeds
        (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
        u0 u1 IRSProfile.domain.injective.injOn hdegree hnoPencil R g)

/-- Terminal adaptive projection families imply the exact frozen global
selected-family count consumed by the stock alignment bridge. -/
theorem global_count_lt_alignment6600_of_terminal_projection_families
    (hprojection : FrozenTerminalAdaptiveProjectionFamilies6600) :
    ContactFrozenAlignment6600Research.GlobalCountLtAlignment6600 := by
  intro Q hQ hbox selected seeds u0 u1 hdegree hsolution hagreement hnoPencil
  apply global_count_lt_alignment_of_adaptive_projection_families
    Q hQ hbox selected seeds
      (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by norm_num [IRSProfile.Index, n])
      hdegree hsolution hagreement hnoPencil
  intro R g
  exact hprojection Q hQ hbox selected seeds u0 u1 hdegree hnoPencil R g

end

end ProximityPrize.SubmissionLower.ContactGlobalAdaptiveAlignment6600Research

#print axioms ProximityPrize.SubmissionLower.ContactGlobalAdaptiveAlignment6600Research.global_count_lt_alignment6600_of_terminal_projection_families
