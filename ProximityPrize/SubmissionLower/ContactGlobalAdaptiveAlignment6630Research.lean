import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFrozenAlignment6630Research
import ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6630Research

/-!
# Frozen score-66.30 alignment from terminal adaptive YZ families

This adapter specializes the complete geometric count to the benchmark field
and full evaluation domain. Its sole premise is the adaptive YZ projection
family at every terminal proper cut of every actual regular geometric factor.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalAdaptiveAlignment6630Research

open scoped Classical
open ProximityPrize.Benchmark
open ContactParameters6630Research
open ContactInterpolation ContactTranslation ContactPrimeSeedIncidence
open ContactGenericInitialPoint ContactOriginalRegularSeedCount
open ContactRegularFactorFlag6630Research ContactRegularSeeds6630Research
open ContactGlobalSelectedFamilies6630Research
open ContactRegularFactorResidualStage6630Research
open ContactTerminalAdaptiveProjection6630Research
open ContactAdaptiveProjectionFactorProvider6630Research
open ContactGlobalAdaptiveProjection6630Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 35000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : DecidableEq (GenericField IRSProfile.Field) := Classical.decEq _
local instance : CharP IRSProfile.Field prime :=
  ContactFrozenAlignment6630Research.challenge_field_characteristic6630
local instance : CharP (GenericField IRSProfile.Field) prime :=
  genericField_charP IRSProfile.Field prime

/-- Exact geometric premise left after freezing interpolation and alignment.
No counting or numerical assertion is exposed here. -/
def FrozenTerminalAdaptiveProjectionFamiliesYZ6630 : Prop :=
  ∀ (Q : MvPolynomial (Fin 4) IRSProfile.Field) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox IRSProfile.Field
      weightedCap w seedTotalCap slopeCap)
    (hsharp : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field weightedCap w seedTotalCap slopeCap)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (seeds : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hnoPencil : NoLargeSelectedPencil selected seeds w errors)
    (R : RegularIndex Q)
    (g : GeometricFactor IRSProfile.Field R.1),
    TerminalAdaptiveProjectionFamiliesYZ6630
      (regularGeometricResidualStage6630 Q hQ hbox hsharp selected seeds
        (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
        u0 u1 IRSProfile.domain.injective.injOn hdegree hnoPencil R g)

/-- Terminal adaptive YZ families imply the exact frozen global selected
count consumed by the alignment bridge. -/
theorem global_count_lt_alignment6630_of_terminal_projection_families
    (hprojection : FrozenTerminalAdaptiveProjectionFamiliesYZ6630) :
    ContactFrozenAlignment6630Research.GlobalCountLtAlignment6630 := by
  intro Q hQ hbox hsharp selected seeds u0 u1 hdegree hsolution hagreement hnoPencil
  apply global_count_lt_alignment_of_adaptive_projection_families
    Q hQ hbox hsharp selected seeds
      (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by norm_num [IRSProfile.Index, n])
      hdegree hsolution hagreement hnoPencil
  intro R g
  exact hprojection Q hQ hbox hsharp selected seeds u0 u1 hdegree hnoPencil R g

end

end ProximityPrize.SubmissionLower.ContactGlobalAdaptiveAlignment6630Research
