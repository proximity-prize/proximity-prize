import ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryProperProvider6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredCongruentTangent6750Research

namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredOrdinaryTangent6750Research

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactFirstTailCertificate6731Research ContactProperCutSeedCount
open ContactDelayedTailMultiplicityProvider6732Research
open ContactPrimeSeedIncidence ContactInterpolation
open ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch
open ContactAnchoredDelayedTailLocalDVR6750Research
open ContactAnchoredReducedActiveGeometry6750Research
open ContactAnchoredReducedWeightedResultants6750Research
open ContactAnchoredCongruentCuts6750Research
open ContactAnchoredCongruentTangent6750Research
open ContactAnchoredOrdinaryFixedCell6750Research
open ContactAnchoredOrdinaryProperProvider6750Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactAdaptiveProjectionCoordinateResearch
open ContactAdaptiveNestedProjectionActive6630Research
open ContactFlagAffineFamilyDegree6543Research
open ContactTwoTailParameters6750Research
open ContactRouterCellCosts6750Research
open ContactMovingAgreementCertificate6719Research
open ContactWeakSeparableSeparatorResearch
open ActualCurveCoordinateField CoordinateBoxZeroCount

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
local instance : CharP (GenericField K) prime := genericField_charP K prime

theorem reducedUnitFamily_one_le_yzCost
    {Gamma : Finset K} {flag : FlagDegree} {t y r : Nat}
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain prime
      errors flag w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime)
    (hmixed : (1 + (w + 1) * (2 * (cellB y r + cellS r + 3) - 2)) *
        flag.all + (flag.yz + flag.all) *
          ((2 * (cellS r + 2) - 2) * (w + 1)) < prime)
    (C : RegularComponent (GenericField K) S.G (reducedFirstCut S)
      (regularitySurface (polynomialEmbedding K) S.F)) :
    1 ≤ (reducedUnitFamily S hfirstProper hflagChar hmixed
      ).toPrimeFlagBudgetFamily.yzCost C := by
  let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
  let U := reducedUnitFamily S hfirstProper hflagChar hmixed
  change 1 ≤ coordinateDegree (GenericField K)
    (CoordinateField (GenericField K) C.1) (U.yzProjection C)
  apply one_le_coordinateDegree_of_transcendental_value
  have hproj : U.yzProjection C = coordinateOfGate
      (affineU (GenericField K) C.1 A.data.lam) (A.data.uGate C) := rfl
  rw [hproj, coordinateOfGate_value]
  exact A.data.uTranscendental C

theorem cellTangentProviderD6750 (D t y r : Nat)
    (hDshort : w + 1 ≤ D) (hDchar : D < prime) :
    CellTangentProviderD6750 D t y r := by
  constructor
  intro Gamma flag S hfirstProper hnodes hagreement hbox hflagChar hmixed C hall
  let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
  let U := reducedUnitFamily S hfirstProper hflagChar hmixed
  let hd := ordinary_sub_reducedFirstCut_dvd S
  have hyzPositive : 1 ≤ U.toPrimeFlagBudgetFamily.yzCost
      (regularComponentEquiv hd C) :=
    reducedUnitFamily_one_le_yzCost S hfirstProper hflagChar hmixed _
  exact tangent_component_card_le_of_congruentCut S C hfirstProper hd A.base U
    agreements D t r hnodes hagreement
    (by norm_num [w, agreements, n, errors]) (by norm_num [w])
    hDshort hDchar
    hbox hyzPositive hall

theorem cellTangentProvider6750 (t y r : Nat) :
    CellTangentProvider6750 t y r :=
  cellTangentProviderD6750 profileA.weightedCap t y r
    (by norm_num [w, profileA,
      ContactTwoTailParameters6750Research.Profile.weightedCap,
      agreements, n, errors])
    (by norm_num [prime, profileA,
      ContactTwoTailParameters6750Research.Profile.weightedCap,
      agreements, n, errors])

theorem properStageProvider6750
    (t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 71) (hr : r ≤ 16)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t) :
    ProperStageProvider6750 t y r :=
  properStageProvider6750_of_tangent t y r ht hy hr hr2 hry hyt
    (cellTangentProvider6750 t y r)

end
end ContactAnchoredOrdinaryTangent6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryTangent6750Research.reducedUnitFamily_one_le_yzCost
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryTangent6750Research.cellTangentProvider6750
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryTangent6750Research.properStageProvider6750
