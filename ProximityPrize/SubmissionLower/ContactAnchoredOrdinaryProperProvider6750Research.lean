import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryFixedCell6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredReducedDelayedTailAssembly6750Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredOrdinaryProperProvider6750Research

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactFirstTailCertificate6731Research ContactProperCutSeedCount
open ContactPrimeSeedIncidence ContactInterpolation
open ContactFlagBezout6543Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactResidualSupportParametersResearch
open ContactMovingAgreementCertificate6719Research
open ContactAnchoredDelayedTailLocalDVR6750Research
open ContactAnchoredDelayedTailProviderAdapter6750Research
open ContactAnchoredReducedWeightedResultants6750Research
open ContactAnchoredReducedDelayedTailAssembly6750Research
open ContactAnchoredOrdinaryFixedCell6750Research
open ContactRouterCellCosts6750Research
open ContactTwoTailParameters6750Research
open ContactAnchoredReducedActiveGeometry6750Research
open ContactAnchoredCongruentCuts6750Research
open ContactTangentCoefficientProvider6732Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactAdaptiveProjectionCoordinateResearch
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

 


structure CellTangentProviderD6750 (D t y r : Nat) : Prop where
  bound : ∀ {Gamma : Finset K} {flag : FlagDegree}
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain prime
      errors flag w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hnodes : S.nodes.card = agreements + errors)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflagChar : flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime)
    (hmixed : (1 + (w + 1) * (2 * (cellB y r + cellS r + 3) - 2)) *
        flag.all + (flag.yz + flag.all) *
          ((2 * (cellS r + 2) - 2) * (w + 1)) < prime),
    ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (errors + 1) *
            (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C

abbrev CellTangentProvider6750 :=
  CellTangentProviderD6750 profileA.weightedCap

 
theorem properStageProviderD6750_of_tangent
    (D t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (tangent : CellTangentProviderD6750 D t y r) :
    ProperStageProviderD6750 D t y r := by
  intro Gamma flag S hfirstProper hnodes hagreement hbox hflag
  have hsCell : (cellSupport t y r).s = r := by
    simp only [cellSupport, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  have hysCell : (cellSupport t y r).ys = y := by
    simp only [cellSupport, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  have htotalCell : (cellSupport t y r).total = t := by
    simp only [cellSupport, cellA, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  have hs : (cellSupport t y r).s ≤ anchoredFixedSupport.s := by
    rw [hsCell]
    exact hr
  have hys : (cellSupport t y r).ys ≤ anchoredFixedSupport.ys := by
    rw [hysCell]
    exact hy
  have htotal : (cellSupport t y r).total ≤ anchoredFixedSupport.total := by
    rw [htotalCell]
    exact ht
  have hflagChar : flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime := by
    norm_num [prime]
    omega
  have hmixed :
      (1 + (w + 1) * (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
        (flag.yz + flag.all) *
          ((2 * (cellS r + 2) - 2) * (w + 1)) < prime := by
    have hb : cellB y r + cellS r + 3 = y := by
      simp only [cellB, cellS]
      omega
    have hs' : cellS r + 2 = r := by
      simp only [cellS]
      omega
    rw [hb, hs']
    have hy' : 2 * y - 2 ≤ 128 := by omega
    have hr' : 2 * r - 2 ≤ 26 := by omega
    have h1 : (1 + (w + 1) * (2 * y - 2)) * flag.all ≤
        (1 + (w + 1) * 128) * 14 :=
      Nat.mul_le_mul
        (Nat.add_le_add_left (Nat.mul_le_mul_left (w + 1) hy') 1)
        (hflag.1.trans hr)
    have h2 : (flag.yz + flag.all) * ((2 * r - 2) * (w + 1)) ≤
        65 * (26 * (w + 1)) :=
      Nat.mul_le_mul (hflag.2.1.trans hy)
        (Nat.mul_le_mul_right (w + 1) hr')
    exact (Nat.add_le_add h1 h2).trans_lt (by norm_num [w, prime])
  have htangentGate : anchoredErrors + 1 ≤
      (reducedResidualAgreementFlag6750 (cellSupport t y r)
        (anchoredW + 2)).yz := by
    have hyr : 1 ≤ y - r := by omega
    have hdir : 2 ≤ 2 * (y - r) := Nat.mul_le_mul_left 2 hyr
    have hmul := Nat.mul_le_mul_right (anchoredW + 2) hdir
    simp only [reducedResidualAgreementFlag6750,
      reducedAgreementDirection6750, hysCell, hsCell]
    norm_num [anchoredErrors, anchoredW] at hmul ⊢
    omega
  apply exists_delayedTailMultiplicityProvider_of_reducedWeightedResultants
    S hs hys htotal hfirstProper hflagChar hmixed htangentGate
  exact tangent.bound S hfirstProper hnodes hagreement hbox hflagChar hmixed

 
theorem properStageProvider6750_of_tangent
    (t y r : Nat) (ht : t ≤ 2530) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (tangent : CellTangentProvider6750 t y r) :
    ProperStageProvider6750 t y r :=
  properStageProviderD6750_of_tangent profileA.weightedCap t y r ht hy hr
    hr2 hry hyt tangent

end

end ContactAnchoredOrdinaryProperProvider6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryProperProvider6750Research.properStageProvider6750_of_tangent
